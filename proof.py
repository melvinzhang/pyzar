"""Hybrid Isar declarative proof DSL.

Each ``have`` produces one kernel theorem; the ``Proof`` object tracks named
facts and discharges blocks via the existing primitives (``INDUCT_PROVE``,
``DISJ_CASES``, ``DISCH`` / ``GEN``, ``REWRITE_PROVE``, ``MP_LIST``).

Usage:

    from proof import proof
    from nat import ADD_1, ADD_SUC

    @proof
    def SATZ_5(p):
        p.goal("!x y z. (x + y) + z = x + (y + z)")
        p.fix("x y z")
        with p.induction("z"):
            with p.base():
                p.thus("(x + y) + 1 = x + (y + 1)")\
                    .by_rewrite([ADD_1, ADD_SUC])
            with p.step("IH"):
                p.thus("(x + y) + SUC z = x + (y + SUC z)")\
                    .by_rewrite([ADD_SUC, "IH"])

The decorator runs the script and returns the resulting kernel theorem.
"""

import re

from fusion import (
    Var, Const, Comb, Abs, thm,
    aconv, concl, HolError, ASSUME, EQ_MP, BETA, INST, mk_abs, mk_comb,
    rand, type_of, TRANS, mk_eq, mk_fun_ty, MK_COMB, ABS, REFL,
)
from axioms import T, F, mk_select, mk_forall
from tactics import (
    SPEC, GEN, DISCH, MP, MP_LIST, DISJ_CASES, BETA_CONV, BETA_NORM, SYM,
    AP_THM, PROVE_HYP, ELIM_EX, _subst_term,
    NOT_INTRO, NOT_ELIM, CONTR, REWRITE_NE, EXISTS, DISJ1, DISJ2,
    CONJUNCT1, CONJUNCT2,
    REWRITE_PROVE, REWRITE_RULE, REWRITE_CONV, BETA_RULE,
    AC_PROVE, REWRITE_AC_PROVE,
)
from parser import parse, pp, ParseError, DEFAULT_SIG


# ---------------------------------------------------------------------------
# Unfolder registry: each entry maps a relation symbol (e.g. ">", "<") to
# a function ``unfold(a, b) -> |- (op a b) = (?v. body)``. Modules that
# introduce a relation can register here so ``p.choose(...)`` can be invoked
# directly on facts of that relation.
# ---------------------------------------------------------------------------

_UNFOLDERS = {}

def register_unfolder(op_name, unfold_fn):
    _UNFOLDERS[op_name] = unfold_fn


# Parallel registry for disjunction-shaped unfolders (e.g. ``>=``, ``<=``):
# each entry maps a relation symbol to a function ``unfold(a, b) -> |- (op a
# b) = (left \/ right)``. ``cases_on`` consults this so it can take a fact of
# the form ``a R b`` directly and case-split on the unfolded disjunction.

_DISJ_UNFOLDERS = {}

def register_disj_unfolder(op_name, unfold_fn):
    _DISJ_UNFOLDERS[op_name] = unfold_fn


# Contradiction-finder registry: each entry maps an unordered pair of
# relation-symbol names ``(rel_a, rel_b)`` to a finder
# ``finder(th_a, th_b) -> |- F`` whose inputs are facts of shape ``rel_a a b``
# and ``rel_b a b`` respectively. ``p.absurd().auto(...)`` consults this so
# call sites no longer need to name a specific contradiction lemma.

_CONTRA_FINDERS = {}

def register_contra_finder(rel_a, rel_b, finder):
    _CONTRA_FINDERS[(rel_a, rel_b)] = finder


# ---------------------------------------------------------------------------
# Frame: a single open scope (root, induction body, base/step, case).
# ---------------------------------------------------------------------------

class LazyLetDef:
    """Local-equation form of a let (Isabelle-style ``define``).

    The let abbreviation stays folded throughout the proof: a fresh kernel
    ``Var`` of the right function type is the carrier, and a local
    equation theorem
    ``[!args. R args = body] |- !args. R args = body`` is available for
    downstream tactics to rewrite through. The hypothesis is discharged
    on frame close (see ``_discharge_lazy_lets``): the carrier is
    INST'd to ``\\args. body`` and the now-trivial substituted equation
    is PROVE_HYP'd, leaving a theorem with no lazy-let baggage.
    """
    __slots__ = ("name", "bvars", "body", "carrier", "eq_th")

    def __init__(self, name, bvars, body, carrier, eq_th):
        self.name = name
        self.bvars = list(bvars)
        self.body = body
        self.carrier = carrier   # fresh Var of fun-type t1->...->tn->bty
        self.eq_th = eq_th       # [eq_term] |- !b1...bn. R b1..bn = body


class _Frame:
    __slots__ = ("goal", "kind", "vars_added", "hyps_added",
                 "facts_added", "choose_env", "type_env",
                 "lazy_lets", "pending_choose", "data", "result")

    def __init__(self, goal=None, kind="root"):
        self.goal = goal
        self.kind = kind
        self.vars_added = []      # for fix(): GEN at close
        self.hyps_added = []      # for assume(): list of (label, term); DISCH at close
        self.facts_added = []     # labels added at this frame; popped on exit
        self.choose_env = {}      # name -> witness term (parser env entries)
        self.type_env = {}        # name -> hol_type for higher-order params
        self.lazy_lets = {}       # name -> LazyLetDef (Isabelle-style local equation)
        self.pending_choose = []  # list of (ex_th, pred, hyp_ex) to discharge on close
        self.data = {}            # block-specific scratch
        self.result = None        # the theorem proving `goal`


# ---------------------------------------------------------------------------
# Proof object: stack of frames + name->thm registry.
# ---------------------------------------------------------------------------

class Proof:
    def __init__(self):
        self._frames = [_Frame(kind="root")]
        self._facts = {}          # label -> thm
        self._fact_order = []     # insertion order for negative-index lookup
        self._anon = 0

    @property
    def _cur(self):
        return self._frames[-1]

    # ---- env / parsing ---------------------------------------------------

    def _scope_env(self):
        env = {"F": F, "T": T}
        for fr in self._frames:
            for name, ty in fr.type_env.items():
                env[name] = ty
            for v in fr.vars_added:
                env[v.name] = v
            for name, term in fr.choose_env.items():
                env[name] = term
            for name, lz in fr.lazy_lets.items():
                env[name] = lz.carrier
        return env

    def _set_frame_result(self, frame, th):
        """Assign `frame.result = th`, after discharging any pending choose-blocks
        on the frame (in LIFO order). The discharge replays CHOOSE_GT-style
        ELIM_EX + PROVE_HYP plumbing."""
        for ex_th, pred, hyp_ex in reversed(frame.pending_choose):
            th = PROVE_HYP(ex_th, ELIM_EX(pred, hyp_ex, lambda _: th))
        frame.pending_choose.clear()
        frame.result = th

    def _lazy_let_carriers(self):
        """Map every in-scope lazy-let carrier ``Var`` to its ``LazyLetDef``."""
        out = {}
        for fr in self._frames:
            for lz in fr.lazy_lets.values():
                out[lz.carrier] = lz
        return out

    def _unfold_lazy_lets_in_term(self, tm, carriers=None):
        """Bottom-up unfold of every lazy-let application in ``tm``, returning
        ``|- tm = tm_unfolded``.

        Bypasses ``REWRITE_CONV``'s blanket "no hyp-bearing rules under
        binders" rule. The relaxation is sound here because lazy-let
        equation hyps are exactly ``!args. carrier args = body`` and
        ``ABS`` succeeds under binders (the bvar is not free in the hyp).

        Self-reference is bounded: each carrier may fire at most once on
        any descent path. A self-referential body (carrier appearing in
        its own RHS) therefore unfolds once and stops, rather than
        looping.
        """
        if carriers is None:
            carriers = self._lazy_let_carriers()
        if not carriers:
            return REFL(tm)
        return self._unfold_walk(tm, carriers, frozenset())

    def _unfold_walk(self, tm, carriers, blocked):
        if isinstance(tm, Abs):
            body_eq = self._unfold_walk(tm.body, carriers, blocked)
            if aconv(rand(body_eq._concl), tm.body):
                return REFL(tm)
            return ABS(tm.bvar, body_eq)
        if isinstance(tm, Comb):
            # Walk the spine; if the head is a lazy-let carrier and we have
            # enough args, fire the rule at the spine root then recurse on
            # the surplus arguments and child positions.
            spine = []
            head = tm
            while isinstance(head, Comb):
                spine.append(head.arg)
                head = head.fun
            spine.reverse()
            if (isinstance(head, Var) and head in carriers
                    and head not in blocked):
                lz = carriers[head]
                n = len(lz.bvars)
                if len(spine) >= n:
                    arg_eqs = [self._unfold_walk(a, carriers, blocked)
                               for a in spine]
                    eq = lz.eq_th
                    for i in range(n):
                        eq = SPEC(rand(arg_eqs[i]._concl), eq)
                    # In the unfolded body, the same carrier should not fire
                    # again on this descent (else self-referential lets loop).
                    rhs_unfolded = self._unfold_walk(
                        rand(eq._concl), carriers, blocked | {head})
                    eq = TRANS(eq, rhs_unfolded)
                    head_chain = REFL(head)
                    for i in range(n):
                        head_chain = MK_COMB(head_chain, arg_eqs[i])
                    head_eq = TRANS(head_chain, eq)
                    cur = head_eq
                    for i in range(n, len(spine)):
                        cur = MK_COMB(cur, arg_eqs[i])
                    return cur
            # No rule fires at the head; recurse into fun and arg.
            f_eq = self._unfold_walk(tm.fun, carriers, blocked)
            a_eq = self._unfold_walk(tm.arg, carriers, blocked)
            if (aconv(rand(f_eq._concl), tm.fun)
                    and aconv(rand(a_eq._concl), tm.arg)):
                return REFL(tm)
            return MK_COMB(f_eq, a_eq)
        return REFL(tm)

    def _unfold_fact(self, th):
        """Unfold every lazy-let application in ``th``'s conclusion,
        returning a theorem whose conclusion is the unfolded body. Used
        by ``by`` / ``by_select`` to auto-lift folded facts into their
        HO shape before SPEC/MP chains.
        """
        eq = self._unfold_lazy_lets_in_term(th._concl)
        if aconv(rand(eq._concl), th._concl):
            return th
        return EQ_MP(eq, th)

    def materialize_let(self, th, name):
        """Substitute the named lazy-let carrier with its ``\\args. body``
        abstraction in ``th`` and BETA-normalize the result, returning a
        new theorem whose conclusion no longer mentions the carrier.

        Use this when downstream code needs the original lambda shape
        (e.g. SELECT_AX-derived facts in EXCLUDED_MIDDLE that the rest of
        the proof navigates as ``@x. body``) rather than the folded
        carrier form. The local-equation hypothesis is discharged
        immediately, so the returned theorem has no lazy-let baggage.
        """
        lz = self._lookup_lazy_let(name)
        if lz is None:
            raise HolError(f"materialize_let: no lazy let named {name!r}")
        abs_body = lz.body
        for bv in reversed(lz.bvars):
            abs_body = mk_abs(bv, abs_body)
        th_inst = INST([(abs_body, lz.carrier)], th)
        # Discharge the (now-trivially-true) substituted equation hypothesis.
        applied = abs_body
        for bv in lz.bvars:
            applied = mk_comb(applied, bv)
        eq_th = BETA_NORM(applied)
        for bv in reversed(lz.bvars):
            eq_th = GEN(bv, eq_th)
        th_inst = PROVE_HYP(eq_th, th_inst)
        nf_eq = BETA_NORM(th_inst._concl)
        if not aconv(rand(nf_eq._concl), th_inst._concl):
            th_inst = EQ_MP(nf_eq, th_inst)
        return th_inst

    def _mp_modulo_lazy_lets(self, th_imp, th_arg):
        """``MP(th_imp, th_arg)`` with conversion-on-match fallback.

        If the antecedent shape and ``th_arg``'s conclusion don't ``aconv``
        directly, try to align them by unfolding lazy lets in either
        direction. Used by ``by`` and ``by_select``'s MP steps so the user
        can mix folded/unfolded facts in the same MP chain.
        """
        try:
            return MP(th_imp, th_arg)
        except HolError:
            pass
        # th_imp must be of shape a ==> b. Pull out a.
        c = th_imp._concl
        if not (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const) and c.fun.fun.name == "==>"):
            raise HolError(
                "MP: antecedent not a ==> shape\n"
                f"  th_imp: {pp(c)}\n"
                f"  th_arg: {pp(th_arg._concl)}")
        ant = c.fun.arg
        lifted = self._match_modulo_lazy_lets(ant, th_arg)
        if lifted is None:
            raise HolError(
                "MP: antecedent shape does not match argument\n"
                f"  expected: {pp(ant)}\n"
                f"  got:      {pp(th_arg._concl)}")
        return MP(th_imp, lifted)

    def _match_modulo_lazy_lets(self, target, th):
        """If ``aconv(target, th._concl)`` fails, try to align them by
        unfolding every lazy-let application in both terms.

        Uses the under-binder-tolerant ``_unfold_lazy_lets_in_term`` rather
        than the engine's ``REWRITE_CONV``, which would refuse to descend
        under binders for hyp-bearing rules.

        Returns ``th'`` with ``aconv(concl(th'), target)`` on success,
        else ``None``.
        """
        carriers = self._lazy_let_carriers()
        if not carriers:
            return None
        try:
            target_eq = self._unfold_lazy_lets_in_term(target, carriers)
            th_eq = self._unfold_lazy_lets_in_term(th._concl, carriers)
        except HolError:
            return None
        if not aconv(rand(target_eq._concl), rand(th_eq._concl)):
            return None
        th_at_nf = EQ_MP(th_eq, th)
        return EQ_MP(SYM(target_eq), th_at_nf)

    def _discharge_lazy_lets(self, frame, th):
        """Discharge each lazy-let hypothesis on ``th`` from ``frame``.

        For every lazy let ``R(b1...bn) := body`` registered on ``frame``,
        substitute ``R := \\b1...bn. body`` in ``th`` and ``PROVE_HYP`` the
        resulting (now trivially provable) equation hypothesis. The
        conclusion is BETA-normalized to clean up redexes left behind by
        the substitution.

        Lazy lets registered on parent frames are *not* discharged here —
        they go out with the corresponding parent frame.
        """
        if not frame.lazy_lets:
            return th
        # Process lets in reverse registration order: a later let's body
        # may reference an earlier carrier, so discharging the earlier
        # one first would mutate the later let's hyp into a shape that no
        # longer matches the eq_th we synthesize from ``lz.body``.
        for lz in reversed(list(frame.lazy_lets.values())):
            abs_body = lz.body
            for bv in reversed(lz.bvars):
                abs_body = mk_abs(bv, abs_body)
            # Substitute carrier := abs_body in th. Beta-redexes appear at
            # every former carrier-application site, plus inside the local
            # equation hypothesis (now ``!b1..bn. (\b1..bn. body) b1..bn = body``).
            th = INST([(abs_body, lz.carrier)], th)
            # Build the hypothesis-proof: |- !b1..bn. (\b1..bn. body) b1..bn = body
            # via BETA_NORM on the LHS chain, then GEN over each bvar.
            applied = abs_body
            for bv in lz.bvars:
                applied = mk_comb(applied, bv)
            eq_th = BETA_NORM(applied)            # |- (abs_body) b1..bn = body
            for bv in reversed(lz.bvars):
                eq_th = GEN(bv, eq_th)
            th = PROVE_HYP(eq_th, th)
        # Clean up residual redexes in the conclusion left by INST.
        nf_eq = BETA_NORM(th._concl)              # |- concl = beta-normal-concl
        if not aconv(rand(nf_eq._concl), th._concl):
            th = EQ_MP(nf_eq, th)
        return th

    def _parse(self, s):
        return parse(s, _env_bindings=self._scope_env())

    def _lookup_lazy_let(self, name):
        """Find a `LazyLetDef` by name in scope (inner frames shadow outer)."""
        for fr in reversed(self._frames):
            ld = fr.lazy_lets.get(name)
            if ld is not None:
                return ld
        return None

    def _register_lazy_let(self, name, bvars, body):
        """Register a lazy-let binding on the current frame.

        Builds a fresh carrier ``Var name : t1 -> ... -> tn -> body_ty`` and
        the local equation theorem
        ``[!b1...bn. name b1..bn = body] |- !b1...bn. name b1..bn = body``.
        Stores both in a ``LazyLetDef`` keyed under ``name`` in the current
        frame's ``lazy_lets`` map.

        Re-registering the same name on the same frame raises.
        """
        if name in self._cur.lazy_lets:
            raise HolError(
                f"_register_lazy_let: {name!r} already registered on frame")
        ty = type_of(body)
        for bv in reversed(bvars):
            ty = mk_fun_ty(bv.ty, ty)
        carrier = Var(name, ty)
        applied = carrier
        for bv in bvars:
            applied = mk_comb(applied, bv)
        eq_term = mk_eq(applied, body)
        for bv in reversed(bvars):
            eq_term = mk_forall(bv, eq_term)
        eq_th = ASSUME(eq_term)
        self._cur.lazy_lets[name] = LazyLetDef(name, bvars, body, carrier, eq_th)
        return self._cur.lazy_lets[name]

    def unfold(self, def_th, *args):
        """Apply a definition equation to argument terms.

        Thin wrapper over ``tactics.UNFOLD`` that resolves each string arg
        in the current scope before delegating; kernel-term args pass
        through.  See ``tactics.UNFOLD`` for the underlying behavior."""
        from tactics import UNFOLD
        resolved = [self._parse(a) if isinstance(a, str) else a for a in args]
        return UNFOLD(def_th, *resolved)

    def unfold_let(self, name, *args):
        """Produce the local equation for a lazy let, specialized at args.

        Returns ``|- name a1...an = body[bvars := ai]`` (with the local-
        equation hypothesis still attached; discharged on frame close).
        Mirrors ``p.unfold`` for global definitions: the result is an
        equation that downstream code threads through ``EQ_MP`` /
        ``TRANS`` / ``by_eq_mp`` / ``REWRITE_RULE``.

        Each ``arg`` may be a kernel term or a string parsed in the
        current scope.
        """
        lz = self._lookup_lazy_let(name)
        if lz is None:
            raise HolError(f"unfold_let: no lazy let named {name!r} in scope")
        if len(args) != len(lz.bvars):
            raise HolError(
                f"unfold_let: {name!r} expects {len(lz.bvars)} args, "
                f"got {len(args)}")
        th = lz.eq_th
        for a in args:
            a_t = self._parse(a) if isinstance(a, str) else a
            th = SPEC(a_t, th)
        return th

    def fold_let(self, name, *args):
        """Inverse of ``unfold_let``: returns ``|- body = name a1...an``."""
        return SYM(self.unfold_let(name, *args))

    _LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z_0-9]*)\s*:\s*(.+)$", re.DOTALL)

    _LET_SPEC_RE = re.compile(
        r"^\s*([A-Za-z_]\w*)\s*"
        r"\(\s*(.+?)\s*\)\s*"
        r":=\s*(.+)$",
        re.DOTALL)
    _LET_ARG_RE = re.compile(
        r"^\s*([A-Za-z_]\w*)\s*(?::\s*([A-Za-z_]\w*)\s*)?$")

    def _split_label(self, spec):
        """Parse 'label: term' or 'term'.

        Returns ``(label_or_None, kernel_term)``. Tries label-form first; if
        the remainder fails to parse, falls back to treating the whole spec
        as a term (so ``"!x:num. x = x"`` survives).
        """
        m = self._LABEL_RE.match(spec)
        if m:
            label = m.group(1)
            rest = m.group(2)
            try:
                return label, self._parse(rest)
            except ParseError:
                pass
        return None, self._parse(spec)

    def _fresh_label(self, prefix="h"):
        while True:
            self._anon += 1
            name = f"_{prefix}{self._anon}"
            if name not in self._facts:
                return name

    # ---- facts -----------------------------------------------------------

    def _register_fact(self, label, th):
        if label in self._facts:
            raise HolError(f"duplicate fact label: {label!r}")
        self._facts[label] = th
        self._fact_order.append(label)
        self._cur.facts_added.append(label)

    def _drop_facts(self, labels):
        for label in labels:
            self._facts.pop(label, None)
        if labels:
            drop = set(labels)
            self._fact_order = [l for l in self._fact_order if l not in drop]

    def _resolve_fact(self, ref):
        """Resolve `ref` to a theorem.

        Accepts a ``thm`` directly, a string label, or a negative integer
        (index into insertion order)."""
        if isinstance(ref, thm):
            return ref
        if isinstance(ref, str):
            if ref in self._facts:
                return self._facts[ref]
            raise HolError(f"unknown fact label: {ref!r}")
        if isinstance(ref, int):
            try:
                return self._facts[self._fact_order[ref]]
            except IndexError:
                raise HolError(f"fact index out of range: {ref}")
        raise HolError(f"cannot resolve fact reference: {ref!r}")

    def fact(self, ref):
        """Public accessor: returns the theorem associated with a label or index."""
        return self._resolve_fact(ref)

    def _resolve_fact_or_term(self, ref):
        """Like _resolve_fact but a non-fact string is parsed as a term."""
        if isinstance(ref, thm):
            return ref
        if isinstance(ref, int):
            return self._resolve_fact(ref)
        if isinstance(ref, str):
            if ref in self._facts:
                return self._facts[ref]
            return self._parse(ref)
        return ref

    # ---- public API: opening declarations --------------------------------

    def goal(self, spec, types=None):
        """Set the goal for the current frame.

        ``types``: optional ``{name: hol_type}`` mapping registering
        higher-order or non-default-type parameters in scope. The parser
        consults these when it encounters bare identifiers *or* binders
        (``!f. ...``) so HO parameters can appear naturally in the goal
        and subsequent ``fix``/``assume``/``have`` terms.
        """
        if self._cur.goal is not None:
            raise HolError("goal: already set on current frame")
        if types:
            for name, ty in types.items():
                self._cur.type_env[name] = ty
        self._cur.goal = self._parse(spec)

    def fix(self, names):
        if isinstance(names, str):
            names = names.split()
        for nm in names:
            g = self._cur.goal
            if not (isinstance(g, Comb) and isinstance(g.fun, Const)
                    and g.fun.name == "!" and isinstance(g.arg, Abs)):
                raise HolError(f"fix({nm!r}): goal is not a forall: {pp(g)}")
            v = g.arg.bvar
            if v.name != nm:
                raise HolError(
                    f"fix: name mismatch -- binder is {v.name!r}, given {nm!r}")
            self._cur.goal = g.arg.body
            self._cur.vars_added.append(v)

    def let(self, spec, types=None):
        """Register a local abbreviation in the current frame
        (Isabelle-style ``define``).

        Spec form: ``"NAME(arg1, arg2, ...) := body"``; each arg may carry
        an optional type annotation (``arg:ty``). The body parses in the
        current scope extended with the placeholders.

        Mechanics: a fresh kernel ``Var`` of the appropriate function type
        is introduced as the *carrier*, plus a local equation
        ``[!args. NAME args = body] |- !args. NAME args = body``. Goals
        and facts mention ``NAME`` in folded form; use ``p.unfold_let`` /
        ``p.fold_let`` to convert to/from the body. The local-equation
        hypothesis is discharged on frame close (carrier substituted with
        ``\\args. body``, BETA-normalized) so the resulting theorem has
        no lazy-let baggage and never names ``NAME`` outside the frame.

        ``types``: optional ``{name: hol_type}`` mapping supplying types
        for bvars whose desired type is not registered as a parser alias
        (e.g. fresh tyvars or function types). Also extends the
        body-parsing env so other free names in ``body`` can be typed.

        Lifetime: the binding dies with the current frame (same as
        ``vars_added`` and ``facts_added``).
        """
        m = self._LET_SPEC_RE.match(spec)
        if not m:
            raise HolError(
                f"let: expected 'NAME(arg1, arg2, ...) := body' "
                f"(args may be annotated 'arg:ty'), got {spec!r}")
        name, args_str, body_str = m.groups()
        types = types or {}

        bvars = []
        seen = set()
        for piece in args_str.split(","):
            am = self._LET_ARG_RE.match(piece)
            if not am:
                raise HolError(
                    f"let: cannot parse arg declaration {piece!r} in {spec!r}")
            arg_name, ty_name = am.groups()
            if arg_name in seen:
                raise HolError(
                    f"let: duplicate arg name {arg_name!r} in {spec!r}")
            seen.add(arg_name)
            if ty_name is not None:
                if ty_name not in DEFAULT_SIG.type:
                    raise HolError(f"let: unknown type {ty_name!r}")
                bvar_ty = DEFAULT_SIG.type[ty_name]
            elif arg_name in types:
                bvar_ty = types[arg_name]
            else:
                bvar_ty = DEFAULT_SIG.default_var_ty
                if bvar_ty is None:
                    raise HolError(
                        "let: no default type registered; annotate the bvar "
                        f"as '{name}({arg_name}:T, ...) := ...'")
            bvars.append(Var(arg_name, bvar_ty))

        env = self._scope_env()
        if name in env:
            raise HolError(
                f"let: {name!r} clashes with an existing binding in scope")
        if name in DEFAULT_SIG.const:
            raise HolError(
                f"let: {name!r} clashes with a registered constant")

        # Parse body with the placeholders injected; placeholders shadow
        # any same-named outer scope binding for the duration of the body.
        # ``types`` further extends the env so other free names in body
        # (not bvars) get their declared types.
        body_env = dict(env)
        for nm, ty in types.items():
            if nm not in seen:
                body_env[nm] = ty
        for bv in bvars:
            body_env[bv.name] = bv
        try:
            body = parse(body_str, _env_bindings=body_env)
        except ParseError as ex:
            raise HolError(f"let: cannot parse body: {ex}") from ex

        self._register_lazy_let(name, bvars, body)

    def split_conj(self, ref, *labels):
        """Split a right-associated conjunction fact ``h : a /\\ b /\\ ... /\\ z``
        into the supplied labels, registering each conjunct as its own fact."""
        th = ref if isinstance(ref, thm) else self._resolve_fact(ref)
        # If the fact's top-level isn't already a conjunction (e.g., a
        # folded lazy-let application whose body is a conj), unfold lazy
        # lets to expose it. Avoids unfolding when not needed so other
        # downstream facts that prefer folded shape are unaffected.
        c = th._concl
        if not (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const)
                and c.fun.fun.name == "/\\"):
            th = self._unfold_fact(th)
        cur = th
        n = len(labels)
        for i, lbl in enumerate(labels):
            if i == n - 1:
                self._register_fact(lbl, cur)
            else:
                self._register_fact(lbl, CONJUNCT1(cur))
                cur = CONJUNCT2(cur)

    def assume(self, *labelled):
        for spec in labelled:
            label, term = self._split_label(spec)
            if label is None:
                label = self._fresh_label("h")
            g = self._cur.goal
            if not (isinstance(g, Comb) and isinstance(g.fun, Comb)
                    and isinstance(g.fun.fun, Const)
                    and g.fun.fun.name == "==>"):
                raise HolError(f"assume: goal is not an implication: {pp(g)}")
            ant = g.fun.arg
            cons = g.arg
            if not aconv(ant, term):
                raise HolError(
                    "assume: hypothesis does not match antecedent\n"
                    f"  antecedent: {pp(ant)}\n  given:      {pp(term)}")
            self._cur.goal = cons
            self._cur.hyps_added.append((label, ant))
            self._register_fact(label, ASSUME(ant))

    # ---- have / thus -----------------------------------------------------

    def have(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=False)

    def thus(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=True)

    # ---- block constructs ------------------------------------------------

    def induction(self, var_name):
        body = self._cur.goal
        if body is None:
            raise HolError("induction: no current goal")
        # If the goal is ``!var_name. inner``, peel the binder automatically
        # so the user doesn't need an intermediate fix() call.
        if (isinstance(body, Comb) and isinstance(body.fun, Const)
                and body.fun.name == "!" and isinstance(body.arg, Abs)
                and body.arg.bvar.name == var_name):
            return _InductionCtx(self, body.arg.bvar, body.arg.body,
                                  peel_forall=True)
        env = self._scope_env()
        if var_name not in env:
            raise HolError(f"induction: unknown variable {var_name!r}")
        return _InductionCtx(self, env[var_name], body, peel_forall=False)

    def base(self):
        from num import ONE
        fr = self._cur
        if fr.kind != "_induction":
            raise HolError("base() outside induction()")
        var = fr.data["var"]
        body = fr.data["body"]
        sub_goal = _subst_term(var, ONE, body)

        def on_close(th):
            fr.data["base_th"] = th

        return _SubFrameCtx(self, sub_goal, kind="ind_base",
                             on_close=on_close)

    def step(self, ih_label="IH"):
        from num import mk_suc
        fr = self._cur
        if fr.kind != "_induction":
            raise HolError("step() outside induction()")
        var = fr.data["var"]
        body = fr.data["body"]
        sub_goal = _subst_term(var, mk_suc(var), body)

        def on_close(th):
            fr.data["step_th"] = th

        return _SubFrameCtx(self, sub_goal, kind="ind_step",
                             on_close=on_close,
                             extra_facts=[(ih_label, ASSUME(body))])

    def choose(self, name_spec, from_, eq_label=None):
        """Eliminate an existential, bringing a witness into scope.

        ``name_spec``: ``"name"`` or ``"name: equation"``. The latter form
            verifies the equation matches the body the witness satisfies.
        ``from_``: label of the source fact, which must be ``?v. body``,
            or ``x > y``, or ``x < y`` (auto-unfolded).
        ``eq_label``: label under which to register the equation fact;
            defaults to ``f"{name}_eq"`` so it doesn't clash with the witness
            name (which lives in the parser env).
        """
        m = self._LABEL_RE.match(name_spec)
        if m:
            name = m.group(1)
            eq_check = m.group(2)
        else:
            name = name_spec.strip()
            eq_check = None

        src_th = self._resolve_fact(from_)
        c = src_th._concl

        # If src is a relation registered with an unfolder, unfold to
        # existential first.
        if (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const)
                and c.fun.fun.name in _UNFOLDERS):
            unfold_fn = _UNFOLDERS[c.fun.fun.name]
            a = c.fun.arg
            b = c.arg
            ex_th = EQ_MP(unfold_fn(a, b), src_th)
        else:
            ex_th = src_th

        # ex_th's conclusion must now be `?v. body`.
        exc = ex_th._concl
        if not (isinstance(exc, Comb) and isinstance(exc.fun, Const)
                and exc.fun.name == "?" and isinstance(exc.arg, Abs)):
            raise HolError(
                f"choose: source {from_!r} is not an existential or order relation: "
                f"{pp(c)}")

        pred = exc.arg
        v_var = pred.bvar
        w_term = mk_select(v_var, pred.body)
        # body[w/v]: beta-reduce (pred w).
        body_at_w = rand(BETA_CONV(mk_comb(pred, w_term))._concl)

        if eq_check is not None:
            env = self._scope_env()
            env[name] = w_term
            try:
                expected = parse(eq_check, _env_bindings=env)
            except ParseError as ex:
                raise HolError(f"choose: cannot parse equation spec: {ex}") from ex
            ok = aconv(expected, body_at_w)
            if not ok:
                # Try matching modulo lazy lets (the user wrote a folded
                # body whose unfolded form equals body_at_w, or vice versa).
                expected_unfold = self._unfold_lazy_lets_in_term(expected)
                body_unfold = self._unfold_lazy_lets_in_term(body_at_w)
                if aconv(rand(expected_unfold._concl),
                         rand(body_unfold._concl)):
                    ok = True
            if not ok:
                raise HolError(
                    "choose: equation spec doesn't match witness body\n"
                    f"  expected: {pp(body_at_w)}\n"
                    f"  given:    {pp(expected)}")

        # Register witness in parser env on the current frame.
        if name in self._cur.choose_env:
            raise HolError(f"choose: witness name {name!r} already in use in this scope")
        self._cur.choose_env[name] = w_term

        # Register the equation as a fact (default label = "{name}_eq").
        eq_label = eq_label or f"{name}_eq"
        self._register_fact(eq_label, ASSUME(body_at_w))

        # Defer discharge to frame close.
        self._cur.pending_choose.append((ex_th, pred, exc))

    def _open_cases(self, ref, target, on_close, args=()):
        if args:
            if not isinstance(ref, thm):
                raise HolError(
                    "cases_on: spec args require a theorem source")
            resolved = [self._resolve_fact_or_term(a) for a in args]
            or_th = MP_LIST(ref, resolved)
        else:
            or_th = self._resolve_fact(ref)
        c = or_th._concl
        # If the source is a relation registered with a disjunction unfolder
        # (e.g. ``>=``, ``<=``), unfold to the disjunction first.
        if (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const)
                and c.fun.fun.name in _DISJ_UNFOLDERS):
            unfold_fn = _DISJ_UNFOLDERS[c.fun.fun.name]
            a = c.fun.arg
            b = c.arg
            or_th = EQ_MP(unfold_fn(a, b), or_th)
            c = or_th._concl
        # Expect (p \/ q) at the top.
        if not (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const)
                and c.fun.fun.name == "\\/"):
            raise HolError(f"cases_on: not a disjunction: {pp(c)}")
        return _CasesCtx(self, or_th, target, on_close)

    def cases_on(self, ref, *args):
        """Case-split on a disjunction.

        ``ref`` is a fact label, theorem, or relation fact (``a R b`` for a
        relation registered with ``register_disj_unfolder``). When extra
        ``*args`` are supplied, ``ref`` must be a theorem; the args are
        ``MP_LIST``-applied (each string is parsed as a term, each fact
        label looked up) before the cases are taken — so
        ``cases_on(SATZ_10, "x", "y")`` is equivalent to
        ``cases_on(SPECL([x, y], SATZ_10))``.
        """
        parent = self._cur
        if parent.goal is None:
            raise HolError("cases_on: no current goal")
        return self._open_cases(
            ref, parent.goal,
            lambda res: self._set_frame_result(parent, res),
            args=args)

    def suppose(self, label_spec):
        """Open a hypothetical sub-block to prove a negation goal.

        The current goal must be ``~p``. The block has goal ``F`` and gets
        ``label: p`` registered as a fact. On close, wraps the F-theorem as
        ``NOT_INTRO(DISCH(p, F_th))`` and discharges the parent's ``~p`` goal.
        """
        fr = self._cur
        g = fr.goal
        if g is None or not (isinstance(g, Comb) and isinstance(g.fun, Const)
                and g.fun.name == "~"):
            raise HolError(
                f"suppose: current goal is not a negation: "
                f"{pp(g) if g is not None else 'None'}")
        body = g.arg

        spec = label_spec.strip()
        m = self._LABEL_RE.match(spec)
        if m:
            label = m.group(1)
            try:
                hyp_term = self._parse(m.group(2))
            except ParseError as ex:
                raise HolError(f"suppose: cannot parse hypothesis: {ex}") from ex
            if not aconv(hyp_term, body):
                raise HolError(
                    "suppose: hypothesis does not match negated body\n"
                    f"  body:  {pp(body)}\n  given: {pp(hyp_term)}")
        else:
            if not re.match(r"^[A-Za-z_][A-Za-z_0-9]*$", spec):
                raise HolError(f"suppose: bad label spec: {label_spec!r}")
            label = spec

        def on_close(F_th):
            not_th = NOT_INTRO(DISCH(body, F_th))
            self._set_frame_result(self._cur, not_th)

        return _SubFrameCtx(self, F, kind="suppose",
                             on_close=on_close,
                             extra_facts=[(label, ASSUME(body))])

    def absurd(self):
        """Discharge the current goal as an impossible case by deriving F.

        Returns a helper whose ``.by(...)``/``.by_thm(...)`` produce a
        theorem of conclusion ``F``; this is wrapped via ``CONTR(goal, F_th)``
        and set as the current frame's result.
        """
        fr = self._cur
        if fr.goal is None:
            raise HolError("absurd: no current goal")
        return _Absurd(self, fr.goal)

    def case(self, branch_spec):
        fr = self._cur
        if fr.kind != "_cases":
            raise HolError("case() outside cases_on()")
        label, user_term = self._split_label(branch_spec)
        outer_goal = fr.data["goal"]
        or_concl = fr.data["or_concl"]

        # Walk the right-associated disjunction to find the leaf this user
        # spec corresponds to (alpha-equivalence). Using the *leaf* term for
        # ASSUME/DISCH is essential: DISJ_CASES later requires literal
        # identity with the disjunction's actual disjunct, not just aconv.
        leaf = _find_disj_leaf(or_concl, user_term)
        if leaf is None:
            raise HolError(
                "case: branch does not alpha-match any disjunct\n"
                f"  branch: {pp(user_term)}\n"
                f"  disj:   {pp(or_concl)}")

        def on_close(th):
            fr.data["branches"].append((leaf, th))

        # If the branch hypothesis is itself an existential ``?v. body``,
        # auto-choose the witness inside the case body so the user gets
        # ``v`` in scope and ``v_eq: body[v]`` as a fact, exactly as if they
        # had written ``p.choose("v: body", from_=label)`` themselves. The
        # display name follows the *user*'s spec bvar (so they can rename to
        # avoid clashes with outer scopes); the underlying witness/pred terms
        # come from the leaf so ELIM_EX matches kernel-literally.
        auto_choose = None
        if (isinstance(leaf, Comb) and isinstance(leaf.fun, Const)
                and leaf.fun.name == "?"
                and isinstance(leaf.arg, Abs)):
            leaf_pred = leaf.arg
            leaf_v = leaf_pred.bvar
            w_term = mk_select(leaf_v, leaf_pred.body)
            body_at_w = rand(BETA_CONV(mk_comb(leaf_pred, w_term))._concl)
            user_pred = (user_term.arg
                          if (isinstance(user_term, Comb)
                              and isinstance(user_term.fun, Const)
                              and user_term.fun.name == "?"
                              and isinstance(user_term.arg, Abs))
                          else None)
            wit_name = user_pred.bvar.name if user_pred else leaf_v.name
            eq_label = f"{wit_name}_eq"
            auto_choose = (wit_name, w_term, eq_label, body_at_w,
                            leaf_pred, leaf)

        return _SubFrameCtx(self, outer_goal, kind="case",
                             on_close=on_close,
                             extra_facts=[(label, ASSUME(leaf))],
                             auto_choose=auto_choose)


# ---------------------------------------------------------------------------
# Have / Thus: justification dispatchers.
# ---------------------------------------------------------------------------

class _Have:
    __slots__ = ("p", "label", "term", "is_thus")

    def __init__(self, p, label, term, is_thus):
        self.p = p
        self.label = label
        self.term = term
        self.is_thus = is_thus

    # ----- finishing: alpha-check, register, optionally close goal -----

    def _finish(self, th):
        if not aconv(concl(th), self.term):
            # Conversion-on-match: if the mismatch is between a folded
            # let-application and its body, reconcile via the lazy-let
            # equation set.
            th_lifted = self.p._match_modulo_lazy_lets(self.term, th)
            if th_lifted is None:
                raise HolError(
                    "have: justification produced wrong conclusion\n"
                    f"  expected: {pp(self.term)}\n"
                    f"  got:      {pp(concl(th))}")
            th = th_lifted
        label = self.label or self.p._fresh_label("h")
        self.p._register_fact(label, th)
        if self.is_thus:
            cur = self.p._cur
            ok = cur.goal is not None and aconv(cur.goal, self.term)
            if not ok and cur.goal is not None:
                # Lazy-let-aware match: both goal and thus-term may carry
                # folded carrier applications; unfold both and re-check.
                g_eq = self.p._unfold_lazy_lets_in_term(cur.goal)
                t_eq = self.p._unfold_lazy_lets_in_term(self.term)
                if aconv(rand(g_eq._concl), rand(t_eq._concl)):
                    ok = True
                    # Pivot th's concl from self.term shape to cur.goal shape
                    # so the frame's recorded result has the same shape as
                    # the original goal.
                    pivot = TRANS(g_eq, SYM(t_eq))   # |- goal = thus_term
                    th = EQ_MP(SYM(pivot), th)
            if not ok:
                raise HolError(
                    "thus: term does not match current goal\n"
                    f"  goal: {pp(cur.goal) if cur.goal is not None else 'None'}\n"
                    f"  thus: {pp(self.term)}")
            self.p._set_frame_result(cur, th)
        return th

    # ----- justification methods -----

    def by_thm(self, th):
        """Direct: the supplied theorem already proves the have-term."""
        return self._finish(th)

    def by(self, justification, *args):
        """SPEC/MP chain (if `justification` is a theorem or fact label) or
        a callable.

        - ``thm | label + args``: each arg is dispatched via MP_LIST -- a
          Term arg becomes ``SPEC``, a Theorem arg becomes ``MP``. Strings
          in ``args`` are interpreted as fact labels (theorem) when known,
          else parsed as terms. A ``str`` ``justification`` is resolved as
          a fact label or negative index.
        - ``callable + args``: each arg is resolved as a fact (string label,
          negative index, or theorem); the callable is invoked on them.
        """
        if isinstance(justification, (str, int)):
            justification = self.p._resolve_fact(justification)
        if isinstance(justification, thm):
            # Auto-unfold a folded justification (e.g. ``R c h 1 m`` from a
            # lazy let) so subsequent SPECs have a forall to peel.
            th = self.p._unfold_fact(justification)
            for a in args:
                resolved = self.p._resolve_fact_or_term(a)
                if isinstance(resolved, thm):
                    th = self.p._mp_modulo_lazy_lets(th, resolved)
                else:
                    th = SPEC(resolved, th)
            return self._finish(th)
        if callable(justification):
            resolved = [self.p._resolve_fact_or_term(a) for a in args]
            return self._finish(justification(*resolved))
        raise HolError(
            f"by: not a theorem or callable: {justification!r}")

    def by_rewrite(self, rules):
        """REWRITE_PROVE with the given rules.

        Each rule may be a Theorem or a string label naming a fact in scope.
        """
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        return self._finish(REWRITE_PROVE(rule_thms, self.term))

    def by_rewrite_of(self, ref, rules):
        """Rewrite an existing fact `ref` with `rules` to obtain the have-term."""
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        fact_th = self.p._resolve_fact(ref)
        return self._finish(REWRITE_RULE(rule_thms, fact_th))

    def by_select(self, axiom, *args):
        """Higher-order-to-first-order boundary helper.

        ``axiom`` is the HO theorem (e.g. ``SELECT_AX`` after ``INST_TYPE``,
        or any custom lemma like ``_SATZ_27_EXISTS_M``).  Each subsequent
        arg is dispatched in order:

        - ``str`` matching a let-name in scope: materialize as kernel ``Abs``,
          ``SPEC`` at it, and ``BETA_RULE`` the result (so the redexes that
          ``SPEC`` introduces normalize back to the let-expansion shape that
          surrounding ``have``/``thus`` terms agree with).
        - ``str`` matching a fact label: ``MP``.
        - ``str`` otherwise: parse as a term and ``SPEC``.
        - kernel ``thm``: ``MP``.
        - kernel term (Var/Const/Comb/Abs): ``SPEC``.

        Replaces the manual ``MP_LIST(BETA_RULE(SPECL([...], LEMMA)), [...])``
        chain at every HO-lemma boundary.
        """
        p = self.p
        th = axiom if isinstance(axiom, thm) else p._resolve_fact(axiom)
        # Auto-unfold the axiom: a folded lazy-let fact like ``R c h 1 m``
        # is lifted to its HO body so the SPEC chain finds a forall.
        th = p._unfold_fact(th)
        for a in args:
            if isinstance(a, str):
                lz = p._lookup_lazy_let(a)
                if lz is not None:
                    # Lazy let: SPEC the HO axiom at the carrier ``Var``
                    # directly. No Abs materialization, no BETA needed.
                    th = SPEC(lz.carrier, th)
                    continue
                if a in p._facts:
                    th = p._mp_modulo_lazy_lets(th, p._facts[a])
                    continue
                th = SPEC(p._parse(a), th)
                continue
            if isinstance(a, thm):
                th = p._mp_modulo_lazy_lets(th, a)
                continue
            th = SPEC(a, th)
        return self._finish(th)

    def by_unfold(self, src, *defs):
        """Prove the goal from ``src`` by unfolding the given definition
        equations (with beta-reduction). The goal and ``src``'s conclusion
        must reduce to the same beta-normal form once ``defs`` fire as
        rewrite rules. Used to bridge a theorem stated in unfolded form
        (e.g. SATZ_9) to a goal stated using the defined symbol (SATZ_10's
        ``>`` / ``<``)."""
        src_th = src if isinstance(src, thm) else self.p._resolve_fact(src)
        rules = [d if isinstance(d, thm) else self.p._resolve_fact(d)
                 for d in defs]
        eq_unfold = REWRITE_CONV(rules, self.term)
        eq_beta = BETA_NORM(rand(eq_unfold._concl))
        eq_goal = TRANS(eq_unfold, eq_beta)
        src_norm = BETA_RULE(REWRITE_RULE(rules, src_th))
        if not aconv(rand(eq_goal._concl), src_norm._concl):
            raise HolError(
                "by_unfold: normal forms differ\n"
                f"  goal -> {pp(rand(eq_goal._concl))}\n"
                f"  src  -> {pp(src_norm._concl)}")
        return self._finish(EQ_MP(SYM(eq_goal), src_norm))

    def by_rewrite_ne(self, ref, eqs):
        """REWRITE_NE on a non-equation fact: takes ``~(a = b)`` and rewrites
        each side via ``[eq_l, eq_r]`` (theorems ``a = a'`` and ``b = b'``)
        to produce the have-term ``~(a' = b')``."""
        if len(eqs) != 2:
            raise HolError(
                f"by_rewrite_ne: expected 2 side equations, got {len(eqs)}")
        ne_th = self.p._resolve_fact(ref)
        eq_l_th = self.p._resolve_fact(eqs[0])
        eq_r_th = self.p._resolve_fact(eqs[1])
        return self._finish(REWRITE_NE(ne_th, eq_l_th, eq_r_th))

    def by_cases(self, ref, *args):
        """Open a cases-on block whose target is the have-term (rather than
        the parent's goal). On close, the combined ``DISJ_CASES`` result is
        registered as the have's fact (and, if invoked from ``thus``, also
        becomes the current frame's result).

        Like ``cases_on``, accepts extra ``*args`` to ``MP_LIST``-specialize
        a theorem source inline."""
        return self.p._open_cases(ref, self.term, self._finish, args=args)

    def proof(self):
        """Open a sub-frame whose goal is the have-term. The body proves it
        via standard tactics (``thus``, ``cases_on``, ``induction``, …); on
        exit the resulting theorem is registered as the have's fact (and,
        if invoked from ``thus``, also closes the parent goal).

        This is the declarative analogue of writing an intermediate lemma
        inline — the dream sketch's ``.proof(lambda q: …)`` block."""
        return _SubFrameCtx(self.p, self.term, kind="have_proof",
                             on_close=self._finish)

    def by_eq_mp(self, eq_th, ref):
        """``EQ_MP(eq_th, fact)`` -- rewrite a fact through an equation."""
        return self._finish(EQ_MP(eq_th, self.p._resolve_fact(ref)))

    def by_fold(self, ref):
        """Inverse of an unfolder: if the have-term is ``a R b`` for a
        relation ``R`` registered with ``register_unfolder`` or
        ``register_disj_unfolder``, fold ``ref`` (whose conclusion equals the
        unfolded form) back into ``a R b``."""
        target = self.term
        if not (isinstance(target, Comb) and isinstance(target.fun, Comb)
                and isinstance(target.fun.fun, Const)):
            raise HolError(
                f"by_fold: target is not a binary relation: {pp(target)}")
        op_name = target.fun.fun.name
        if op_name in _UNFOLDERS:
            unfold_fn = _UNFOLDERS[op_name]
        elif op_name in _DISJ_UNFOLDERS:
            unfold_fn = _DISJ_UNFOLDERS[op_name]
        else:
            raise HolError(
                f"by_fold: no unfolder registered for {op_name!r}")
        a = target.fun.arg
        b = target.arg
        fact = self.p._resolve_fact(ref)
        return self._finish(EQ_MP(SYM(unfold_fn(a, b)), fact))

    def by_witness(self, witness, ref):
        """For an existential have-term ``?v. P v`` (or a registered relation
        ``a R b`` whose unfolded form is ``?v. body``), given a fact whose
        conclusion is ``P[witness/v]``, produce ``?v. P v`` via ``EXISTS``
        (and fold back through the relation's unfolder if applicable).

        ``witness`` is parsed in the current scope (so ``choose``-bound names
        are available) or accepted as a kernel term directly. ``ref`` is a
        fact label, fact index, or a theorem.
        """
        target = self.term
        p = self.p

        fact_th = ref if isinstance(ref, thm) else p._resolve_fact(ref)
        witness_t = p._parse(witness) if isinstance(witness, str) else witness

        # Direct existential: ?v. body.
        if (isinstance(target, Comb) and isinstance(target.fun, Const)
                and target.fun.name == "?" and isinstance(target.arg, Abs)):
            # The expected fact shape is ``P[witness/v]``. If the supplied
            # fact is in folded lazy-let form (or vice versa), align it
            # via conversion-on-match before EXISTS.
            from tactics import _subst_term
            expected = _subst_term(target.arg.bvar, witness_t, target.arg.body)
            if not aconv(fact_th._concl, expected):
                lifted = p._match_modulo_lazy_lets(expected, fact_th)
                if lifted is not None:
                    fact_th = lifted
            return self._finish(EXISTS(target.arg, witness_t, fact_th))

        # Registered relation a R b: unfold, EXISTS, fold back.
        if (isinstance(target, Comb) and isinstance(target.fun, Comb)
                and isinstance(target.fun.fun, Const)
                and target.fun.fun.name in _UNFOLDERS):
            op_name = target.fun.fun.name
            unfold_eq = _UNFOLDERS[op_name](target.fun.arg, target.arg)
            ex_term = rand(unfold_eq._concl)
            if not (isinstance(ex_term, Comb) and isinstance(ex_term.fun, Const)
                    and ex_term.fun.name == "?" and isinstance(ex_term.arg, Abs)):
                raise HolError(
                    f"by_witness: unfolded form of {op_name!r} is not "
                    f"existential: {pp(ex_term)}")
            ex_th = EXISTS(ex_term.arg, witness_t, fact_th)
            return self._finish(EQ_MP(SYM(unfold_eq), ex_th))

        raise HolError(
            "by_witness: target is not existential or a registered relation: "
            f"{pp(target)}")

    def by_disj(self, ref):
        """Given a fact whose conclusion alpha-matches one of the goal's
        right-associated disjuncts, build the ``DISJ1``/``DISJ2`` chain to
        inject it as the proof of the whole disjunction."""
        target = self.term
        fact_th = ref if isinstance(ref, thm) else self.p._resolve_fact(ref)

        def build(disj, th):
            if aconv(disj, fact_th._concl):
                return th
            if not (isinstance(disj, Comb) and isinstance(disj.fun, Comb)
                    and isinstance(disj.fun.fun, Const)
                    and disj.fun.fun.name == "\\/"):
                raise HolError(
                    "by_disj: fact conclusion does not match any disjunct\n"
                    f"  fact: {pp(fact_th._concl)}\n"
                    f"  goal: {pp(target)}")
            p_part = disj.fun.arg
            q_part = disj.arg
            if aconv(p_part, fact_th._concl):
                return DISJ1(th, q_part)
            return DISJ2(p_part, build(q_part, th))

        try:
            return self._finish(build(target, fact_th))
        except HolError:
            # Fallback: target may be a folded lazy-let application whose
            # body is the disjunction. Unfold, build there, fold back.
            unfold_eq = self.p._unfold_lazy_lets_in_term(target)
            target_un = rand(unfold_eq._concl)
            if aconv(target_un, target):
                raise
            th_un = build(target_un, fact_th)
            th = EQ_MP(SYM(unfold_eq), th_un)
            return self._finish(th)

    def by_ac(self, op, assoc, comm):
        """AC_PROVE under ``(op, assoc, comm)`` for the (equation) have-term."""
        return self._finish(AC_PROVE(op, assoc, comm, self.term))

    def by_rewrite_ac(self, rules, op, assoc, comm, ac_rules=()):
        """REWRITE_AC_PROVE -- rewrite both sides under ``rules`` (and optional
        ``ac_rules`` for canonicalisation), then close by AC over ``op``."""
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        ac_thms = tuple(self.p._resolve_fact(r) if not isinstance(r, thm) else r
                        for r in ac_rules)
        return self._finish(REWRITE_AC_PROVE(rule_thms, op, assoc, comm,
                                              self.term, ac_rules=ac_thms))


# ---------------------------------------------------------------------------
# Absurd: derive F from the current scope and CONTR-wrap to the frame's goal.
# ---------------------------------------------------------------------------

class _Absurd:
    __slots__ = ("p", "target")

    def __init__(self, p, target):
        self.p = p
        self.target = target

    def _finish(self, F_th):
        if not aconv(F_th._concl, F):
            raise HolError(
                f"absurd: justification did not produce F: {pp(F_th._concl)}")
        result = CONTR(self.target, F_th)
        self.p._set_frame_result(self.p._cur, result)
        return result

    def by_thm(self, th):
        return self._finish(th)

    def by(self, justification, *args):
        if isinstance(justification, thm):
            resolved = [self.p._resolve_fact_or_term(a) for a in args]
            return self._finish(MP_LIST(justification, resolved))
        if callable(justification):
            resolved = [self.p._resolve_fact_or_term(a) for a in args]
            return self._finish(justification(*resolved))
        raise HolError(
            f"absurd: not a theorem or callable: {justification!r}")

    def by_conj(self, *refs):
        """Discharge F from a fact ``P`` and a fact ``~P`` (in either order).

        The two refs name a positive fact and its direct negation; we run
        ``MP(NOT_ELIM(neg), pos)``."""
        if len(refs) != 2:
            raise HolError(
                f"absurd: by_conj requires exactly two facts, got {len(refs)}")
        ths = [self.p._resolve_fact(r) for r in refs]
        for pos, neg in (ths, ths[::-1]):
            c = neg._concl
            if (isinstance(c, Comb) and isinstance(c.fun, Const)
                    and c.fun.name == "~" and aconv(c.arg, pos._concl)):
                return self._finish(MP(NOT_ELIM(neg), pos))
        raise HolError(
            "absurd: by_conj could not match P / ~P among "
            f"{pp(ths[0]._concl)} / {pp(ths[1]._concl)}")

    def auto(self, *refs):
        """Discharge F by inspecting the conclusions of the supplied facts.

        Each fact's conclusion is classified as ``rel a b`` for some binary
        relation symbol ``rel``; a finder registered via
        ``register_contra_finder`` for the resulting pair of relations
        (in either order) produces ``|- F``.
        """
        if len(refs) != 2:
            raise HolError(
                f"absurd: auto() requires exactly two facts, got {len(refs)}")
        ths = [self.p._resolve_fact_or_term(r) for r in refs]
        cs = [_classify_contra(th._concl) for th in ths]
        if cs[0] is None or cs[1] is None:
            raise HolError(
                "absurd: auto() cannot classify fact shapes: "
                f"{pp(ths[0]._concl)} / {pp(ths[1]._concl)}")
        rel0, rel1 = cs[0][0], cs[1][0]
        finder = _CONTRA_FINDERS.get((rel0, rel1))
        if finder is not None:
            return self._finish(finder(ths[0], ths[1]))
        finder = _CONTRA_FINDERS.get((rel1, rel0))
        if finder is not None:
            return self._finish(finder(ths[1], ths[0]))
        raise HolError(
            f"absurd: auto() has no finder for ({rel0!r}, {rel1!r})")


def _classify_contra(t):
    """Return ``(rel_name, a, b)`` for ``rel a b``, else ``None``."""
    match t:
        case Comb(Comb(Const(name, _), a), b):
            return (name, a, b)
    return None


# ---------------------------------------------------------------------------
# Sub-frame context manager: pushes a frame with a sub-goal, on exit verifies
# discharge and reports the result back to the parent via ``on_close``.
# ---------------------------------------------------------------------------

class _SubFrameCtx:
    def __init__(self, p, goal, kind, on_close, extra_facts=(),
                  auto_choose=None):
        self.p = p
        self.goal = goal
        self.kind = kind
        self.on_close = on_close
        self.extra_facts = list(extra_facts)
        self.auto_choose = auto_choose

    def __enter__(self):
        fr = _Frame(goal=self.goal, kind=self.kind)
        self.p._frames.append(fr)
        for label, th in self.extra_facts:
            if label is None:
                label = self.p._fresh_label("h")
            self.p._register_fact(label, th)
        if self.auto_choose is not None:
            wit_name, w_term, eq_label, body_at_w, pred, hyp_ex = self.auto_choose
            if wit_name in fr.choose_env:
                raise HolError(
                    f"case: witness name {wit_name!r} clashes with an "
                    f"existing chooser-bound name in this scope")
            fr.choose_env[wit_name] = w_term
            self.p._register_fact(eq_label, ASSUME(body_at_w))
            fr.pending_choose.append((ASSUME(hyp_ex), pred, hyp_ex))
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        if fr.result is None:
            raise HolError(
                f"{self.kind}: block did not discharge sub-goal via thus")
        th = fr.result
        # See note in `proof()` decorator: DISCH first to clear out
        # carrier-mentioning assume-hyps, then discharge lazy lets so the
        # equation hyp is gone before GEN tries to ABS over fix-vars,
        # then GEN.
        for label, term in reversed(fr.hyps_added):
            th = DISCH(term, th)
        th = self.p._discharge_lazy_lets(fr, th)
        for v in reversed(fr.vars_added):
            th = GEN(v, th)
        self.p._drop_facts(fr.facts_added)
        self.on_close(th)
        return False


# ---------------------------------------------------------------------------
# Induction block: pushes an "_induction" frame whose .base() / .step()
# children fill in base_th / step_th. On exit, INDUCT_PROVE composes them and
# the result is set as the parent frame's .result, after SPEC'ing the
# induction variable so the resulting term matches the parent's body-shaped
# goal (the outer fix() will GEN it back).
# ---------------------------------------------------------------------------

class _InductionCtx:
    def __init__(self, p, var, body, peel_forall=False):
        self.p = p
        self.var = var
        self.body = body
        self.peel_forall = peel_forall

    def __enter__(self):
        fr = _Frame(goal=None, kind="_induction")
        fr.data = {"var": self.var, "body": self.body,
                   "base_th": None, "step_th": None}
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        d = fr.data
        if d["base_th"] is None:
            raise HolError("induction: missing base()")
        if d["step_th"] is None:
            raise HolError("induction: missing step()")
        # User's step_th already contains ASSUME(body) as a hypothesis (under
        # the IH label). INDUCT_PROVE wraps that with DISCH(body, ...) and
        # GEN(var, ...) to produce |- !var. body. If the parent's goal already
        # has a !var binder, leave it as is; otherwise SPEC var back out so
        # the parent's body-shaped goal matches.
        from num import INDUCT_PROVE
        forall_th = INDUCT_PROVE(self.var, self.body, d["base_th"],
                                  lambda IH: d["step_th"])
        body_th = forall_th if self.peel_forall else SPEC(self.var, forall_th)
        body_th = self.p._discharge_lazy_lets(fr, body_th)
        self.p._drop_facts(fr.facts_added)
        parent = self.p._cur
        if parent.goal is None or not aconv(parent.goal, body_th._concl):
            raise HolError(
                "induction: produced wrong conclusion\n"
                f"  goal: {pp(parent.goal) if parent.goal else 'None'}\n"
                f"  got:  {pp(body_th._concl)}")
        self.p._set_frame_result(parent, body_th)
        return False


# ---------------------------------------------------------------------------
# cases_on block: pushes a "_cases" frame; .case() children supply each
# branch's proof under an extra hypothesis. On exit, DISJ_CASES composes them.
# ---------------------------------------------------------------------------

def _find_disj_leaf(or_concl, target):
    """Walk a right-associated disjunction; return the leaf alpha-equivalent
    to ``target``, or ``None``. The whole disjunction itself is also a valid
    leaf (matched at depth 0)."""
    if aconv(or_concl, target):
        return or_concl
    if not (isinstance(or_concl, Comb) and isinstance(or_concl.fun, Comb)
            and isinstance(or_concl.fun.fun, Const)
            and or_concl.fun.fun.name == "\\/"):
        return None
    if aconv(or_concl.fun.arg, target):
        return or_concl.fun.arg
    return _find_disj_leaf(or_concl.arg, target)


def _split_disj_n(term, n):
    """Right-associated split of ``p1 \\/ (p2 \\/ (... \\/ pn))`` into a
    list of exactly ``n`` disjuncts, or ``None`` if the shape doesn't fit."""
    leaves = [term]
    while len(leaves) < n:
        last = leaves[-1]
        if not (isinstance(last, Comb) and isinstance(last.fun, Comb)
                and isinstance(last.fun.fun, Const)
                and last.fun.fun.name == "\\/"):
            return None
        leaves[-1] = last.fun.arg
        leaves.append(last.arg)
    return leaves


def _build_disj_cases(or_th, branches):
    """Compose nested ``DISJ_CASES`` over a right-associated disjunction.

    ``or_th``'s conclusion is ``p1 \\/ (p2 \\/ (... \\/ pn))``; ``branches``
    is the matching ordered list of ``(disjunct_term, branch_th)`` pairs
    where each ``branch_th`` proves the target under hypothesis
    ``disjunct_term``. Returns the combined theorem with all branch
    hypotheses discharged."""
    if len(branches) == 2:
        l_term, l_th = branches[0]
        r_term, r_th = branches[1]
        return DISJ_CASES(or_th, DISCH(l_term, l_th), DISCH(r_term, r_th))
    head_term, head_th = branches[0]
    rest_or = or_th._concl.arg
    inner_th = _build_disj_cases(ASSUME(rest_or), branches[1:])
    return DISJ_CASES(or_th,
                      DISCH(head_term, head_th),
                      DISCH(rest_or, inner_th))


class _CasesCtx:
    def __init__(self, p, or_th, target, on_close):
        self.p = p
        self.or_th = or_th
        self.target = target
        self.on_close = on_close

    def __enter__(self):
        fr = _Frame(goal=self.target, kind="_cases")
        fr.data = {"goal": self.target, "branches": [],
                    "or_concl": self.or_th._concl}
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        branches = fr.data["branches"]
        n = len(branches)
        if n < 2:
            raise HolError(
                f"cases_on: need at least 2 case() blocks, got {n}")
        leaves = _split_disj_n(self.or_th._concl, n)
        if leaves is None:
            raise HolError(
                f"cases_on: cannot split into {n} disjuncts: "
                f"{pp(self.or_th._concl)}")
        # Match each user-supplied case to a leaf (preserves leaf order).
        slots = [None] * n
        for branch_term, th in branches:
            placed = False
            for i, leaf in enumerate(leaves):
                if slots[i] is None and aconv(leaf, branch_term):
                    slots[i] = (branch_term, th)
                    placed = True
                    break
            if not placed:
                raise HolError(
                    f"cases_on: branch does not match any disjunct: "
                    f"{pp(branch_term)}")
        if any(s is None for s in slots):
            missing = [pp(leaves[i]) for i, s in enumerate(slots) if s is None]
            raise HolError(f"cases_on: missing case for {missing}")
        result = _build_disj_cases(self.or_th, slots)
        result = self.p._discharge_lazy_lets(fr, result)
        self.p._drop_facts(fr.facts_added)
        if not aconv(self.target, result._concl):
            raise HolError(
                "cases_on: produced wrong conclusion\n"
                f"  target: {pp(self.target)}\n"
                f"  got:    {pp(result._concl)}")
        self.on_close(result)
        return False


# ---------------------------------------------------------------------------
# Decorator: runs the script function and returns the kernel theorem.
# ---------------------------------------------------------------------------

def proof(fn):
    p = Proof()
    fn(p)
    if len(p._frames) != 1:
        raise HolError(
            f"proof({fn.__name__}): unbalanced frames at end ({len(p._frames)} open)")
    fr = p._frames[0]
    if fr.result is None:
        raise HolError(
            f"proof({fn.__name__}): no result -- did you forget thus or close a block?")
    th = fr.result
    # Order matters:
    # 1. DISCH first so any user-``assume``d hyps that mention the lazy-let
    #    carrier move out of ``_asl`` and into the conclusion; the ensuing
    #    INST in discharge can BETA-clean them.
    # 2. Discharge lazy lets next so the equation hyp (and any free fix-var
    #    appearing in it) is gone before GEN tries to ABS over those vars.
    # 3. GEN last over fix-vars.
    for label, term in reversed(fr.hyps_added):
        th = DISCH(term, th)
    th = p._discharge_lazy_lets(fr, th)
    for v in reversed(fr.vars_added):
        th = GEN(v, th)
    return th


# ---------------------------------------------------------------------------
# Self-test: port SATZ_5 (induction + rewrite) and SATZ_17 (cases_on) and
# verify they alpha-equal the existing theorems in nat.py.
# ---------------------------------------------------------------------------

def _selftest():
    import nat
    from nat import (
        ADD_1, ADD_SUC, UNFOLD_LE, LT_TO_LE, SATZ_16A,
    )

    @proof
    def SATZ_5_NEW(p):
        p.goal("!x y z. (x + y) + z = x + (y + z)")
        p.fix("x y z")
        with p.induction("z"):
            with p.base():
                p.thus("(x + y) + 1 = x + (y + 1)")\
                    .by_rewrite([ADD_1, ADD_SUC])
            with p.step("IH"):
                p.thus("(x + y) + SUC z = x + (y + SUC z)")\
                    .by_rewrite([ADD_SUC, "IH"])

    assert aconv(concl(SATZ_5_NEW), concl(nat.SATZ_5)), \
        f"SATZ_5 mismatch:\n  new: {pp(concl(SATZ_5_NEW))}\n  old: {pp(concl(nat.SATZ_5))}"
    assert SATZ_5_NEW._asl == nat.SATZ_5._asl

    # SATZ_17: x <= y, y <= z ==> x <= z. Cases on y < z \/ y = z.
    from nat import x as VX, y as VY, z as VZ

    @proof
    def SATZ_17_NEW(p):
        p.goal("!x y z. x <= y ==> y <= z ==> x <= z")
        p.fix("x y z")
        p.assume("hxy: x <= y", "hyz: y <= z")
        p.have("yz_or: (y < z) \\/ (y = z)")\
            .by_eq_mp(UNFOLD_LE(VY, VZ), "hyz")
        with p.cases_on("yz_or"):
            with p.case("y < z"):
                p.have("xz_lt: x < z").by(SATZ_16A, "x", "y", "z", "hxy", -1)
                p.thus("x <= z").by(LT_TO_LE, "xz_lt")
            with p.case("y = z"):
                p.thus("x <= z").by_rewrite_of("hxy", [-1])

    assert aconv(concl(SATZ_17_NEW), concl(nat.SATZ_17)), \
        f"SATZ_17 mismatch:\n  new: {pp(concl(SATZ_17_NEW))}\n  old: {pp(concl(nat.SATZ_17))}"
    assert SATZ_17_NEW._asl == nat.SATZ_17._asl

    # ---- p.let smoke tests (Isabelle-style) ----------------------------
    from fusion import mk_var
    from num import ONE, num_ty

    # (1) Basic round-trip via the lazy let: ``M 1`` (folded) is bridged
    # to ``1 = 1`` (REFL) through conversion-on-match in _finish.
    @proof
    def LET_REFL(p):
        p.goal("1 = 1")
        p.let("M(x) := x = x")
        p.thus("M 1").by_thm(REFL(ONE))
    assert aconv(concl(LET_REFL), parse("1 = 1"))

    # (2) Let-name in have-term, body closes over fix-var 'a'.
    @proof
    def LET_FIX(p):
        p.goal("!a. a = a")
        p.fix("a")
        p.let("M(x) := x = a")
        p.thus("M a").by_thm(REFL(mk_var("a", num_ty)))
    assert aconv(concl(LET_FIX), parse("!a. a = a"))

    # (3) Collision with fix-var refused.
    pp_proof = Proof()
    pp_proof.goal("!x. x = x")
    pp_proof.fix("x")
    try:
        pp_proof.let("x(y) := y = y")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for let/fix-var collision")

    # (4) Multi-arg let: ``R(a, b) := a + b = b + a`` proves
    # ``R 1 1`` from REFL of ``1 + 1`` via conversion-on-match.
    @proof
    def LET_MULTI(p):
        p.goal("1 + 1 = 1 + 1")
        p.let("R(a, b) := a + b = b + a")
        p.thus("R 1 1").by_thm(REFL(parse("1 + 1")))
    assert aconv(concl(LET_MULTI), parse("1 + 1 = 1 + 1"))

    # (5) by_select with a multi-arg let: trivial 2-ary HO axiom
    # ``|- !Q. Q 1 1 ==> Q 1 1`` at ``R(a, b) := a = b``.
    from fusion import bool_ty
    Q2_ty = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))
    Q2_var = mk_var("Q", Q2_ty)
    Q2_at_11 = mk_comb(mk_comb(Q2_var, ONE), ONE)
    trivial_HO_2 = GEN(Q2_var, DISCH(Q2_at_11, ASSUME(Q2_at_11)))
    @proof
    def BY_SELECT_MULTI(p):
        p.goal("1 = 1")
        p.let("R(a, b) := a = b")
        p.have("R_11: R 1 1").by_thm(REFL(ONE))
        p.thus("R 1 1").by_select(trivial_HO_2, "R", "R_11")
    assert aconv(concl(BY_SELECT_MULTI), parse("1 = 1"))

    # (6) Bad spec rejected.
    try:
        Proof().let("R(a b) := a = b")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for malformed multi-arg spec")

    # (7) Duplicate argument names rejected.
    try:
        Proof().let("R(a, a) := a = a")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for duplicate let arg names")

    # ---- p.unfold smoke test --------------------------------------------
    from num import SUC_DEF
    # Unary def: SUC_DEF : |- SUC = \n. mk_num (IND_SUC (dest_num n)).
    x_v = mk_var("x", num_ty)
    expected_unary = BETA_RULE(AP_THM(SUC_DEF, x_v))
    got_unary = Proof().unfold(SUC_DEF, x_v)
    assert aconv(got_unary._concl, expected_unary._concl), \
        "p.unfold (unary): mismatch"
    assert got_unary._asl == expected_unary._asl

    # Binary def: GT_DEF : |- > = \x y. ?u. x = y + u (defined in nat).
    from nat import GT_DEF, UNFOLD_GT, x as VX, y as VY
    expected_binary = UNFOLD_GT(VX, VY)
    got_binary = Proof().unfold(GT_DEF, VX, VY)
    assert aconv(got_binary._concl, expected_binary._concl), \
        "p.unfold (binary): mismatch"

    # String form: parses argument in current scope.
    p_str = Proof()
    p_str.goal("!x. x = x")
    p_str.fix("x")
    got_str = p_str.unfold(SUC_DEF, "x")
    assert aconv(got_str._concl, expected_unary._concl)

    # ---- _Have.by_select smoke test -------------------------------------
    # Build a tiny HO lemma `|- !P. P 1 ==> P 1` and apply by_select with a
    # let-defined predicate plus a witness fact, verifying the SPEC + BETA_RULE
    # + MP chain produces the right theorem.
    P_var = mk_var("P", mk_fun_ty(num_ty, bool_ty))
    P_1   = mk_comb(P_var, ONE)
    trivial_HO = GEN(P_var, DISCH(P_1, ASSUME(P_1)))   # |- !P. P 1 ==> P 1

    @proof
    def BY_SELECT_TEST(p):
        p.goal("1 = 1")
        p.let("M(x) := x = x")
        p.have("M_1: M 1").by_thm(REFL(ONE))
        p.thus("M 1").by_select(trivial_HO, "M", "M_1")
    assert aconv(concl(BY_SELECT_TEST), parse("1 = 1"))

    # ---- lazy-let registry smoke test -----------------------------------
    # Direct call to _register_lazy_let: confirm carrier is a fresh Var of
    # the right function type, equation has the expected shape, and lookup
    # finds the registered binding.
    p_lazy = Proof()
    a_v = Var("a", num_ty)
    body_aa = mk_eq(a_v, a_v)                    # body: a = a (bool)
    ld = p_lazy._register_lazy_let("MX", [a_v], body_aa)
    # Carrier: Var named "MX" with type num -> bool.
    assert isinstance(ld.carrier, Var) and ld.carrier.name == "MX"
    assert ld.carrier.ty == mk_fun_ty(num_ty, bool_ty)
    # Equation conclusion: !a. MX a = (a = a).
    expected_eq = mk_forall(a_v, mk_eq(mk_comb(ld.carrier, a_v), body_aa))
    assert aconv(ld.eq_th._concl, expected_eq), \
        f"lazy-let eq mismatch: {pp(ld.eq_th._concl)} vs {pp(expected_eq)}"
    # Equation hypothesis: same as conclusion (introduced via ASSUME).
    assert len(ld.eq_th._asl) == 1 and aconv(ld.eq_th._asl[0], expected_eq), \
        f"lazy-let hyp mismatch: {ld.eq_th._asl}"
    # Lookup: scope chain finds it.
    assert p_lazy._lookup_lazy_let("MX") is ld
    assert p_lazy._lookup_lazy_let("missing") is None
    # Re-registration on the same frame raises.
    try:
        p_lazy._register_lazy_let("MX", [a_v], body_aa)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError on duplicate lazy-let register")
    # Multi-arg: MX2(a, b) := a = b.
    b_v = Var("b", num_ty)
    body_ab = mk_eq(a_v, b_v)
    ld2 = p_lazy._register_lazy_let("MX2", [a_v, b_v], body_ab)
    expected_ty2 = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))
    assert ld2.carrier.ty == expected_ty2
    expected_eq2 = mk_forall(a_v, mk_forall(b_v,
        mk_eq(mk_comb(mk_comb(ld2.carrier, a_v), b_v), body_ab)))
    assert aconv(ld2.eq_th._concl, expected_eq2), \
        f"lazy-let multi-arg eq mismatch: {pp(ld2.eq_th._concl)}"

    # ---- lazy by_select smoke test --------------------------------------
    # Register a lazy let MZ(x) := x = x directly, then verify by_select
    # with "MZ" produces a folded ``MZ 1`` theorem (rather than an unfolded
    # ``1 = 1``).
    p_bsl = Proof()
    a_v_l = Var("x", num_ty)
    body_xx = mk_eq(a_v_l, a_v_l)
    lz = p_bsl._register_lazy_let("MZ", [a_v_l], body_xx)
    p_bsl.goal("MZ 1")
    # MZ 1 = (1 = 1) via SPEC; EQ_MP(SYM(...), REFL 1) gives |- MZ 1 (with
    # the local-equation hypothesis still attached).
    eq_at_1 = SPEC(ONE, lz.eq_th)
    mz_1_th = EQ_MP(SYM(eq_at_1), REFL(ONE))
    p_bsl.have("MZ_1: MZ 1").by_thm(mz_1_th)
    p_bsl.thus("MZ 1").by_select(trivial_HO, "MZ", "MZ_1")
    # The frame's result is the folded ``MZ 1`` theorem; verify shape.
    assert p_bsl._cur.result is not None
    assert aconv(p_bsl._cur.result._concl, parse("MZ 1",
                                                  _env_bindings={"MZ": lz.carrier})), \
        f"lazy by_select: unexpected concl {pp(p_bsl._cur.result._concl)}"

    # ---- p.unfold_let / p.fold_let smoke test ---------------------------
    # Register MN(x) := x + x; verify unfold_let yields |- MN 1 = 1 + 1.
    p_ul = Proof()
    x_v_u = Var("x", num_ty)
    plus_x_x = parse("x + x", _env_bindings={"x": x_v_u})
    lz_n = p_ul._register_lazy_let("MN", [x_v_u], plus_x_x)
    eq_at_one = p_ul.unfold_let("MN", ONE)
    expected = mk_eq(mk_comb(lz_n.carrier, ONE), parse("1 + 1"))
    assert aconv(eq_at_one._concl, expected), \
        f"unfold_let: {pp(eq_at_one._concl)} vs {pp(expected)}"
    # String arg form (parsed in current scope).
    p_ul.goal("MN 1 = 1 + 1")
    eq_str = p_ul.unfold_let("MN", "1")
    assert aconv(eq_str._concl, expected)
    # Wrong arity raises.
    try:
        p_ul.unfold_let("MN", ONE, ONE)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for unfold_let arity mismatch")
    # Missing name raises.
    try:
        p_ul.unfold_let("nope", ONE)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for unfold_let missing name")
    # fold_let is the inverse equation.
    eq_folded = p_ul.fold_let("MN", ONE)
    expected_fold = mk_eq(parse("1 + 1"), mk_comb(lz_n.carrier, ONE))
    assert aconv(eq_folded._concl, expected_fold), \
        f"fold_let: {pp(eq_folded._concl)} vs {pp(expected_fold)}"

    # ---- lazy let end-to-end smoke test --------------------------------
    # A complete @proof using a lazy let. Frame-close discharge substitutes
    # the carrier away, leaving the unfolded equivalent and no dangling hyp.
    @proof
    def LAZY_LET_END2END(p):
        p.let("MK(x) := x = x")
        p.goal("MK 1")
        p.thus("MK 1").by_eq_mp(p.fold_let("MK", ONE), REFL(ONE))
    assert LAZY_LET_END2END._asl == [], \
        f"lazy let: dangling hyp on result: {LAZY_LET_END2END._asl}"
    assert aconv(LAZY_LET_END2END._concl, parse("1 = 1")), \
        f"lazy let: unexpected concl {pp(LAZY_LET_END2END._concl)}"

    # ---- conversion-on-match smoke tests -------------------------------
    # Folded target, unfolded justification: the fallback in _finish should
    # reconcile ``MK 1`` (folded have-term) with ``|- 1 = 1`` (REFL).
    @proof
    def MATCH_FOLDED_TGT(p):
        p.let("MK(x) := x = x")
        p.goal("MK 1")
        p.thus("MK 1").by_thm(REFL(ONE))
    assert MATCH_FOLDED_TGT._asl == []
    assert aconv(MATCH_FOLDED_TGT._concl, parse("1 = 1"))

    # Unfolded target, folded justification: by_select on the carrier
    # gives folded ``MK 1``; the have-term ``1 = 1`` is unfolded. The
    # conversion-on-match in _finish lifts the theorem.
    @proof
    def MATCH_UNFOLDED_TGT(p):
        p.let("MK(x) := x = x")
        p.goal("1 = 1")
        p.have("MK_1: MK 1").by_eq_mp(p.fold_let("MK", ONE), REFL(ONE))
        p.thus("1 = 1").by_thm(p.fact("MK_1"))
    assert MATCH_UNFOLDED_TGT._asl == []
    assert aconv(MATCH_UNFOLDED_TGT._concl, parse("1 = 1"))

    # Non-terminating-rewrite guard: a (synthetic) self-referential lazy
    # let must not loop; conversion-on-match returns failure cleanly. The
    # body here is ``M y`` itself (rule ``M y -> M y`` — same size, fires
    # repeatedly until the rewriter's 256-fire guard trips). A growing
    # body (e.g. ``M y = M y``) would blow the term size up exponentially
    # before that guard fires; for an infrastructure-level loop check the
    # same-size form is sufficient.
    p_loop = Proof()
    yv = Var("y", num_ty)
    M_carrier = Var("M", mk_fun_ty(num_ty, bool_ty))
    self_ref_body = mk_comb(M_carrier, yv)               # body = M y
    eq_term_loop = mk_forall(yv,
        mk_eq(mk_comb(M_carrier, yv), self_ref_body))    # !y. M y = M y
    p_loop._cur.lazy_lets["M"] = LazyLetDef(
        "M", [yv], self_ref_body, M_carrier, ASSUME(eq_term_loop))
    th_dummy = REFL(ONE)                                 # |- 1 = 1
    target_loop = parse("M 1", _env_bindings={"M": M_carrier})
    assert p_loop._match_modulo_lazy_lets(target_loop, th_dummy) is None, \
        "self-ref lazy let: match must fail cleanly"


if __name__ == "__main__":
    _selftest()
    print("proof.py self-tests passed.")
