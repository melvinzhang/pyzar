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
    Const, Comb, Abs, thm,
    aconv, concl, HolError, ASSUME, EQ_MP, BETA, mk_comb,
    rand, type_of, TRANS,
)
from axioms import F, mk_select
from logic import (
    SPEC, GEN, DISCH, MP_LIST, DISJ_CASES, BETA_CONV, BETA_NORM, SYM,
    PROVE_HYP, ELIM_EX, _subst_term,
    NOT_INTRO, CONTR, REWRITE_NE, EXISTS, DISJ1, DISJ2,
    CONJUNCT1, CONJUNCT2,
)
from tactics import (REWRITE_PROVE, REWRITE_RULE, REWRITE_CONV, BETA_RULE,
                     AC_PROVE, REWRITE_AC_PROVE)
from parser import parse, pp, ParseError
from num import INDUCT_PROVE, mk_suc, ONE


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

class _Frame:
    __slots__ = ("goal", "kind", "vars_added", "hyps_added",
                 "facts_added", "choose_env", "type_env", "pending_choose",
                 "data", "result")

    def __init__(self, goal=None, kind="root"):
        self.goal = goal
        self.kind = kind
        self.vars_added = []      # for fix(): GEN at close
        self.hyps_added = []      # for assume(): list of (label, term); DISCH at close
        self.facts_added = []     # labels added at this frame; popped on exit
        self.choose_env = {}      # name -> witness term (parser env entries)
        self.type_env = {}        # name -> hol_type for higher-order params
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
        env = {"F": F}
        for fr in self._frames:
            for name, ty in fr.type_env.items():
                env[name] = ty
            for v in fr.vars_added:
                env[v.name] = v
            for name, term in fr.choose_env.items():
                env[name] = term
        return env

    def _set_frame_result(self, frame, th):
        """Assign `frame.result = th`, after discharging any pending choose-blocks
        on the frame (in LIFO order). The discharge replays CHOOSE_GT-style
        ELIM_EX + PROVE_HYP plumbing."""
        for ex_th, pred, hyp_ex in reversed(frame.pending_choose):
            th = PROVE_HYP(ex_th, ELIM_EX(pred, hyp_ex, lambda _: th))
        frame.pending_choose.clear()
        frame.result = th

    def _parse(self, s):
        return parse(s, _env_bindings=self._scope_env())

    _LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z_0-9]*)\s*:\s*(.+)$", re.DOTALL)

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

    def split_conj(self, ref, *labels):
        """Split a right-associated conjunction fact ``h : a /\\ b /\\ ... /\\ z``
        into the supplied labels, registering each conjunct as its own fact."""
        th = ref if isinstance(ref, thm) else self._resolve_fact(ref)
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
            if not aconv(expected, body_at_w):
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
            raise HolError(
                "have: justification produced wrong conclusion\n"
                f"  expected: {pp(self.term)}\n"
                f"  got:      {pp(concl(th))}")
        label = self.label or self.p._fresh_label("h")
        self.p._register_fact(label, th)
        if self.is_thus:
            cur = self.p._cur
            if cur.goal is None or not aconv(cur.goal, self.term):
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
        """SPEC/MP chain (if `justification` is a theorem) or a callable.

        - ``thm + args``: each arg is dispatched via MP_LIST -- a Term arg
          becomes ``SPEC``, a Theorem arg becomes ``MP``. Strings are
          interpreted as fact labels (theorem) when known, else parsed as
          terms.
        - ``callable + args``: each arg is resolved as a fact (string label,
          negative index, or theorem); the callable is invoked on them.
        """
        if isinstance(justification, thm):
            resolved = [self.p._resolve_fact_or_term(a) for a in args]
            return self._finish(MP_LIST(justification, resolved))
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

        return self._finish(build(target, fact_th))

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
        for label, term in reversed(fr.hyps_added):
            th = DISCH(term, th)
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
        forall_th = INDUCT_PROVE(self.var, self.body, d["base_th"],
                                  lambda IH: d["step_th"])
        body_th = forall_th if self.peel_forall else SPEC(self.var, forall_th)
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
    for label, term in reversed(fr.hyps_added):
        th = DISCH(term, th)
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


if __name__ == "__main__":
    _selftest()
    print("proof.py self-tests passed.")
