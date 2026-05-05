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

import contextlib
import dataclasses
import enum

from fusion import (
    Var, Comb, Abs, thm,
    HolError, ASSUME, EQ_MP, INST, type_of, TRANS, MK_COMB, ABS, REFL,
    DEDUCT_ANTISYM_RULE,
    vfree_in,
)
from basics import (
    aconv, mk_abs, mk_app, rand, rator, mk_eq, mk_fun_ty, dest_eq, dest_binop_any,
)
from axioms import (
    T, F, mk_select, mk_forall, mk_not,
    dest_disj, dest_exists, dest_forall, dest_imp, dest_neg,
    dest_conj, is_conj, is_disj,
)
from tactics import (
    SPEC, GEN, DISCH, MP, MP_LIST, DISJ_CASES, BETA_NORM, SYM,
    AP_TERM, AP_THM, PROVE_HYP, CHOOSE_WITNESS, UNFOLD, subst_term,
    NOT_INTRO, NOT_ELIM, CONTR, EXISTS, DISJ1, DISJ2,
    CONJ, CONJUNCT1, CONJUNCT2, TRANS_CHAIN,
    REWRITE_PROVE, REWRITE_CONV, REWRITE_RULE,
    AC_PROVE,
    _strip_forall, _term_match,
)
from parser import (
    parse, parse_label, parse_label_or_bare, parse_let_spec,
    parse_pattern_spec, peel_label_prefix,
    pp, ParseError, has_const,
    PatName, PatConj,
)


# ---------------------------------------------------------------------------
# Relation registry: each entry maps a relation symbol (e.g. ">", "<=") to
# a ``RelationDef`` describing its unfold target. Two kinds:
#
#   "exists" -- unfold to ``?v. body``. Consumed by ``choose``,
#               ``by_witness``, ``disj_witness``.
#   "disj"   -- unfold to ``left \/ right``. Consumed by ``cases_on``.
#
# ``by_fold`` accepts either kind and folds the equation back through
# ``SYM`` to re-introduce the relation. The ``register_unfolder`` /
# ``register_disj_unfolder`` entry points are the user-facing API; both
# route to ``_RELATIONS`` so a single ``_lookup_relation`` call can serve
# every consumer (with an optional ``kind=`` filter for shape-discriminating
# call sites).
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class RelationDef:
    op: str
    kind: str   # "exists" | "disj"
    unfold: object   # (a, b) -> |- (op a b) = body


_RELATIONS = {}   # op_name -> RelationDef


def register_relation(rel):
    """Register a binary relation's unfolder. ``rel`` is a ``RelationDef``."""
    _RELATIONS[rel.op] = rel


def register_unfolder(op_name, unfold_fn):
    """Register an existential-shape unfolder for ``op_name``:
    ``unfold_fn(a, b) -> |- (op_name a b) = (?v. body)``."""
    register_relation(RelationDef(op_name, "exists", unfold_fn))


def register_disj_unfolder(op_name, unfold_fn):
    """Register a disjunction-shape unfolder for ``op_name``:
    ``unfold_fn(a, b) -> |- (op_name a b) = (left \\/ right)``."""
    register_relation(RelationDef(op_name, "disj", unfold_fn))


# Contradiction-finder registry: each entry maps an unordered pair of
# relation-symbol names ``(rel_a, rel_b)`` to a finder
# ``finder(th_a, th_b) -> |- F`` whose inputs are facts of shape ``rel_a a b``
# and ``rel_b a b`` respectively. ``p.absurd().auto(...)`` consults this so
# call sites no longer need to name a specific contradiction lemma.

_CONTRA_FINDERS = {}

def register_contra_finder(rel_a, rel_b, finder):
    """Register ``finder(th_a, th_b) -> |- F`` for facts ``rel_a a b`` /
    ``rel_b a b``. Both orientations are stored so ``auto`` can look up
    once without swapping at the call site; the swapped entry wraps
    ``finder`` to keep its registered argument order."""
    _CONTRA_FINDERS[(rel_a, rel_b)] = finder
    if rel_a != rel_b:
        _CONTRA_FINDERS[(rel_b, rel_a)] = lambda x, y: finder(y, x)


def contra_finder(thm):
    """Decorator that registers a ``@proof``-built theorem of shape
    ``!vs. R1 a b ==> R2 a b ==> F`` as a contradiction finder.

    Reads the relation symbols from the antecedents, discovers the forall
    substitution by matching the first antecedent against the input fact,
    and auto-orients an equality second input. Stack on top of ``@proof``
    to skip the manual ``_ab_of`` / ``_orient_eq`` adapter:

        @contra_finder
        @proof
        def _CONTRA_LT_GT(p):
            p.goal("!a b. a < b ==> a > b ==> F")
            ...

    Constraint: the first antecedent must uniquely determine the foralls
    (i.e. its operands are the schematic ``a, b``). For symmetric-shape
    antecedents like ``a = b``, put the rigid relation first.
    """
    vs, body = _strip_forall(thm)
    parts = dest_imp(body._concl)
    if parts is None:
        raise HolError(
            f"contra_finder: {pp(thm._concl)} is not an implication")
    ant1, rest = parts
    parts2 = dest_imp(rest)
    if parts2 is None or not aconv(parts2[1], F):
        raise HolError(
            f"contra_finder: expected '!vs. A1 ==> A2 ==> F', got "
            f"{pp(thm._concl)}")
    ant2 = parts2[0]

    def _rel_of(t):
        c = dest_binop_any(t)
        if c is None:
            raise HolError(
                f"contra_finder: antecedent {pp(t)} is not a binary relation")
        return c[0]

    rel1 = _rel_of(ant1)
    rel2 = _rel_of(ant2)
    vars_set = set(vs)

    def adapter(th_a, th_b):
        subst = _term_match(ant1, th_a._concl, vars_set, {})
        if subst is None:
            raise HolError(
                f"contra_finder({rel1!r}, {rel2!r}): first fact "
                f"{pp(th_a._concl)} does not match {pp(ant1)}")
        if any(v not in subst for v in vs):
            raise HolError(
                f"contra_finder({rel1!r}, {rel2!r}): forall vars not "
                f"determined by first fact {pp(th_a._concl)}")
        specced = thm
        for v in vs:
            specced = SPEC(subst[v], specced)
        ant2_inst = ant2
        for v in vs:
            ant2_inst = subst_term(v, subst[v], ant2_inst)
        if aconv(th_b._concl, ant2_inst):
            th_b_use = th_b
        elif rel2 == "=":
            l_exp, r_exp = dest_eq(ant2_inst)
            l_got, r_got = dest_eq(th_b._concl)
            if aconv(l_got, r_exp) and aconv(r_got, l_exp):
                th_b_use = SYM(th_b)
            else:
                raise HolError(
                    f"contra_finder({rel1!r}, {rel2!r}): equality "
                    f"{pp(th_b._concl)} does not relate "
                    f"{pp(l_exp)} and {pp(r_exp)}")
        else:
            raise HolError(
                f"contra_finder({rel1!r}, {rel2!r}): second fact "
                f"{pp(th_b._concl)} does not match expected {pp(ant2_inst)}")
        return MP(MP(specced, th_a), th_b_use)

    register_contra_finder(rel1, rel2, adapter)
    return thm


# ---------------------------------------------------------------------------
# Induction strategy registry: each entry maps a hol_type to an
# ``InductionStrategy`` describing the base term, the successor function,
# and the kernel induction principle. ``num.py`` registers the natural-
# number strategy at import time; other domains (lists, trees, ...) can
# register their own without touching ``proof.py``. This breaks the
# old circular ``proof <-> num`` dependency: ``proof.py`` no longer
# names ``num`` at all.
# ---------------------------------------------------------------------------

class InductionStrategy:
    """How to do induction on a single ``hol_type``.

    * ``ty``          : the type whose vars this strategy applies to.
    * ``base_term``   : closed term of type ``ty`` that the base case
                         substitutes for the induction var.
    * ``succ_fn``     : ``term -> term``; the successor used in the
                         step case (e.g. ``v -> SUC v``).
    * ``induct_prove``: ``(var, body, base_th, step_fn) -> thm`` — the
                         kernel principle. Receives the base proof and a
                         function that, given the IH theorem, returns
                         the step proof; produces ``|- !var. body``.
    """
    __slots__ = ("ty", "base_term", "succ_fn", "induct_prove")

    def __init__(self, ty, base_term, succ_fn, induct_prove):
        self.ty = ty
        self.base_term = base_term
        self.succ_fn = succ_fn
        self.induct_prove = induct_prove


_INDUCTION_STRATEGIES = {}   # hol_type -> InductionStrategy

def register_induction(strategy):
    """Plugins call this once at import time to teach ``p.induction(v)``
    how to handle a new type. Re-registering the same type overrides
    (so test code can install fakes)."""
    _INDUCTION_STRATEGIES[strategy.ty] = strategy


def _lookup_relation(term, kind=None):
    """If ``term`` is ``op a b`` for a registered relation that matches
    the optional ``kind`` filter (``"exists"`` / ``"disj"``), return the
    unfolding equation ``|- (op a b) = body``; else ``None``. Single
    classify-then-apply path for every consumer of ``_RELATIONS``."""
    parts = dest_binop_any(term)
    if parts is None:
        return None
    op_name, a, b = parts
    rel = _RELATIONS.get(op_name)
    if rel is None or (kind is not None and rel.kind != kind):
        return None
    return rel.unfold(a, b)


# ---------------------------------------------------------------------------
# Assume-pattern dispatch registry.
#
# Each ``Proof.assume`` spec is parsed (by ``parser.parse_pattern_spec``)
# into a tree of ``PatName`` / ``PatConj`` nodes describing how to
# destructure the antecedent into named facts. Each top-level spec
# consumes one ``==>``; the pattern drives further structural
# decomposition of the consumed antecedent (conjunction split, etc).
#
# ``_PATTERN_HANDLERS`` maps a pattern node type to a handler
# ``(p, pat, th) -> None`` that registers the appropriate facts for
# ``th`` (a theorem whose conclusion has the shape the pattern expects).
# Plugins add new pattern kinds by extending the lark grammar in
# ``parser.py`` (the ``pattern`` rule + a visitor method) and
# registering a handler here -- e.g. an existential-witness pattern,
# an iff-split pattern, or a disjunction case-split pattern.
# ---------------------------------------------------------------------------

_PATTERN_HANDLERS = {}   # pattern type -> (p, pat, th) -> None


def register_pattern_handler(pat_type, handler):
    """Plugins call this at import time to teach ``Proof.assume`` how
    to register facts for a new pattern node type. ``handler(p, pat, th)``
    is invoked with the active ``Proof``, the pattern node, and a
    kernel theorem whose conclusion is the term the pattern destructures.
    Re-registering the same type overrides."""
    _PATTERN_HANDLERS[pat_type] = handler


def _apply_pattern(p, pat, th):
    """Dispatch ``pat`` on ``th`` to register the corresponding facts."""
    handler = _PATTERN_HANDLERS.get(type(pat))
    if handler is None:
        raise HolError(
            f"assume: no handler for pattern type {type(pat).__name__}")
    handler(p, pat, th)


def _handle_name_pattern(p, pat, th):
    label = pat.label if pat.label is not None else p._fresh_label("h")
    p._register_fact(label, th)


def _handle_conj_pattern(p, pat, th):
    # Simp-normalize so a folded carrier whose unfolded form is a
    # conjunction (e.g. ``Q args := A /\\ B``) still exposes the top
    # ``/\\`` to CONJUNCT1/CONJUNCT2.
    th = p.simp_norm_fact(th)
    n = len(pat.parts)
    cur = th
    for i, sub in enumerate(pat.parts):
        if i == n - 1:
            _apply_pattern(p, sub, cur)
        else:
            if not is_conj(cur._concl):
                raise HolError(
                    f"assume: pattern expects conjunction, got "
                    f"{pp(cur._concl)}")
            _apply_pattern(p, sub, CONJUNCT1(cur))
            cur = CONJUNCT2(cur)


register_pattern_handler(PatName, _handle_name_pattern)
register_pattern_handler(PatConj, _handle_conj_pattern)


def _pattern_primary_label(pat):
    """First named label found in ``pat`` (left-to-right). Used as the
    informational label on the ``_AssumeHyp`` record; ``DISCH`` at frame
    close uses ``asm._concl``, not the label, so any name suffices."""
    if isinstance(pat, PatName):
        return pat.label
    if isinstance(pat, PatConj):
        for sub in pat.parts:
            lbl = _pattern_primary_label(sub)
            if lbl is not None:
                return lbl
        return None
    return None


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


def _carrier_abs_body(lz):
    """``\\b1..bn. body`` -- the abstraction that replaces ``lz``'s
    carrier under INST."""
    abs_body = lz.body
    for bv in reversed(lz.bvars):
        abs_body = mk_abs(bv, abs_body)
    return abs_body


def _substitute_carrier(lz, th):
    """Substitute lazy-let ``lz``'s carrier with ``\\args. body`` in
    ``th`` and discharge the local-equation hypothesis. The returned
    theorem still has beta-redexes at every former carrier-application
    site; callers responsible for any conclusion BETA cleanup."""
    abs_body = _carrier_abs_body(lz)
    th_inst = INST([(abs_body, lz.carrier)], th)
    # Build the now-trivially-true equation hyp:
    # |- !b1..bn. (\b1..bn. body) b1..bn = body
    eq_th = BETA_NORM(mk_app(abs_body, *lz.bvars))
    for bv in reversed(lz.bvars):
        eq_th = GEN(bv, eq_th)
    return PROVE_HYP(eq_th, th_inst)


def _beta_norm_concl(th):
    """If ``th``'s conclusion has beta-redexes, lift through the
    normalizing equation; else return unchanged."""
    nf_eq = BETA_NORM(th._concl)
    if aconv(rand(nf_eq._concl), th._concl):
        return th
    return EQ_MP(nf_eq, th)


class FrameKind(enum.Enum):
    """Discriminator for ``_Frame``. Replaces ad-hoc string tags so
    misspellings fail loudly at the use site instead of silently never
    matching."""
    ROOT = "root"
    INDUCTION = "induction"
    IND_BASE = "ind_base"
    IND_STEP = "ind_step"
    CASES = "cases"
    CASE = "case"
    HAVE_PROOF = "have_proof"
    SUPPOSE = "suppose"

    def __str__(self):
        return self.value


@dataclasses.dataclass
class _InductionData:
    """Per-frame state for ``FrameKind.INDUCTION``. Populated by
    ``_InductionCtx.__enter__``; the ``base_th`` / ``step_th`` slots are
    filled by the corresponding sub-frames' ``on_close`` callbacks and
    consumed by ``_InductionCtx.__exit__``."""
    var: object
    body: object
    strategy: InductionStrategy
    base_th: object = None
    step_th: object = None


@dataclasses.dataclass
class _CasesData:
    """Per-frame state for ``FrameKind.CASES``. ``or_concl`` is the
    full right-associated disjunction theorem's conclusion (used by
    ``case()`` to find the matching leaf); ``branches`` is appended to
    by each ``case()``'s ``on_close`` and consumed by
    ``_CasesCtx.__exit__``."""
    or_concl: object
    branches: list = dataclasses.field(default_factory=list)


@dataclasses.dataclass
class _AssumeHyp:
    """Per-frame entry recorded by ``Proof.assume``: the user-visible
    label, the kernel ``ASSUME`` theorem, and a shape equation bridging
    the user's surface term to the goal's antecedent.

    ``_discharge_lazy_lets`` mutates ``asm`` and ``term_eq_ant`` in place
    when a lazy let goes out of scope; ``_close_frame`` later DISCHes
    them in the original registration order.
    """
    label: str
    asm: object
    term_eq_ant: object


class _Frame:
    __slots__ = ("goal", "kind", "vars_added", "hyps_added",
                 "facts_added", "choose_env", "type_env",
                 "lazy_lets", "simp_rules", "data", "result")

    def __init__(self, goal=None, kind=FrameKind.ROOT):
        self.goal = goal
        self.kind = kind
        self.vars_added = []      # for fix(): GEN at close
        self.hyps_added = []      # list of _AssumeHyp; DISCH'd at close
        self.facts_added = []     # labels added at this frame; popped on exit
        self.choose_env = {}      # name -> witness term (parser env entries)
        self.type_env = {}        # name -> hol_type for higher-order params
        self.lazy_lets = {}       # name -> LazyLetDef (Isabelle-style local equation)
        self.simp_rules = []      # list of theorems used as default rewrite rules
        self.data = None          # _InductionData / _CasesData (kind-specific)
        self.result = None        # the theorem proving `goal`


# ---------------------------------------------------------------------------
# Proof object: stack of frames + name->thm registry.
# ---------------------------------------------------------------------------

class Proof:
    def __init__(self):
        self._frames = [_Frame(kind=FrameKind.ROOT)]
        self._facts = {}          # label -> thm
        self._anon = 0

    @property
    def _cur(self):
        return self._frames[-1]

    # ---- env / parsing ---------------------------------------------------

    def _namespace_kind(self, name):
        """Return a label describing where ``name`` is already registered
        as a Proof-level identifier, or ``None`` if it is free.

        Covers the four namespaces that resolve a string at lookup time
        to *different kernel values*: fact labels, lazy-let carriers,
        choose witnesses, and fixed vars. The H9 fix refuses any
        registration that would put two different values under one name
        so ``coerce`` calls have an unambiguous source.

        ``type_env`` is intentionally excluded: it carries variable-type
        declarations (a pre-fix hint about what *type* a later ``fix``
        or parsed-binder occurrence of the name should have), not a
        separate kernel value. Realising the name via ``fix`` -- which
        consumes the same hint -- is consistent, not a collision.
        """
        if name in self._facts:
            return "fact label"
        for fr in self._frames:
            if name in fr.lazy_lets:
                return "lazy-let binding"
            if name in fr.choose_env:
                return "choose witness"
            for v in fr.vars_added:
                if v.name == name:
                    return "fixed variable"
        return None

    def _require_fresh_name(self, name, registering_as):
        existing = self._namespace_kind(name)
        if existing is not None:
            raise HolError(
                f"{registering_as}: name {name!r} clashes with an "
                f"existing {existing}")

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

    def _lazy_let_carriers(self):
        """Map every in-scope lazy-let carrier ``Var`` to its ``LazyLetDef``."""
        out = {}
        for fr in self._frames:
            for lz in fr.lazy_lets.values():
                out[lz.carrier] = lz
        return out

    def _active_simp_rules(self):
        """Theorems registered via ``p.simp(...)`` in any open frame, in
        registration order (outer frames first, innermost last). Consumed
        by ``by_rewrite`` / ``by_rewrite_of`` / ``disj`` / ``disj_witness``
        as a default extension to the user's rule list."""
        out = []
        for fr in self._frames:
            out.extend(fr.simp_rules)
        return out

    def simp(self, *rules):
        """Register one or more theorems as default rewrite rules in the
        current frame. Each rule is a fact label or theorem; rules are
        added to the active simp set in order and used
        by every subsequent ``by_rewrite``-family / ``disj``-family call
        in this frame and any nested frame.

        Modeled after Isabelle's ``[simp]``: rules added here are applied
        silently in addition to any user-supplied rule list. Frame-local
        scoping means a sub-block can extend the simp set without
        affecting the surrounding proof.
        """
        for r in rules:
            self._cur.simp_rules.append(self.coerce(r))

    def simp_normalize(self, tm, carriers=None):
        """Fixpoint simp pass over ``tm`` against the active simp set
        (currently: lazy-let local equations), returning ``|- tm = tm_norm``.

        Walks bottom-up; each carrier application fires its rule, and the
        substituted body is re-walked so nested carriers also normalize.
        Self-reference is bounded by a per-descent ``blocked`` set so a let
        whose body mentions itself unfolds once and stops.

        Bypasses ``REWRITE_CONV``'s "no hyp-bearing rules under binders"
        filter — sound because lazy-let equation hyps are
        ``!args. carrier args = body``; ``ABS`` normally succeeds under
        binders (bvar isn't free in the hyp), and ``_unfold_walk`` falls
        back to ``REFL`` for the rare case where it can't.

        Real kernel errors raised inside ``_unfold_walk`` propagate
        unchanged — only ``SimpFailure`` signals "simp gave up cleanly".
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
            # ``ABS`` fails if ``tm.bvar`` is free in some hyp of ``body_eq``.
            # That's a legitimate "can't lift this rewrite under the binder"
            # signal, not a bug -- fall back to no-progress at this node and
            # let the caller see the un-normalized lambda. Check the
            # precondition explicitly rather than catching the kernel
            # ``HolError``, which would also mask signature / non-equation
            # bugs (the kernel returns the same error for all three).
            if any(vfree_in(tm.bvar, h) for h in body_eq._asl):
                return REFL(tm)
            return ABS(tm.bvar, body_eq)
        if isinstance(tm, Comb):
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
            f_eq = self._unfold_walk(tm.fun, carriers, blocked)
            a_eq = self._unfold_walk(tm.arg, carriers, blocked)
            if (aconv(rand(f_eq._concl), tm.fun)
                    and aconv(rand(a_eq._concl), tm.arg)):
                return REFL(tm)
            return MK_COMB(f_eq, a_eq)
        return REFL(tm)

    def simp_norm_fact(self, th):
        """Simp-normalize ``th``'s conclusion, returning a theorem whose
        conclusion is the normal form. Pattern B: structural exposure —
        used by tactics that need the unfolded shape (``by`` before SPEC
        chains, conjunction-pattern dispatch to expose the top ``/\\``,
        ``by_disj`` to expose the disjunction)."""
        eq = self.simp_normalize(th._concl)
        if aconv(rand(eq._concl), th._concl):
            return th
        return EQ_MP(eq, th)

    def simp_aconv(self, t1, t2):
        """Term-level analogue of ``aconv`` modulo the active simp set.

        Two terms are simp-equivalent iff their bottom-up unfolds (via the
        lazy-let carriers and globally-registered ``define`` rules)
        produce alpha-equivalent normal forms. Used by tactics that
        compare a user-supplied term against a frame-stored canonical
        form which was already simp-normalized at frame entry (e.g.
        ``suppose``, ``by_contradiction``)."""
        if aconv(t1, t2):
            return True
        eq1 = self.simp_normalize(t1)
        eq2 = self.simp_normalize(t2)
        return aconv(rand(eq1._concl), rand(eq2._concl))

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
        return _beta_norm_concl(_substitute_carrier(lz, th))

    def simp_mp(self, th_imp, th_arg):
        """``MP(th_imp, th_arg)`` modulo simp on the antecedent.

        If the antecedent and ``th_arg``'s conclusion don't ``aconv``
        directly, lift via ``simp_match`` so the user can mix folded /
        unfolded forms across an MP boundary."""
        parts = dest_imp(th_imp._concl)
        if parts is None:
            return MP(th_imp, th_arg)
        ant, _ = parts
        return MP(th_imp, self._simp_require(ant, th_arg, op="MP"))

    def simp_match(self, target, th):
        """If ``aconv(target, th._concl)`` fails, try to align them by
        simp-normalizing both terms.

        Uses the under-binder-tolerant ``simp_normalize`` rather than the
        engine's ``REWRITE_CONV``, which would refuse to descend under
        binders for hyp-bearing rules.

        Returns ``th'`` with ``aconv(concl(th'), target)`` on success,
        else ``None``."""
        carriers = self._lazy_let_carriers()
        if not carriers:
            return th if aconv(target, th._concl) else None
        target_eq = self.simp_normalize(target, carriers)
        th_eq = self.simp_normalize(th._concl, carriers)
        if not aconv(rand(target_eq._concl), rand(th_eq._concl)):
            return None
        th_at_nf = EQ_MP(th_eq, th)
        return EQ_MP(SYM(target_eq), th_at_nf)

    def simp_eq_mp(self, eq_th, fact_th):
        """``EQ_MP(eq_th, fact_th)`` modulo simp on the LHS of ``eq_th``.

        Aligns the equation's LHS with the fact's conclusion via simp on
        the active simp set, so callers can mix folded/unfolded forms
        across an EQ_MP boundary."""
        try:
            lhs, _ = dest_eq(eq_th._concl)
        except HolError:
            return EQ_MP(eq_th, fact_th)
        lifted = self.simp_match(lhs, fact_th)
        if lifted is not None:
            fact_th = lifted
        return EQ_MP(eq_th, fact_th)

    def _simp_require(self, target, th, op):
        """Return ``th`` lifted to shape ``target`` via ``simp_match``, or
        raise ``HolError`` with a uniform shape-mismatch message."""
        if aconv(target, th._concl):
            return th
        lifted = self.simp_match(target, th)
        if lifted is not None:
            return lifted
        raise HolError(
            f"{op}: shape does not match\n"
            f"  expected: {pp(target)}\n"
            f"  got:      {pp(th._concl)}")

    def _apply_chain(self, justification, args, *, simp, op):
        """Drive the ``thm | callable | fact-ref`` dispatch shared by
        ``_Have.by`` and ``_Absurd.by``.

        - ``str``/``int`` ``justification`` is resolved via ``coerce``.
        - ``thm``: walk ``args`` left-to-right, dispatching ``term -> SPEC``,
          ``thm -> MP``. With ``simp=True``, the head is ``simp_norm_fact``-ed
          and each MP goes through ``simp_mp`` (folded/unfolded bridging);
          with ``simp=False``, the chain is the literal ``MP_LIST`` shape.
        - ``callable``: invoked on the resolved args (each via ``coerce``
          with ``accept_term=True``).
        - anything else raises with an ``op``-prefixed message.
        """
        if isinstance(justification, str):
            justification = self.coerce(justification)
        if isinstance(justification, thm):
            th = self.simp_norm_fact(justification) if simp else justification
            for a in args:
                resolved = self.coerce(a, accept_term=True)
                if isinstance(resolved, thm):
                    th = self.simp_mp(th, resolved) if simp else MP(th, resolved)
                else:
                    th = SPEC(resolved, th)
            return th
        if callable(justification):
            resolved = [self.coerce(a, accept_term=True) for a in args]
            return justification(*resolved)
        raise HolError(
            f"{op}: not a theorem or callable: {justification!r}")

    def _close_frame(self, fr, th):
        """Discharge a frame's accumulated bindings into ``th``.

        For each saved hyp, ``DISCH(asm._concl, th)`` produces
        ``... |- term ==> consequent`` (with ``term`` being the user's
        surface form). The accompanying ``term_eq_ant`` (``|- term =
        ant``) is lifted to an implication equation
        ``|- (term ==> consequent) = (ant ==> consequent)`` via
        ``MK_COMB(AP_TERM(==>, term_eq_ant), REFL(consequent))``, then
        ``EQ_MP`` rewrites the antecedent to the goal's kernel form. So
        the user always sees their surface form via ``p.fact(label)``,
        and the closed theorem matches the original goal exactly.

        ``hyps_added`` stores the registered ``ASSUME`` theorems and
        their shape equations; ``_discharge_lazy_lets`` INSTs both in
        lockstep with ``th``, so ``DISCH`` / lazy-let-discharge order
        does not affect correctness. ``GEN`` still has to come last
        (its ``ABS`` step fails if a fix-var is free in any remaining
        hyp).

        Induction's frame has empty ``hyps_added`` / ``vars_added``
        (the ``GEN`` happens earlier via ``INDUCT_PROVE``), so for
        that caller this collapses to ``_discharge_lazy_lets``.
        """
        for h in reversed(fr.hyps_added):
            th = DISCH(h.asm._concl, th)
            consequent = rand(th._concl)
            imp_eq_const = rator(rator(th._concl))   # the (==>) const
            imp_eq = MK_COMB(AP_TERM(imp_eq_const, h.term_eq_ant),
                             REFL(consequent))
            th = EQ_MP(imp_eq, th)
        th = self._discharge_lazy_lets(fr, th)
        th = _beta_norm_concl(th)
        for v in reversed(fr.vars_added):
            th = GEN(v, th)
        return th

    def _discharge_lazy_lets(self, frame, th):
        """Discharge each lazy-let hypothesis on ``th`` from ``frame``.

        For every lazy let ``R(b1...bn) := body`` registered on
        ``frame``, substitute ``R := \\b1...bn. body`` and ``PROVE_HYP``
        the resulting (now trivially provable) equation hypothesis. The
        same substitution is applied to every ``ASSUME`` saved in
        ``frame.hyps_added``, so each saved hyp's ``_concl`` tracks
        ``th._asl`` through the discharge — this is what lets
        ``_close_frame`` swap discharge / DISCH order without changing
        the result.

        Lazy lets registered on parent frames are *not* discharged here —
        they go out with the corresponding parent frame.

        Reverse registration order matters: a later let's body may
        reference an earlier carrier, so discharging the earlier one
        first would mutate the later let's hyp shape away from what
        ``_substitute_carrier`` synthesises from ``lz.body``.
        """
        if not frame.lazy_lets:
            return th
        for lz in reversed(list(frame.lazy_lets.values())):
            th = _substitute_carrier(lz, th)
            # Sync saved ASSUMEs and shape equations in lockstep.
            #   * Plain INST on each ASSUME: keeps its _concl matching
            #     th._asl. _substitute_carrier would risk discharging
            #     the user's own hyp if they literally assumed the
            #     lazy-let equation.
            #   * _substitute_carrier on each shape equation: it carries
            #     the lazy-let equation hyp internally, so we want it
            #     discharged the same way as in th.
            sub = (_carrier_abs_body(lz), lz.carrier)
            for h in frame.hyps_added:
                h.asm = INST([sub], h.asm)
                h.term_eq_ant = _substitute_carrier(lz, h.term_eq_ant)
        return _beta_norm_concl(th)

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
        self._require_fresh_name(name, "register_lazy_let")
        ty = type_of(body)
        for bv in reversed(bvars):
            ty = mk_fun_ty(bv.ty, ty)
        carrier = Var(name, ty)
        eq_term = mk_eq(mk_app(carrier, *bvars), body)
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

    def _split_label(self, spec):
        """Parse ``"label: term"`` or ``"term"`` or ``"label:"``.

        Thin wrapper over ``parser.parse_label`` that supplies the
        current scope env. The grammar commits once it sees ``NAME ":"``
        so a body-level ``ParseError`` reports the typo the user
        actually wrote (no misleading whole-spec retry).

        The trailing-colon form ``"label:"`` (no body) is the
        inferred-conclusion variant: the resulting ``_Have`` has
        ``term=None``, so ``_finish`` skips the shape check and
        registers the justifier's output at its native conclusion.
        """
        peeled = peel_label_prefix(spec)
        if peeled is not None and not peeled[1].strip():
            return peeled[0], None
        return parse_label(spec, _env_bindings=self._scope_env())

    def _fresh_label(self, prefix="h"):
        while True:
            self._anon += 1
            name = f"_{prefix}{self._anon}"
            if name not in self._facts:
                return name

    def _parse_label_or_check(self, label_spec, expected, op):
        """Resolve a ``"label"`` or ``"label: term"`` spec for tactics that
        already know the expected hypothesis (``suppose`` / ``by_contradiction``).

        A bare label short-circuits with no body check. An explicit
        ``"label: term"`` spec has its body simp-aconv-checked against
        ``expected``. Raises ``HolError`` with ``op``-prefixed messages
        on any failure. Returns the resolved label.
        """
        try:
            label, hyp_term = parse_label_or_bare(
                label_spec, _env_bindings=self._scope_env())
        except ParseError as ex:
            raise HolError(f"{op}: cannot parse label spec: {ex}") from ex
        if hyp_term is None:
            return label
        if not self.simp_aconv(hyp_term, expected):
            raise HolError(
                f"{op}: hypothesis does not match expected\n"
                f"  expected: {pp(expected)}\n"
                f"  given:    {pp(hyp_term)}")
        return label

    # ---- facts -----------------------------------------------------------

    def _register_fact(self, label, th):
        self._require_fresh_name(label, "register_fact")
        self._facts[label] = th
        self._cur.facts_added.append(label)

    def _drop_facts(self, labels):
        for label in labels:
            if label not in self._facts:
                raise HolError(
                    f"_drop_facts: {label!r} not in fact registry "
                    "(facts_added must stay a subset of _facts)")
            del self._facts[label]

    def coerce(self, x, *, accept_term=False):
        """Resolve ``x`` to a theorem -- or, when ``accept_term`` is true,
        to a kernel term as a fallback.

        Always-fact (``accept_term=False``, default):
          - ``thm`` -- returned unchanged.
          - ``str`` -- looked up as a fact label; an unknown label raises.
          - kernel term object -- rejected.

        Fact-or-term (``accept_term=True``): same as above, plus:
          - ``str`` not in the fact table -- parsed as a term in the
            current scope.
          - kernel term object -- returned as-is.

        Used by tactics that take a single named theorem ref (``simp``,
        ``by_rewrite_of``, ``cases_on``, ...) in the default mode, and
        by variadic-arg tactics (``_Have.by``, ``by_match``,
        ``cases_on``'s extra ``*args``) in fact-or-term mode where
        positional args may mix theorem refs and specialization terms.
        """
        if isinstance(x, thm):
            return x
        if isinstance(x, str):
            if x in self._facts:
                return self._facts[x]
            if accept_term:
                return self._parse(x)
            raise HolError(f"unknown fact label: {x!r}")
        if accept_term:
            return x
        raise HolError(f"coerce: cannot resolve reference: {x!r}")

    def fact(self, ref):
        """Public accessor: returns the theorem associated with a label or index."""
        return self.coerce(ref)

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
            pred = dest_forall(g)
            if pred is None:
                raise HolError(f"fix({nm!r}): goal is not a forall: {pp(g)}")
            if pred.bvar.name != nm:
                raise HolError(
                    f"fix: name mismatch -- binder is {pred.bvar.name!r}, given {nm!r}")
            self._require_fresh_name(nm, "fix")
            self._cur.goal = pred.body
            self._cur.vars_added.append(pred.bvar)

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
        types = types or {}

        # Build the body-parsing env first so the parser sees user-supplied
        # type aliases (consulted by ``var_decl`` for ``arg:T`` annotations
        # *and* for body free-names that need a declared type).
        env = self._scope_env()
        body_env = dict(env)
        for nm, ty in types.items():
            body_env[nm] = ty
        try:
            name, bvars, body = parse_let_spec(spec, _env_bindings=body_env)
        except ParseError as ex:
            raise HolError(
                f"let: expected 'NAME(arg1, arg2, ...) := body' "
                f"(args may be annotated 'arg:ty'); {ex}") from ex

        seen = set()
        for v in bvars:
            if v.name in seen:
                raise HolError(
                    f"let: duplicate arg name {v.name!r} in {spec!r}")
            seen.add(v.name)

        if has_const(name):
            raise HolError(
                f"let: {name!r} clashes with a registered constant")

        self._register_lazy_let(name, bvars, body)

    def split(self, ref, spec):
        """Destructure an existing fact via the pattern grammar shared with
        ``assume``.

        ``ref`` resolves through ``coerce`` (label, index, or theorem).
        ``spec`` is a pattern -- optionally annotated ``: term`` --
        using the same grammar as an ``assume`` spec body. The pattern
        is dispatched on ``ref``'s conclusion through the registry that
        ``assume`` uses, so any pattern kind installed via
        ``register_pattern_handler`` works here too. Examples::

            p.split("h", "(h1, h2)")            # split a conjunction
            p.split("h", "(h1, _, h3)")         # discard middle conjunct
            p.split(-1, "(h1, (h2, h3))")       # nested destructure

        If the optional ``: term`` is supplied, ``term`` is
        simp-equivalence-checked against ``ref``'s conclusion (as in
        ``assume``).
        """
        th = self.coerce(ref)
        try:
            pattern, body_term = parse_pattern_spec(
                spec, _env_bindings=self._scope_env())
        except ParseError as ex:
            raise HolError(
                f"split: cannot parse spec {spec!r}: {ex}") from ex
        if body_term is not None:
            self._derive_shape_eq(body_term, th._concl, op="split")
        _apply_pattern(self, pattern, th)

    def assume(self, *specs):
        """Consume the goal's antecedent(s) into facts via pattern destructuring.

        Each spec consumes one ``==>`` from the current goal. The spec's
        pattern then destructures the consumed antecedent into named
        facts. Patterns:

        * ``label`` / ``label: term`` -- atomic: register the antecedent
          as fact ``label``. ``_`` for an anonymous label. ``term`` (when
          given) is simp-equivalence-checked against the goal antecedent
          and preserves the user's surface form across frame close.
        * ``(p1, p2, ..., pn)`` / ``(p1, p2, ..., pn): term`` -- split a
          right-associated conjunction antecedent into ``n`` parts,
          recursively applying each sub-pattern. Sub-patterns may
          themselves be tuples (nested destructure) or names.

        Examples::

            p.assume("h: A")                              # chain, one ==>
            p.assume("h1: A", "h2: B")                    # chain, two ==>s
            p.assume("(h1, h2): A /\\ B")                 # split: h1: A, h2: B
            p.assume("(h1, _, h3): A /\\ B /\\ C")        # discard middle conjunct

        New pattern kinds (existential witness, iff-split, ...) plug in
        via ``register_pattern_handler``; see the assume-pattern AST
        block at the top of this module.
        """
        for spec in specs:
            try:
                pattern, body_term = parse_pattern_spec(
                    spec, _env_bindings=self._scope_env())
            except ParseError as ex:
                raise HolError(
                    f"assume: cannot parse spec {spec!r}: {ex}") from ex
            g = self._cur.goal
            parts = dest_imp(g)
            if parts is None:
                raise HolError(f"assume: goal is not an implication: {pp(g)}")
            ant, cons = parts
            term = body_term if body_term is not None else ant
            # Register the user's surface-form ASSUME so its conclusion
            # matches what they wrote. ``term_eq_ant : |- term = ant``
            # bridges the surface form (which may be folded while ``ant``
            # is unfolded, or vice versa) to the kernel-form antecedent at
            # frame close, so the resulting implication has the goal's
            # original shape. The shape equation also serves as the
            # simp-equivalence check: ``_derive_shape_eq`` raises if the
            # user's term and the goal's antecedent don't normalize to
            # the same shape.
            self._cur.goal = cons
            asm_th = ASSUME(term)
            term_eq_ant = self._derive_shape_eq(term, ant, op="assume")
            primary = _pattern_primary_label(pattern) or self._fresh_label("h")
            self._cur.hyps_added.append(_AssumeHyp(primary, asm_th, term_eq_ant))
            _apply_pattern(self, pattern, asm_th)

    def _derive_shape_eq(self, lhs, rhs, op="_derive_shape_eq"):
        """``|- lhs = rhs`` for two simp-equivalent terms. ``REFL`` when
        they're already kernel-aconv; otherwise composed from the two
        ``simp_normalize`` equations through the shared normal form.

        Raises ``HolError`` (prefixed with ``op``) if the two terms are
        not simp-equivalent, so callers can use this both as a shape
        bridge and as a simp-equivalence check in one step.
        """
        if aconv(lhs, rhs):
            return REFL(lhs)
        lhs_eq = self.simp_normalize(lhs)
        rhs_eq = self.simp_normalize(rhs)
        if not aconv(rand(lhs_eq._concl), rand(rhs_eq._concl)):
            raise HolError(
                f"{op}: shape does not match\n"
                f"  expected: {pp(rhs)}\n"
                f"  got:      {pp(lhs)}")
        return TRANS(lhs_eq, SYM(rhs_eq))

    # ---- have / thus -----------------------------------------------------

    def have(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=False)

    def thus(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=True)

    def calc(self, lhs_spec, *, thus=False):
        """Open an equational-chain context (Mizar-style ``... .= ...``).

        ``lhs_spec`` is ``"lhs"`` or ``"label: lhs"``. Inside the
        ``with``, each ``c.step("= rhs").by(...)`` proves
        ``cur_rhs = rhs`` and TRANS-composes it onto the running chain;
        ``cur_rhs`` starts at ``lhs`` and advances after each step. On
        exit the composed equation ``lhs = final_rhs`` is registered as
        a fact (under ``label`` or an anonymous name).

        With ``thus=True``, the composed equation must alpha-match the
        current goal and discharges it (mirrors ``thus`` vs. ``have``).

        Each ``_CalcStep`` is a ``_Have`` subclass, so every ``by_*``
        justification (``by``, ``by_thm``, ``by_rewrite``,
        ``by_rewrite_of``, ``by_match``, ``by_ac``, ``proof()``, ...)
        works on a step.
        """
        label, lhs_term = self._split_label(lhs_spec)
        return _CalcCtx(self, label, lhs_term, thus_mode=thus)

    # ---- block constructs ------------------------------------------------

    def induction(self, var_name):
        body = self._cur.goal
        if body is None:
            raise HolError("induction: no current goal")
        # If the goal is ``!var_name. inner``, peel the binder automatically
        # so the user doesn't need an intermediate fix() call.
        pred = dest_forall(body)
        if pred is not None and pred.bvar.name == var_name:
            var, inner_body, peel = pred.bvar, pred.body, True
        else:
            env = self._scope_env()
            if var_name not in env:
                raise HolError(f"induction: unknown variable {var_name!r}")
            var, inner_body, peel = env[var_name], body, False
        strategy = _INDUCTION_STRATEGIES.get(var.ty)
        if strategy is None:
            raise HolError(
                f"induction: no strategy registered for type {var.ty!r}")
        return _InductionCtx(self, var, inner_body, strategy,
                              peel_forall=peel)

    def base(self):
        fr = self._cur
        if fr.kind != FrameKind.INDUCTION:
            raise HolError("base() outside induction()")
        d = fr.data
        sub_goal = subst_term(d.var, d.strategy.base_term, d.body)

        def on_close(th):
            d.base_th = th

        return _SubFrameCtx(self, sub_goal, kind=FrameKind.IND_BASE,
                             on_close=on_close)

    def step(self, ih_label):
        """Open the inductive-step sub-block.

        ``ih_label`` (required) is the name under which the induction
        hypothesis is registered as a fact for the duration of the
        block. The label is written explicitly at every call site so
        the binding is visible at the block opener -- mirroring the
        ``with p.case("..."):`` pattern -- and so nested inductions
        must pick distinct labels rather than silently colliding on a
        shared default.
        """
        fr = self._cur
        if fr.kind != FrameKind.INDUCTION:
            raise HolError("step() outside induction()")
        d = fr.data
        sub_goal = subst_term(d.var, d.strategy.succ_fn(d.var), d.body)

        def on_close(th):
            d.step_th = th

        return _SubFrameCtx(self, sub_goal, kind=FrameKind.IND_STEP,
                             on_close=on_close,
                             extra_facts=[(ih_label, ASSUME(d.body))])

    def choose(self, name_spec, from_, eq_label=None):
        """Eliminate an existential, bringing a witness into scope.

        ``name_spec``: ``"name"`` (or whitespace-separated ``"n1 n2 ..."`` to
            peel multiple binders in one step), optionally followed by
            ``": equation"`` to verify the final body. With multiple names,
            the source is peeled once per name; only the outer level may be
            an order-relation auto-unfold.
        ``from_``: label of the source fact, which must be ``?v. body``,
            or ``x > y``, or ``x < y`` (auto-unfolded).
        ``eq_label``: label under which to register the equation fact;
            defaults to ``f"{last_name}_eq"`` so it doesn't clash with the
            witness names (which live in the parser env).
        """
        peeled = peel_label_prefix(name_spec)
        if peeled is not None:
            name, eq_check = peeled
        else:
            name = name_spec.strip()
            eq_check = None

        names = name.split()
        if not names:
            raise HolError("choose: empty name spec")

        src_th = self.coerce(from_)
        # If src is a relation registered with an existential unfolder,
        # unfold first.
        unfold_eq = _lookup_relation(src_th._concl, kind="exists")
        cur_th = EQ_MP(unfold_eq, src_th) if unfold_eq is not None else src_th

        for nm in names:
            pred = dest_exists(cur_th._concl)
            if pred is None:
                raise HolError(
                    f"choose: source {from_!r} is not an existential or order relation: "
                    f"{pp(cur_th._concl)}")
            v_var = pred.bvar
            w_term = mk_select(v_var, pred.body)
            # SELECT_AX-derive the witness fact directly. The registered
            # theorem's _asl mirrors the source's, so the user's proof
            # accumulates the source's hyps rather than a free-floating
            # ASSUME that would have to be reconciled at frame close.
            cur_th = CHOOSE_WITNESS(pred, cur_th)
            self._require_fresh_name(nm, "choose")
            self._cur.choose_env[nm] = w_term

        if eq_check is not None:
            env = self._scope_env()
            try:
                expected = parse(eq_check, _env_bindings=env)
            except ParseError as ex:
                raise HolError(f"choose: cannot parse equation spec: {ex}") from ex
            # Simp-aware match: user may have written a folded shape whose
            # unfolded form equals the witness body (or vice versa).
            if self.simp_match(expected, cur_th) is None:
                raise HolError(
                    "choose: equation spec doesn't match witness body\n"
                    f"  expected: {pp(cur_th._concl)}\n"
                    f"  given:    {pp(expected)}")

        # Register the equation as a fact (default label = "{last_name}_eq").
        eq_label = eq_label or f"{names[-1]}_eq"
        self._register_fact(eq_label, cur_th)

    def _build_disj(self, target, match, op):
        """Walk ``target``'s right-associated disjunction.

        For each leaf (and the disjunction itself), call ``match(leaf)``;
        it returns either a theorem of ``leaf`` or ``None``. First success
        is ``DISJ1``/``DISJ2``-chained back into the full disjunction and
        simp-lifted to ``target``'s original shape. Raises ``HolError``
        when no leaf can be discharged. Shared by ``_close_disj`` (which
        operates on the current frame's goal and writes ``fr.result``) and
        ``_Have.by_disj`` (which operates on the have-term and feeds the
        result through ``_finish``).
        """
        target_eq = self.simp_normalize(target)
        target_norm = rand(target_eq._concl)

        def go(d):
            m = match(d)
            if m is not None:
                return m
            parts = dest_disj(d)
            if parts is None:
                return None
            p_part, q_part = parts
            left = go(p_part)
            if left is not None:
                return DISJ1(left, q_part)
            right = go(q_part)
            if right is not None:
                return DISJ2(p_part, right)
            return None

        th = go(target_norm)
        if th is None:
            raise HolError(
                f"{op}: no leaf discharged\n  goal: {pp(target)}")
        return self._simp_require(target, th, op=op)

    def _close_disj(self, op, match):
        """Walk the current frame's right-associated disjunction goal,
        delegating to ``_build_disj``. The first match is set as the
        frame's result. Shared between ``disj`` and ``disj_witness``."""
        fr = self._cur
        if fr.goal is None:
            raise HolError(f"{op}: no current goal")
        th = self._build_disj(fr.goal, match, op)
        self._cur.result = th
        return th

    def _make_existential(self, target, witness, body_provider):
        """Build a theorem of ``target`` from a body-proof provider.

        Recognizes ``target`` as ``?v. body[v]`` directly, or as a relation
        registered with ``register_unfolder`` whose unfolded form is
        existential. ``body_provider(body_at_w) -> thm | None`` produces a
        theorem whose conclusion is ``body[witness/v]``, or ``None`` to
        signal the body couldn't be proved (caller treats the failure as a
        non-match). Returns ``None`` when ``target`` is not an existential
        / unfoldable-to-existential relation; lets ``body_provider``'s own
        exceptions propagate for callers that want raise-on-mismatch.

        Shared by ``_Have.by_witness`` (body proof = supplied fact lifted
        via simp) and ``disj_witness`` (body proof = ``REWRITE_PROVE``).
        """
        pred = dest_exists(target)
        if pred is not None:
            body_at_w = subst_term(pred.bvar, witness, pred.body)
            body_th = body_provider(body_at_w)
            if body_th is None:
                return None
            return EXISTS(pred, witness, body_th)
        unfold_eq = _lookup_relation(target, kind="exists")
        if unfold_eq is not None:
            ex_pred = dest_exists(rand(unfold_eq._concl))
            if ex_pred is None:
                return None
            body_at_w = subst_term(ex_pred.bvar, witness, ex_pred.body)
            body_th = body_provider(body_at_w)
            if body_th is None:
                return None
            return EQ_MP(SYM(unfold_eq), EXISTS(ex_pred, witness, body_th))
        return None

    def _make_existential_multi(self, target, witnesses, body_provider):
        """Multi-witness variant of ``_make_existential``: peels one
        existential level per witness, so a target ``?v1 ... vn. P`` (or a
        registered relation whose unfold begins with that shape) becomes a
        single ``EXISTS`` chain. ``body_provider`` is invoked once with the
        innermost body ``P[w1/v1, ..., wn/vn]``. Returns ``None`` only if
        the outermost level isn't a recognized existential shape; deeper
        non-existential mismatches raise."""
        if not witnesses:
            return body_provider(target)
        w0, rest = witnesses[0], witnesses[1:]

        def inner(body_at_w0):
            inner_th = self._make_existential_multi(
                body_at_w0, rest, body_provider)
            if inner_th is None and rest:
                raise HolError(
                    "by_witness: target has fewer existential levels "
                    f"than witnesses; stuck at: {pp(body_at_w0)}")
            return inner_th

        return self._make_existential(target, w0, inner)

    def disj(self, *rules, ac=None):
        """Close the current frame's disjunction goal by discharging a leaf
        directly: a ``rule`` whose conclusion alpha-matches the leaf is
        used as-is (fact-injection); otherwise the leaf is proved via
        ``REWRITE_PROVE(rules, leaf, ac=ac)``. With no rules, collapses to
        ``REFL`` for a tautological leaf.

        Each ``rule`` is a fact label or theorem. Replaces
        ``p.thus(<disj>).by_disj(ref)`` and the ``have eq →
        by_disj`` two-step.
        """
        user_rules = [self.simp_norm_fact(self.coerce(r))
                      for r in rules]
        rules_thms = user_rules + self._active_simp_rules()

        def match(d):
            for r_th in user_rules:
                if aconv(d, r_th._concl):
                    return r_th
            try:
                return REWRITE_PROVE(rules_thms, d, ac=ac)
            except HolError:
                return None

        return self._close_disj("disj", match)

    def disj_witness(self, witness, *rules, ac=None):
        """Close the current frame's disjunction goal by witnessing an
        existential leaf.

        For each leaf that is ``?w. body[w]`` (directly, or via a
        registered unfolder for an order-style relation like ``a < b``),
        attempts to prove ``body[witness/w]`` via ``REWRITE_PROVE(rules,
        body_at_w, ac=ac)``. The first leaf that succeeds is wrapped via
        ``EXISTS`` (folding any unfolder back), then ``DISJ1``/``DISJ2``-
        chained into the full disjunction.

        ``witness`` is parsed in the current scope (so ``case``-bound
        names are available) or accepted as a kernel term. Each ``rule``
        is a fact label or theorem. Replaces the
        ``have eq → by_witness → by_disj`` quartet, and the
        relation-goal ``have eq → by_witness`` two-step when the goal
        is a single ``a R b`` leaf.
        """
        witness_t = (self._parse(witness) if isinstance(witness, str)
                     else witness)
        rules_thms = ([self.coerce(r) for r in rules]
                      + self._active_simp_rules())

        def body_provider(body_at_w):
            try:
                return REWRITE_PROVE(rules_thms, body_at_w, ac=ac)
            except HolError:
                return None

        def match(d):
            return self._make_existential(d, witness_t, body_provider)

        return self._close_disj("disj_witness", match)

    def _open_cases(self, ref, target, on_close, args=(), op="cases_on"):
        or_th = self.coerce(ref)
        if args:
            resolved = [self.coerce(a, accept_term=True) for a in args]
            or_th = MP_LIST(or_th, resolved)
        c = or_th._concl
        # If the source is a relation registered with a disjunction unfolder
        # (e.g. ``>=``, ``<=``), unfold to the disjunction first.
        unfold_eq = _lookup_relation(c, kind="disj")
        if unfold_eq is not None:
            or_th = EQ_MP(unfold_eq, or_th)
            c = or_th._concl
        # Expect (p \/ q) at the top.
        if not is_disj(c):
            raise HolError(f"{op}: not a disjunction: {pp(c)}")
        return _CasesCtx(self, or_th, target, on_close, op=op)

    def cases_on(self, ref, *args):
        """Case-split on a disjunction.

        ``ref`` is a fact label, theorem, or relation fact (``a R b`` for a
        relation registered with ``register_disj_unfolder``). Extra
        ``*args`` are ``MP_LIST``-applied to the resolved theorem (each
        string is parsed as a term, each fact label looked up) before
        the cases are taken — so
        ``cases_on(SATZ_10, "x", "y")`` is equivalent to
        ``cases_on(SPECL([x, y], SATZ_10))``, and ``cases_on("h", x_term)``
        works when ``"h"`` is a registered fact label.
        """
        parent = self._cur
        if parent.goal is None:
            raise HolError("cases_on: no current goal")
        def on_close(res):
            parent.result = res

        return self._open_cases(ref, parent.goal, on_close, args=args)

    def suppose(self, label_spec):
        """Open a hypothetical sub-block to prove a negation goal.

        The current goal must be ``~p``. The block has goal ``F`` and gets
        ``label: p`` registered as a fact. On close, wraps the F-theorem as
        ``NOT_INTRO(DISCH(p, F_th))`` and discharges the parent's ``~p`` goal.
        """
        fr = self._cur
        g = fr.goal
        body = dest_neg(g) if g is not None else None
        if body is None:
            raise HolError(
                f"suppose: current goal is not a negation: "
                f"{pp(g) if g is not None else 'None'}")

        label = self._parse_label_or_check(label_spec, body, op="suppose")

        def on_close(F_th):
            not_th = NOT_INTRO(DISCH(body, F_th))
            self._cur.result = not_th

        return _SubFrameCtx(self, F, kind=FrameKind.SUPPOSE,
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

    def _auto_choose_for_case_leaf(self, leaf, user_term):
        """If ``leaf`` is ``?v. body``, derive a witness inside the
        just-entered case sub-frame so the user gets ``v`` in scope and
        ``v_eq: body[v]`` as a fact -- exactly as if they had written
        ``p.choose("v: body", from_=label)`` themselves.

        The display name follows the *user*'s spec bvar (so they can
        rename to avoid clashes with outer scopes); when the spec isn't
        an existential, falls back to the leaf's own bvar name. The
        witness theorem is SELECT_AX-derived from ``ASSUME(leaf)``, so
        its hyp set is ``{leaf}`` -- which the case's outer ``DISCH(leaf)``
        already retires.

        No-op when ``leaf`` is not existential.
        """
        leaf_pred = dest_exists(leaf)
        if leaf_pred is None:
            return
        leaf_v = leaf_pred.bvar
        w_term = mk_select(leaf_v, leaf_pred.body)
        user_pred = dest_exists(user_term)
        wit_name = (user_pred.bvar.name if user_pred is not None
                    else leaf_v.name)
        eq_label = f"{wit_name}_eq"
        witness_th = CHOOSE_WITNESS(leaf_pred, ASSUME(leaf))
        self._require_fresh_name(wit_name, "case")
        self._cur.choose_env[wit_name] = w_term
        self._register_fact(eq_label, witness_th)

    @contextlib.contextmanager
    def case(self, branch_spec):
        fr = self._cur
        if fr.kind != FrameKind.CASES:
            raise HolError("case() outside cases_on()")
        label, user_term = self._split_label(branch_spec)
        outer_goal = fr.goal
        or_concl = fr.data.or_concl

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
            fr.data.branches.append((leaf, th))

        sub_ctx = _SubFrameCtx(self, outer_goal, kind=FrameKind.CASE,
                                on_close=on_close,
                                extra_facts=[(label, ASSUME(leaf))])
        with sub_ctx as inner_p:
            self._auto_choose_for_case_leaf(leaf, user_term)
            yield inner_p


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

    # ----- builder protocol: resolve refs then finish -----

    def _resolved(self, refs):
        """List form of ``Proof.coerce``: each ref → ``thm``."""
        return [self.p.coerce(r) for r in refs]

    def _via(self, builder, *args):
        """Resolve each arg as a fact and feed positional results into
        ``builder``; ``_finish`` the produced theorem. The protocol every
        ``by_*`` whose justification is "kernel rule applied to facts"
        collapses through."""
        return self._finish(builder(*self._resolved(args)))

    # ----- finishing: alpha-check, register, optionally close goal -----

    def _finish(self, th):
        # When ``thus``-ing, lift directly to the current goal's shape
        # (the have-term and the goal must be simp-equivalent anyway,
        # since ``thus`` discharges the goal). Registering at goal shape
        # avoids a redundant simp lift through the user's have-term form;
        # ``thus``-registered facts have a frame-bounded lifetime, so the
        # shape change has no downstream consumers.
        #
        # When ``self.term is None`` (``have("name:")`` inferred-conclusion
        # form), skip the shape check and register at the justifier's
        # native conclusion -- the user has opted out of stating the
        # intermediate's shape because the kernel rule pins it down.
        if self.is_thus:
            cur = self.p._cur
            if cur.goal is None:
                raise HolError("thus: no current goal")
            th = self.p._simp_require(cur.goal, th, op="thus")
            cur.result = th
        elif self.term is not None:
            th = self.p._simp_require(self.term, th, op="have")
        label = self.label or self.p._fresh_label("h")
        self.p._register_fact(label, th)
        return th

    # ----- justification methods -----

    def by_thm(self, th):
        """Direct: the supplied theorem already proves the have-term.

        ``th`` may be a kernel theorem or a fact label string (resolved
        via ``coerce`` to the registered fact)."""
        return self._finish(self.p.coerce(th))

    def by(self, justification, *args):
        """SPEC/MP chain (if `justification` is a theorem or fact label) or
        a callable.

        - ``thm | label + args``: each arg is dispatched via MP_LIST -- a
          Term arg becomes ``SPEC``, a Theorem arg becomes ``MP``. Strings
          in ``args`` are interpreted as fact labels (theorem) when known,
          else parsed as terms. A ``str`` ``justification`` is resolved as
          a fact label.
        - ``callable + args``: each arg is resolved as a fact (string label
          or theorem); the callable is invoked on them.

        The thm-chain is simp-aware: the head is ``simp_norm_fact``-ed and
        each MP goes through ``simp_mp`` so folded/unfolded forms bridge
        across the chain.
        """
        return self._finish(
            self.p._apply_chain(justification, args, simp=True, op="by"))

    def by_match(self, justification, *args):
        """Backward-chaining variant of ``by``: infer SPEC instantiations
        by first-order matching against both the goal and the supplied
        facts, so the call site lists only what cannot be pinned down.

        Strips outer foralls (their bvars become match variables) and
        peels ``==>`` antecedents one at a time until the residual matches
        the goal. Positional ``args`` are then walked in order, each
        extending a single shared substitution:
          - a fact arg (label / theorem) is matched
            against the next peeled antecedent's pattern, then queued
            for MP;
          - a term arg (string / kernel term) is assigned to the next
            still-unbound forall var.
        After all args, every forall must be bound and every peeled
        antecedent must have a fact. So a transitivity lemma whose
        ``y`` is determined by a fact's type needs no term arg::

            .by_match(SATZ_15, "hxy", "hyz")     # y inferred from hxy

        whereas ``y`` only reachable through the goal still requires an
        explicit term."""
        p = self.p
        if isinstance(justification, str):
            justification = p.coerce(justification)
        if not isinstance(justification, thm):
            raise HolError(
                f"by_match: not a theorem: {justification!r}")
        th = p.simp_norm_fact(justification)
        vs, body = _strip_forall(th)
        vars_set = set(vs)
        pat = body._concl
        # Simp-normalize the goal to the same canonical form simp_norm_fact
        # used on the theorem (lazy-let carriers unfolded), so matching works
        # in lazy-let contexts. _finish will lift back to self.term shape.
        goal_eq = p.simp_normalize(self.term)
        target = rand(goal_eq._concl)
        n_stripped = 0
        while (subst := _term_match(pat, target, vars_set, {})) is None:
            parts = dest_imp(pat)
            if parts is None:
                raise HolError(
                    f"by_match: no antecedent shape of {pp(body._concl)} "
                    f"matches goal {pp(target)}")
            pat = parts[1]
            n_stripped += 1
        ants = []
        cur = body._concl
        for _ in range(n_stripped):
            a_pat, cur = dest_imp(cur)
            ants.append(a_pat)
        facts = []
        ant_idx = 0
        for a in args:
            resolved = p.coerce(a, accept_term=True)
            if isinstance(resolved, thm):
                if ant_idx >= len(ants):
                    raise HolError(
                        f"by_match: extra fact arg, no antecedent left: "
                        f"{a!r}")
                ant_pat = ants[ant_idx]
                fact_concl = rand(p.simp_normalize(resolved._concl)._concl)
                if _term_match(ant_pat, fact_concl,
                               vars_set, subst) is None:
                    raise HolError(
                        f"by_match: fact concl {pp(fact_concl)} "
                        f"does not match antecedent {pp(ant_pat)}")
                facts.append(resolved)
                ant_idx += 1
            else:
                v = next((v for v in vs if v not in subst), None)
                if v is None:
                    raise HolError(
                        f"by_match: extra term arg, all forall vars "
                        f"bound: {a!r}")
                subst[v] = resolved
        unbound = [v.name for v in vs if v not in subst]
        if unbound:
            raise HolError(
                f"by_match: forall vars not determined: {unbound}")
        if ant_idx < len(ants):
            raise HolError(
                f"by_match: {len(ants) - ant_idx} antecedent(s) lack a "
                "fact arg")
        for v in vs:
            th = SPEC(subst[v], th)
        for fact_th in facts:
            th = p.simp_mp(th, fact_th)
        return self._finish(th)

    def by_rewrite(self, rules, *, ac=None, ac_rules=()):
        """REWRITE_PROVE with the given rules, plus any active simp set.

        Each rule may be a Theorem or a string label naming a fact in scope.
        Pass ``ac=(op, assoc, comm)`` to fall back to AC reasoning when the
        rewritten normal forms don't already match. ``ac_rules`` is an
        optional second-pass canonicalisation rule list applied after the
        main rewrite (e.g. ``SUC x → x + 1``-style normalization to expose
        the AC operator). Rules registered via ``p.simp(...)`` in any
        enclosing frame are appended to the user's list.
        """
        rules_thms = self._resolved(rules) + self.p._active_simp_rules()
        return self._finish(REWRITE_PROVE(
            rules_thms, self.term,
            ac=ac,
            ac_rules=tuple(self._resolved(ac_rules))))

    def by_rewrite_of(self, ref, rules, *, ac=None, beta=False, op="by_rewrite_of"):
        """Rewrite a source fact ``ref`` to the have-term using ``rules``.

        Both the source's conclusion and the have-term are normalized
        under ``rules`` to a common form; an equality bridge connecting
        them is then ``EQ_MP``'d against the source. The bottom-up
        rewriter descends through any boolean shape (``=``, ``~``, the
        order operators, applications), so this single tactic covers:

        * one-sided rewrites where the source rewrites onto the target
          (the historical ``REWRITE_RULE`` use case);
        * targeted equality substitution where a bare ``hxy: x = y``
          rewrites the target back onto the source -- e.g. bridging
          ``y + z > y + u`` to ``x + z > y + u``;
        * inequation rewriting where source and target are both
          ``~(L = R)`` and the rules act under the equation.

        Pass ``ac=(op, assoc, comm)`` to AC-normalize every ``op``-node
        encountered during traversal -- e.g. ``ac=(TIMES, SATZ_31, SATZ_29)``
        replaces a hand-built list of ``SPECL([z, y], SATZ_29)``-style
        commutativity rewrites that would otherwise be needed to align
        the source's and target's product orderings.

        With ``beta=True``, BETA-normalize both rewritten ends before
        the aconv check -- needed when ``rules`` unfold a definition
        whose body contains a lambda (e.g. ``FEQ_DEF: |- feq = \\a b c
        d. ...``). ``by_unfold`` delegates here with ``beta=True``.
        """
        p = self.p
        th_src = p.coerce(ref)
        rules_thms = self._resolved(rules) + p._active_simp_rules()
        # Simp-normalize the source's conclusion, the target, and each
        # rule's conclusion to a common canonical form before the kernel
        # rewriter runs. Without this, REWRITE_CONV does syntactic
        # subterm matching on the user's chosen form (folded or
        # unfolded) and a rule whose LHS is in the other form silently
        # no-ops -- the bug that bit the SATZ_27 inlining attempt at
        # the choose-witness SELECT term.
        src_simp = p.simp_normalize(th_src._concl)        # |- src = src_n
        tgt_simp = p.simp_normalize(self.term)             # |- tgt = tgt_n
        rules_n = [p.simp_norm_fact(r) for r in rules_thms]
        src_n = rand(src_simp._concl)
        tgt_n = rand(tgt_simp._concl)
        eq_src_rw = REWRITE_CONV(rules_n, src_n, ac=ac)    # |- src_n = X
        eq_tgt_rw = REWRITE_CONV(rules_n, tgt_n, ac=ac)    # |- tgt_n = Y
        if beta:
            eq_src_rw = TRANS(eq_src_rw, BETA_NORM(rand(eq_src_rw._concl)))
            eq_tgt_rw = TRANS(eq_tgt_rw, BETA_NORM(rand(eq_tgt_rw._concl)))
        n_src = rand(eq_src_rw._concl)
        n_tgt = rand(eq_tgt_rw._concl)
        if not aconv(n_src, n_tgt):
            raise HolError(
                f"{op}: normal forms differ\n"
                f"  source reduces to: {pp(n_src)}\n"
                f"  target reduces to: {pp(n_tgt)}")
        # Chain: src = src_n = X = tgt_n = tgt
        eq_src_full = TRANS(src_simp, eq_src_rw)            # |- src = X
        eq_tgt_full = TRANS(tgt_simp, eq_tgt_rw)            # |- tgt = X
        bridge = TRANS(eq_src_full, SYM(eq_tgt_full))       # |- src = tgt
        return self._finish(EQ_MP(bridge, th_src))

    def by_unfold(self, src, *defs):
        """Prove the goal from ``src`` by unfolding the given definition
        equations (with beta-reduction). The goal and ``src``'s conclusion
        must reduce to the same beta-normal form once ``defs`` fire as
        rewrite rules. Used to bridge a theorem stated in unfolded form
        (e.g. SATZ_9) to a goal stated using the defined symbol (SATZ_10's
        ``>`` / ``<``).

        Thin wrapper over ``by_rewrite_of`` with ``beta=True``."""
        return self.by_rewrite_of(src, list(defs), beta=True, op="by_unfold")

    def by_cases(self, ref, *args):
        """Open a cases-on block whose target is the have-term (rather than
        the parent's goal). On close, the combined ``DISJ_CASES`` result is
        registered as the have's fact (and, if invoked from ``thus``, also
        becomes the current frame's result).

        Like ``cases_on``, accepts extra ``*args`` to ``MP_LIST``-specialize
        a theorem source inline."""
        return self.p._open_cases(
            ref, self.term, self._finish, args=args, op="by_cases")

    def proof(self):
        """Open a sub-frame whose goal is the have-term. The body proves it
        via standard tactics (``thus``, ``cases_on``, ``induction``, …); on
        exit the resulting theorem is registered as the have's fact (and,
        if invoked from ``thus``, also closes the parent goal).

        This is the declarative analogue of writing an intermediate lemma
        inline — the dream sketch's ``.proof(lambda q: …)`` block."""
        return _SubFrameCtx(self.p, self.term, kind=FrameKind.HAVE_PROOF,
                             on_close=self._finish)

    def by_contradiction(self, label_spec):
        """Classical proof by contradiction.

        Open a sub-frame whose goal is ``F`` and whose extra fact is
        ``label: ~target``; the body derives ``F`` (typically via
        ``p.absurd().by_conj`` or ``.auto``); on close, ``NOT_NOT_ELIM``
        lifts the resulting ``~~target`` back to ``target``.

        ``label_spec`` may be a bare label (``"hnex"``) -- the negated
        target is filled in -- or the explicit form
        ``"hnex: ~target"`` (must match ``~self.term``).

        Replaces the ``cases_on(EXCLUDED_MIDDLE, target)`` boilerplate
        whose first branch is just ``thus(target).by_thm(p.fact("h"))``.
        """
        from classical import NOT_NOT_ELIM   # classical depends on proof
        target = self.term
        p = self.p
        not_target = mk_not(target)

        label = p._parse_label_or_check(
            label_spec, not_target, op="by_contradiction")

        def on_close(F_th):
            nn_th = NOT_INTRO(DISCH(not_target, F_th))
            self._finish(NOT_NOT_ELIM(nn_th))

        return _SubFrameCtx(p, F, kind=FrameKind.SUPPOSE,
                             on_close=on_close,
                             extra_facts=[(label, ASSUME(not_target))])

    def by_eq_mp(self, eq_th, ref):
        """``EQ_MP(eq_th, fact)`` -- rewrite a fact through an equation.

        Aligns the equation's LHS with the fact's conclusion via simp, so
        the user can mix folded/unfolded forms across an EQ_MP boundary."""
        return self._via(self.p.simp_eq_mp, eq_th, ref)

    def by_def(self, def_th, ref):
        """Unfold ``def_th`` at ``ref``'s head args, then ``EQ_MP`` through.

        Sugar for the ``by_eq_mp(UNFOLD(def_th, a1, ..., an), ref)`` cliche
        that dominates relation-unfold proofs. ``def_th`` must be
        ``|- C = \\x1...xn. body``; arity ``n`` is read off the RHS lambda
        chain. ``ref``'s conclusion must be ``C t1 ... tn`` (modulo simp);
        ``UNFOLD`` is auto-instantiated at those args, the resulting fact's
        conclusion is ``body[xi := ti]``."""
        p = self.p
        th_ref = p.coerce(ref)
        parts = dest_eq(def_th._concl)
        if parts is None:
            raise HolError(
                f"by_def: definition is not an equation: "
                f"{pp(def_th._concl)}")
        head, rhs = parts
        n = 0
        while isinstance(rhs, Abs):
            n += 1
            rhs = rhs.body
        if n == 0:
            raise HolError(
                f"by_def: definition RHS is not a lambda: "
                f"{pp(def_th._concl)}")
        concl = p.simp_norm_fact(th_ref)._concl
        peeled = []
        for _ in range(n):
            if not isinstance(concl, Comb):
                raise HolError(
                    f"by_def: fact {pp(th_ref._concl)} is not applied to "
                    f"{n} args (definition arity)")
            peeled.append(concl.arg)
            concl = concl.fun
        peeled.reverse()
        if not aconv(concl, head):
            raise HolError(
                f"by_def: fact head {pp(concl)} does not match "
                f"definition LHS {pp(head)}")
        return self._finish(p.simp_eq_mp(UNFOLD(def_th, *peeled), th_ref))

    def by_inst(self, lemma, *args):
        """``SPECL`` ``lemma`` at term args.

        Each ``arg`` is a kernel term or a string parsed as a term in
        the current scope. ``lemma`` is a fact label or theorem. Sugar
        for the ``var = SPECL([t1,...,tn], LEMMA)`` cliche; pairs with
        ``have("label:")`` so the resulting fact's conclusion does not
        need to be spelled out by the caller."""
        p = self.p
        th = p.simp_norm_fact(p.coerce(lemma))
        for a in args:
            resolved = p.coerce(a, accept_term=True)
            if isinstance(resolved, thm):
                raise HolError(
                    f"by_inst: arg {a!r} resolved to a theorem; "
                    "expected a term")
            th = SPEC(resolved, th)
        return self._finish(th)

    def by_trans(self, *eqs):
        """``TRANS_CHAIN`` over ``eqs``: compose ``a=b``, ``b=c``, ...
        into ``a=c``. Each ``eq`` is a fact label or theorem of equation
        shape."""
        if len(eqs) < 2:
            raise HolError(
                f"by_trans: needs at least 2 equations, got {len(eqs)}")
        return self._finish(TRANS_CHAIN(self._resolved(eqs)))

    def by_cong(self, left, right):
        """Single-step congruence on ``left`` / ``right``.

        Each side is a fact (theorem of equation shape) or a kernel
        term. Dispatch:

        * term + fact: ``AP_TERM(left, right)`` -- ``f a = f b`` from
          ``a = b``.
        * fact + term: ``AP_THM(left, right)`` -- ``g x = h x`` from
          ``g = h``.
        * fact + fact: ``MK_COMB(left, right)`` -- ``f a = g b`` from
          ``f = g`` and ``a = b``.
        """
        p = self.p
        L = p.coerce(left, accept_term=True)
        R = p.coerce(right, accept_term=True)
        if isinstance(L, thm) and isinstance(R, thm):
            return self._finish(MK_COMB(L, R))
        if isinstance(L, thm):
            return self._finish(AP_THM(L, R))
        if isinstance(R, thm):
            return self._finish(AP_TERM(L, R))
        raise HolError(
            "by_cong: at least one side must be an equation fact "
            f"(got both terms: {pp(L)} / {pp(R)})")

    def by_iff(self, fwd, rev):
        """For a boolean-equality have-term ``L = R``, combine two
        implications into the iff: ``fwd: L ==> R`` and ``rev: R ==> L``.

        Argument order may be either direction; the matching against the
        target's L/R disambiguates. Each ref is a fact label or theorem.
        Internally: ``MP(impl, ASSUME(ant))`` on each side gives
        ``{L} |- R`` and ``{R} |- L``, which DEDUCT_ANTISYM_RULE fuses
        into ``|- L = R``."""
        target = self.term
        eq_parts = dest_eq(target)
        if eq_parts is None:
            raise HolError(
                f"by_iff: target is not an equality: {pp(target)}")
        L, R = eq_parts
        p = self.p
        th_a = p.simp_norm_fact(p.coerce(fwd))
        th_b = p.simp_norm_fact(p.coerce(rev))

        def matches(th, ant, conseq):
            parts = dest_imp(th._concl)
            if parts is None:
                return False
            a, c = parts
            return aconv(a, ant) and aconv(c, conseq)

        if matches(th_a, L, R) and matches(th_b, R, L):
            th_lr, th_rl = th_a, th_b
        elif matches(th_a, R, L) and matches(th_b, L, R):
            th_lr, th_rl = th_b, th_a
        else:
            raise HolError(
                f"by_iff: facts do not form L ==> R / R ==> L for goal "
                f"{pp(target)}\n"
                f"  fact A: {pp(th_a._concl)}\n"
                f"  fact B: {pp(th_b._concl)}")

        th_R_from_L = MP(th_lr, ASSUME(L))   # {L} |- R
        th_L_from_R = MP(th_rl, ASSUME(R))   # {R} |- L
        return self._finish(
            DEDUCT_ANTISYM_RULE(th_L_from_R, th_R_from_L))

    def by_fold(self, ref):
        """Inverse of an unfolder: if the have-term is ``a R b`` for a
        relation ``R`` registered with ``register_unfolder`` or
        ``register_disj_unfolder``, fold ``ref`` (whose conclusion equals the
        unfolded form) back into ``a R b``."""
        target = self.term
        unfold_eq = _lookup_relation(target)
        if unfold_eq is None:
            raise HolError(
                f"by_fold: no unfolder registered for target: {pp(target)}")
        fact = self.p.coerce(ref)
        return self._finish(EQ_MP(SYM(unfold_eq), fact))

    def by_witness(self, witness, ref):
        """For an existential have-term ``?v. P v`` (or a registered relation
        ``a R b`` whose unfolded form is ``?v. body``), given a fact whose
        conclusion is ``P[witness/v]``, produce ``?v. P v`` via ``EXISTS``
        (and fold back through the relation's unfolder if applicable).

        ``witness`` is parsed in the current scope (so ``choose``-bound names
        are available) or accepted as a kernel term directly. A list/tuple
        of witnesses peels that many ``?`` levels in one call (the supplied
        fact must match the innermost body). ``ref`` is a fact label, fact
        index, or a theorem.
        """
        target = self.term
        p = self.p
        fact_th = p.coerce(ref)

        if isinstance(witness, (list, tuple)):
            witnesses = [p._parse(w) if isinstance(w, str) else w
                         for w in witness]
        else:
            witnesses = [p._parse(witness) if isinstance(witness, str)
                         else witness]

        def body_provider(body_at_w):
            return p._simp_require(body_at_w, fact_th, op="by_witness")

        th = p._make_existential_multi(target, witnesses, body_provider)
        if th is not None:
            return self._finish(th)

        # body_provider raises rather than returning None, so a None here
        # means the target shape didn't qualify.
        unfold_eq = _lookup_relation(target, kind="exists")
        if unfold_eq is not None:
            raise HolError(
                f"by_witness: unfolded form is not existential: "
                f"{pp(rand(unfold_eq._concl))}")
        raise HolError(
            "by_witness: target is not existential or a registered relation: "
            f"{pp(target)}")

    def by_exists(self, witnesses, *rules):
        """Introduce a multi-quantifier existential ``?v1 ... vn. body`` (or
        a registered relation that unfolds to one) at concrete witnesses,
        with the substituted body discharged automatically.

        Each top-level ``/\\`` conjunct of the substituted body is proved
        via ``REWRITE_PROVE(rules + active simp set)``; reflexive leaves
        (``t = t``) need no rules at all. ``witnesses`` is a list/tuple of
        terms (strings parsed in the current scope, or kernel terms).
        """
        p = self.p
        target = self.term
        if not isinstance(witnesses, (list, tuple)):
            witnesses = [witnesses]
        witnesses_t = [p._parse(w) if isinstance(w, str) else w
                       for w in witnesses]
        rules_thms = ([p.coerce(r) for r in rules]
                      + p._active_simp_rules())

        def prove(tm):
            if is_conj(tm):
                l, r = dest_conj(tm)
                return CONJ(prove(l), prove(r))
            return REWRITE_PROVE(rules_thms, tm)

        th = p._make_existential_multi(target, witnesses_t, prove)
        if th is None:
            raise HolError(
                "by_exists: target is not existential or unfoldable: "
                f"{pp(target)}")
        return self._finish(th)

    def by_select_def(self, def_th, *args, from_):
        """Read the body of a SELECT-style definition at concrete arguments.

        Given ``def_th : |- f = \\x1 ... xk. @v. P v`` and a fact
        ``from_ : ?v. P v`` (already instantiated at the same args),
        derive ``P[(f arg1 ... argk) / v]`` by ``CHOOSE_WITNESS`` on
        ``P``, then folding ``@v. P v`` back to ``f arg1 ... argk``
        through ``SYM(UNFOLD(def_th, args))``.

        The ``args`` are the SPECL terms (strings parsed in scope, or
        kernel terms) the definition is to be instantiated at; the
        existence fact's predicate must already match the body of
        ``def_th`` after that instantiation.
        """
        p = self.p
        def_eq = p.coerce(def_th)
        ex_th = p.coerce(from_)
        spec_args = [p._parse(a) if isinstance(a, str) else a for a in args]
        unfold_eq = UNFOLD(def_eq, *spec_args)   # |- f a1...ak = @v. P v
        pred = dest_exists(ex_th._concl)
        if pred is None:
            raise HolError(
                "by_select_def: from_ is not existential: "
                f"{pp(ex_th._concl)}")
        body_at_sel = CHOOSE_WITNESS(pred, ex_th)   # asl |- P[(@v.Pv)/v]
        folded = REWRITE_RULE([SYM(unfold_eq)], body_at_sel)
        return self._finish(p._simp_require(
            self.term, folded, op="by_select_def"))

    def by_disj(self, ref):
        """Given a fact whose conclusion alpha-matches one of the goal's
        right-associated disjuncts, build the ``DISJ1``/``DISJ2`` chain to
        inject it as the proof of the whole disjunction."""
        p = self.p
        fact_th = p.simp_norm_fact(p.coerce(ref))

        def match(leaf):
            return fact_th if aconv(leaf, fact_th._concl) else None

        return self._finish(p._build_disj(self.term, match, "by_disj"))

    def by_ac(self, op, assoc, comm):
        """AC_PROVE under ``(op, assoc, comm)`` for the (equation) have-term.

        Equivalent to ``by_rewrite([], ac=(op, assoc, comm))`` but skips
        the empty-rule normalization for the common no-rewrite case.
        """
        return self._finish(AC_PROVE(op, assoc, comm, self.term))


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
        self.p._cur.result = result
        return result

    def by_thm(self, th):
        return self._finish(th)

    def by(self, justification, *args):
        return self._finish(
            self.p._apply_chain(justification, args, simp=False, op="absurd"))

    def by_conj(self, *refs):
        """Discharge F from a fact ``P`` and a fact ``~P`` (in either order).

        The two refs name a positive fact and its direct negation; we run
        ``MP(NOT_ELIM(neg), pos)``."""
        if len(refs) != 2:
            raise HolError(
                f"absurd: by_conj requires exactly two facts, got {len(refs)}")
        a, b = (self.p.coerce(r) for r in refs)
        # Try `a` as the negation, then `b`.
        for neg, pos in ((a, b), (b, a)):
            inner = dest_neg(neg._concl)
            if inner is None:
                continue
            if aconv(inner, pos._concl):
                return self._finish(MP(NOT_ELIM(neg), pos))
            # Lift the positive fact to the negation's inner-shape via
            # simp so a folded ``M (m+1)`` matches an unfolded
            # ``~(!n. N n ==> m+1 <= n)``.
            lifted = self.p.simp_match(inner, pos)
            if lifted is not None:
                return self._finish(MP(NOT_ELIM(neg), lifted))
        raise HolError(
            "absurd: by_conj could not match P / ~P among "
            f"{pp(a._concl)} / {pp(b._concl)}")

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
        ths = [self.p.coerce(r) for r in refs]
        cs = [dest_binop_any(th._concl) for th in ths]
        if cs[0] is None or cs[1] is None:
            raise HolError(
                "absurd: auto() cannot classify fact shapes: "
                f"{pp(ths[0]._concl)} / {pp(ths[1]._concl)}")
        rel0, rel1 = cs[0][0], cs[1][0]
        finder = _CONTRA_FINDERS.get((rel0, rel1))
        if finder is None:
            raise HolError(
                f"absurd: auto() has no finder for ({rel0!r}, {rel1!r})")
        return self._finish(finder(ths[0], ths[1]))

    def via(self, forward, case, *, source):
        """Lift ``case`` through ``forward`` to a fact contradicting ``source``.

        ``forward`` is a theorem ``... case_pattern ==> lifted_pattern``;
        ``case`` is a fact whose conclusion matches ``case_pattern``;
        ``source`` is a fact (a binary relation ``op_src(L, R)``) whose
        relation is mutually exclusive with ``case``'s once both are over
        the same operands.

        The forward's foralls are inferred by matching its antecedent
        against ``case``'s conclusion and its consequent against
        ``op_case(L, R)`` -- where ``op_case`` is ``case``'s top-level
        relation and ``L``, ``R`` come from ``source``. ``finder``
        registered via ``register_contra_finder`` for
        ``(rel(source), rel(lifted))`` produces ``|- F``.

        Used inside a ``cases_on`` branch as the one-line analogue of
        ``p.have(...).by_match(forward, case); p.absurd().auto(source, ...)``.
        """
        p = self.p
        case_th = p.coerce(case)
        src_th = p.coerce(source)
        fwd_th = p.coerce(forward)

        # Build the lifted target shape: case's relation applied to source's
        # operands. Both must be binary applications.
        src_concl = rand(p.simp_normalize(src_th._concl)._concl)
        case_concl = rand(p.simp_normalize(case_th._concl)._concl)
        for tm, label in ((src_concl, "source"), (case_concl, "case")):
            if not (isinstance(tm, Comb) and isinstance(tm.fun, Comb)):
                raise HolError(
                    f"absurd.via: {label} is not a binary relation: {pp(tm)}")
        src_L, src_R = src_concl.fun.arg, src_concl.arg
        case_op = case_concl.fun.fun
        target_lifted = mk_app(case_op, src_L, src_R)

        # Specialize forward by matching antecedent ↔ case and consequent ↔
        # target_lifted; then MP with case_th.
        fwd = p.simp_norm_fact(fwd_th)
        vs, fwd_body = _strip_forall(fwd)
        vars_set = set(vs)
        parts = dest_imp(fwd_body._concl)
        if parts is None:
            raise HolError(
                f"absurd.via: forward is not an implication: {pp(fwd._concl)}")
        ant_pat, con_pat = parts
        subst = _term_match(ant_pat, case_concl, vars_set, {})
        if subst is None:
            raise HolError(
                f"absurd.via: forward antecedent {pp(ant_pat)} "
                f"does not match case {pp(case_concl)}")
        subst = _term_match(con_pat, target_lifted, vars_set, subst)
        if subst is None:
            raise HolError(
                f"absurd.via: forward consequent {pp(con_pat)} "
                f"does not match target {pp(target_lifted)}")
        unbound = [v.name for v in vs if v not in subst]
        if unbound:
            raise HolError(
                f"absurd.via: forall vars not determined: {unbound}")
        specced = fwd
        for v in vs:
            specced = SPEC(subst[v], specced)
        lifted = p.simp_mp(specced, case_th)

        # Pair source and lifted via auto.
        cs_src = dest_binop_any(src_th._concl)
        cs_lif = dest_binop_any(lifted._concl)
        finder = _CONTRA_FINDERS.get((cs_src[0], cs_lif[0]))
        if finder is None:
            raise HolError(
                f"absurd.via: no contra finder for "
                f"({cs_src[0]!r}, {cs_lif[0]!r})")
        return self._finish(finder(src_th, lifted))


# ---------------------------------------------------------------------------
# Calc: equational-chain context, Mizar's ``... .= ...`` idiom.
#
# A calc has a running ``cur_rhs`` (initially the user's LHS) and a running
# ``chain_th`` (initially ``None``, then ``|- lhs = cur_rhs``). Each
# ``c.step("= rhs").by_*(...)`` proves the segment ``cur_rhs = rhs`` and
# TRANS-composes it onto the chain. Steps don't push a frame and don't
# register their own facts; only the composed equation is registered on
# context exit.
# ---------------------------------------------------------------------------

class _CalcCtx:
    __slots__ = ("p", "label", "lhs", "thus_mode", "cur_rhs", "chain_th")

    def __init__(self, p, label, lhs, thus_mode):
        self.p = p
        self.label = label
        self.lhs = lhs
        self.thus_mode = thus_mode
        self.cur_rhs = lhs
        self.chain_th = None

    def __enter__(self):
        return self

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        if self.chain_th is None:
            raise HolError("calc: no steps in chain")
        eq_th = self.chain_th
        if self.thus_mode:
            cur = self.p._cur
            if cur.goal is None:
                raise HolError("calc: thus=True but no current goal")
            cur.result = self.p._simp_require(cur.goal, eq_th, op="calc")
        label = self.label or self.p._fresh_label("h")
        self.p._register_fact(label, eq_th)
        return False

    def step(self, spec):
        s = spec.strip()
        if not s.startswith("="):
            raise HolError(
                f"calc.step: expected '= rhs', got {spec!r}")
        rhs_str = s[1:].strip()
        try:
            rhs_term = parse(rhs_str, _env_bindings=self.p._scope_env())
        except ParseError as ex:
            raise HolError(
                f"calc.step: cannot parse RHS in {spec!r}: {ex}") from ex
        segment = mk_eq(self.cur_rhs, rhs_term)
        return _CalcStep(self, segment, rhs_term)


class _CalcStep(_Have):
    """One segment of a ``calc`` chain. Inherits every ``by_*`` from
    ``_Have``; overrides ``_finish`` to TRANS the segment onto the
    chain and advance ``cur_rhs`` instead of registering a fact."""
    __slots__ = ("calc_ctx", "rhs")

    def __init__(self, calc_ctx, segment_term, rhs_term):
        super().__init__(calc_ctx.p, label=None, term=segment_term,
                         is_thus=False)
        self.calc_ctx = calc_ctx
        self.rhs = rhs_term

    def _finish(self, th):
        c = self.calc_ctx
        seg_th = self.p._simp_require(self.term, th, op="calc.step")
        if c.chain_th is None:
            c.chain_th = seg_th
        else:
            c.chain_th = TRANS(c.chain_th, seg_th)
        c.cur_rhs = self.rhs
        return seg_th


# ---------------------------------------------------------------------------
# Sub-frame context manager: pushes a frame with a sub-goal, on exit verifies
# discharge and reports the result back to the parent via ``on_close``.
# ---------------------------------------------------------------------------

def _exit_frame(p, exc_type, on_close):
    """Common exit shape for proof-frame context managers: on clean exit,
    pop the current frame and pass it to ``on_close(fr)`` for synthesis
    and delivery. Returns ``False`` so exceptions propagate. ``on_close``
    is responsible for calling ``p._drop_facts(fr.facts_added)`` at the
    appropriate point in its work."""
    if exc_type is not None:
        return False
    fr = p._frames.pop()
    on_close(fr)
    return False


class _SubFrameCtx:
    def __init__(self, p, goal, kind, on_close, extra_facts=()):
        self.p = p
        self.goal = goal
        self.kind = kind
        self.on_close = on_close
        self.extra_facts = list(extra_facts)

    def __enter__(self):
        # Simp-normalize the sub-goal against the active lazy-let set so the
        # inner proof can ``fix`` over a forall hidden inside a folded
        # carrier (e.g. ``thus("R c h (SUC n) (h n m)").proof()``: `R` peels
        # to ``!Q. ...``, exposing the binder). The normalized form goes into
        # the frame's `goal`; on close, ``_finish`` re-folds via simp-match
        # against the original have-term.
        carriers = self.p._lazy_let_carriers()
        goal = self.goal
        if carriers:
            eq = self.p.simp_normalize(goal, carriers)
            if not aconv(rand(eq._concl), goal):
                goal = rand(eq._concl)
        fr = _Frame(goal=goal, kind=self.kind)
        self.p._frames.append(fr)
        for label, th in self.extra_facts:
            if label is None:
                label = self.p._fresh_label("h")
            self.p._register_fact(label, th)
        return self.p

    def __exit__(self, exc_type, *_):
        return _exit_frame(self.p, exc_type, self._on_pop)

    def _on_pop(self, fr):
        if fr.result is None:
            raise HolError(
                f"{self.kind}: block did not discharge sub-goal via thus")
        th = self.p._close_frame(fr, fr.result)
        self.p._drop_facts(fr.facts_added)
        self.on_close(th)


# ---------------------------------------------------------------------------
# Induction block: pushes an INDUCTION frame whose .base() / .step()
# children fill in base_th / step_th. On exit, INDUCT_PROVE composes them and
# the result is set as the parent frame's .result, after SPEC'ing the
# induction variable so the resulting term matches the parent's body-shaped
# goal (the outer fix() will GEN it back).
# ---------------------------------------------------------------------------

class _InductionCtx:
    def __init__(self, p, var, body, strategy, peel_forall=False):
        self.p = p
        self.var = var
        self.body = body
        self.strategy = strategy
        self.peel_forall = peel_forall

    def __enter__(self):
        fr = _Frame(goal=None, kind=FrameKind.INDUCTION)
        fr.data = _InductionData(var=self.var, body=self.body,
                                  strategy=self.strategy)
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        return _exit_frame(self.p, exc_type, self._on_pop)

    def _on_pop(self, fr):
        d = fr.data
        if d.base_th is None:
            raise HolError("induction: missing base()")
        if d.step_th is None:
            raise HolError("induction: missing step()")
        # User's step_th already contains ASSUME(body) as a hypothesis (under
        # the IH label). induct_prove wraps that with DISCH(body, ...) and
        # GEN(var, ...) to produce |- !var. body. If the parent's goal already
        # has a !var binder, leave it as is; otherwise SPEC var back out so
        # the parent's body-shaped goal matches.
        forall_th = self.strategy.induct_prove(
            self.var, self.body, d.base_th, lambda IH: d.step_th)
        body_th = forall_th if self.peel_forall else SPEC(self.var, forall_th)
        body_th = self.p._close_frame(fr, body_th)
        self.p._drop_facts(fr.facts_added)
        parent = self.p._cur
        if parent.goal is None or not aconv(parent.goal, body_th._concl):
            raise HolError(
                "induction: produced wrong conclusion\n"
                f"  goal: {pp(parent.goal) if parent.goal else 'None'}\n"
                f"  got:  {pp(body_th._concl)}")
        parent.result = body_th


# ---------------------------------------------------------------------------
# cases_on block: pushes a CASES frame; .case() children supply each
# branch's proof under an extra hypothesis. On exit, DISJ_CASES composes them.
# ---------------------------------------------------------------------------

def _find_disj_leaf(or_concl, target):
    """Walk a right-associated disjunction; return the leaf alpha-equivalent
    to ``target``, or ``None``. The whole disjunction itself is also a valid
    leaf (matched at depth 0)."""
    if aconv(or_concl, target):
        return or_concl
    parts = dest_disj(or_concl)
    if parts is None:
        return None
    left, right = parts
    if aconv(left, target):
        return left
    return _find_disj_leaf(right, target)


def _split_disj_n(term, n):
    """Right-associated split of ``p1 \\/ (p2 \\/ (... \\/ pn))`` into a
    list of exactly ``n`` disjuncts, or ``None`` if the shape doesn't fit."""
    leaves = [term]
    while len(leaves) < n:
        parts = dest_disj(leaves[-1])
        if parts is None:
            return None
        left, right = parts
        leaves[-1] = left
        leaves.append(right)
    return leaves


def _build_disj_cases(or_th, branches):
    """Compose nested ``DISJ_CASES`` over a right-associated disjunction.

    ``or_th``'s conclusion is ``p1 \\/ (p2 \\/ (... \\/ pn))``; ``branches``
    is the matching ordered list of ``(disjunct_term, branch_th)`` pairs
    where each ``branch_th`` proves the target under hypothesis
    ``disjunct_term``. Returns the combined theorem with all branch
    hypotheses discharged."""
    if len(branches) == 1:
        return branches[0][1]
    head_term, head_th = branches[0]
    rest_or = or_th._concl.arg
    inner_th = _build_disj_cases(ASSUME(rest_or), branches[1:])
    return DISJ_CASES(or_th,
                      DISCH(head_term, head_th),
                      DISCH(rest_or, inner_th))


class _CasesCtx:
    def __init__(self, p, or_th, target, on_close, op="cases_on"):
        self.p = p
        self.or_th = or_th
        self.target = target
        self.on_close = on_close
        self.op = op

    def __enter__(self):
        fr = _Frame(goal=self.target, kind=FrameKind.CASES)
        fr.data = _CasesData(or_concl=self.or_th._concl)
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        return _exit_frame(self.p, exc_type, self._on_pop)

    def _on_pop(self, fr):
        op = self.op
        branches = fr.data.branches
        n = len(branches)
        if n < 2:
            raise HolError(
                f"{op}: need at least 2 case() blocks, got {n}")
        leaves = _split_disj_n(self.or_th._concl, n)
        if leaves is None:
            raise HolError(
                f"{op}: cannot split into {n} disjuncts: "
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
                    f"{op}: branch does not match any disjunct: "
                    f"{pp(branch_term)}")
        if any(s is None for s in slots):
            missing = [pp(leaves[i]) for i, s in enumerate(slots) if s is None]
            raise HolError(f"{op}: missing case for {missing}")
        result = _build_disj_cases(self.or_th, slots)
        result = self.p._discharge_lazy_lets(fr, result)
        self.p._drop_facts(fr.facts_added)
        if not aconv(self.target, result._concl):
            # Bridge folded/unfolded forms via simp -- cases_on's combined
            # result may have the unfolded shape while the user's target
            # was written using a let-bound symbol (or vice versa).
            lifted = self.p.simp_match(self.target, result)
            if lifted is None:
                raise HolError(
                    f"{op}: produced wrong conclusion\n"
                    f"  target: {pp(self.target)}\n"
                    f"  got:    {pp(result._concl)}")
            result = lifted
        self.on_close(result)


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
    return p._close_frame(fr, fr.result)



# Self-tests live in proof_test.py (H17). Splitting them out also
# retires the sys.modules workaround that proof.py-as-__main__ needed
# to make num.py's induction-strategy registration visible (H2).
