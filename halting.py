"""Undecidability of the halting problem, via SK combinators over HF.

SKETCH ONLY -- this file lays out the construction; the proofs are
stubbed with ``p.sorry()``. The goal is to state and prove, as a HOL
theorem, that no SK combinator decides whether an SK term has a normal
form:

    |- ~ ?H. is_sk_term H /\\
             !t. is_sk_term t ==> ((App H t) reduces_to K_t  <=>  halts t).

The whole development lives over ``hf_sets.py`` plus ``nat0.py``.
Axiomatic cost: zero. The construction reuses ``Pair_ord`` for tagged
HF tuples; no new primitives.

------------------------------------------------------------------
Why SK and not Turing machines or lambda
------------------------------------------------------------------

Three computation models give the same theorem; SK is the cheapest:

  TM        : finite tuple <Q, Sigma, delta, q0, F> + tape encoding +
              configuration step + universal machine. ~600 LOC.
  lambda    : Var/Lam/App + de Bruijn shift + capture-free substitution
              + beta-step. ~500 LOC. Substitution interacts with the
              bit-encoded canonical-form preconditions of ``substitute``
              (cf. ``project_pyzar_simp_select_constraint``).
  SK        : three tags, no binders, two local rewrite rules.
              ~300 LOC. No substitution lemmas. ``Omega = SII(SII)``
              is the non-halting witness, definable in five symbols.

The diagonal is the same shape in all three. SK wins by avoiding the
nastiest infrastructure piece (substitution under binders) while
keeping the diagonal mechanically identical.

------------------------------------------------------------------
The idea (Turing 1936; SK presentation: Barendregt Ch. 7)
------------------------------------------------------------------

Three ingredients:

  (1) *Encoding.* SK terms are finite ternary trees: leaves S/K, internal
      nodes App. Each is a tagged HF tuple, hence a nat0. Reduction
      rules ``K x y -> x`` and ``S x y z -> x z (y z)`` are local
      pattern matches.

  (2) *Halting.*  ``halts t := ?n u. reduces_in n t u /\\ is_normal u``.
      Existential over ``num`` plus a primitive recursive body, so
      ``halts`` is r.e. -- but not, the theorem says, decidable by an
      SK term.

  (3) *Diagonal.* Curry's fixed-point combinator ``Y`` gives, for any
      ``f``, a term ``Y f`` such that ``Y f -->* f (Y f)``. Apply with
      ``f := \\x. if H(x) then Omega else K_t``. The fixed point ``d``
      satisfies ``d -->* if H(d) then Omega else K_t``. If ``H`` decides
      halting, ``halts d <=> halts (if H(d) then Omega else K_t) <=>
      halts d`` -- contradiction either way.

Lambda-abstraction is *defined* on SK (Curry's algorithm ``[x] e``);
no binder primitive needed.

------------------------------------------------------------------
The HOL encoding hurdle
------------------------------------------------------------------

There isn't one for the data: ``Pair_ord`` from ``hf_sets.py`` gives
ordered pairs on nat0, so tagged tuples ``<n, t1, ..., tk>`` are
nested Pair_ord's. The work is:

  * Defining ``sk_step`` as a primitive recursive HF function (it
    inspects the head of an application chain and matches K/S).
  * Defining ``sk_reduces : num -> nat0 -> nat0 -> bool`` by primitive
    recursion on the step count, and ``halts`` as the existential
    closure.
  * Constructing ``Y`` and proving its fixed-point property as an SK
    reduction.
  * The diagonal argument itself -- once the reduction lemmas are in
    place, ~30 lines.

------------------------------------------------------------------
Stage map
------------------------------------------------------------------

  Stage 0:  SK terms as tagged HF tuples (S_t, K_t, App_t, is_sk_term).
  Stage 1:  One-step reduction sk_step + determinism.
  Stage 2:  Multi-step sk_reduces, normal-form predicate, halts.
  Stage 3:  Useful combinators: I, KI, Omega; OMEGA_NON_HALTING.
  Stage 4:  Curry's fixed-point combinator Y and the fixed-point
            theorem Y_FIXED_POINT.
  Stage 5:  Lambda-abstraction emulation [x]e (the bracket abstraction
            algorithm) -- used only to define D readably; could be
            inlined.
  Stage 6:  HALTING_UNDECIDABLE: no SK term decides halting.
  Stage 7:  Corollary: ``halts`` is not primitive recursive
            (essentially, the standard Rice-flavoured consequence).

------------------------------------------------------------------
What this gives and doesn't give
------------------------------------------------------------------

Derived from the bare HOL kernel + ``hf_sets.py``:
  * Undecidability of halting for SK combinators (the headline).
  * Non-haltingness of Omega -- a concrete non-terminating program.
  * SK is Turing-complete in the weak sense: Y gives general recursion.

Not in scope here:
  * Equivalence with Turing machines or lambda calculus (would need a
    third file). The theorem stands on its own without it.
  * Church-Rosser confluence. Cleanly provable here via the standard
    parallel-reduction argument (Tait/Martin-Loef minus the binder
    cases, so ~80 lines), but the halting theorem does not depend on
    it.

Pairs especially well with ``godel_first.py``: the diagonal in this
file is mechanically the same as the Goedel diagonal -- self-application
producing self-reference. Tarski's undefinability of truth is the same
diagonal a third time.
"""

from fusion import Var, new_constant, HolError
from basics import mk_const, mk_app, mk_abs, mk_eq, rand, rator, aconv, dest_eq
from parser import define, parse_type, add_const, pp
from nat0 import nat0_ty, ZERO, mk_suc0
from nat0_order import define_wf_lt
from proof import proof, define_with_at, register_intro_set
from tactics import REFL, SPEC, SPECL, SYM, EQ_MP, DISJ1, DISJ2, CONJ, EXISTS, MP
from tactics import AP_TERM, TRANS, REWRITE_CONV, BETA_NORM, unfold_def_at
from axioms import mk_exists
from hf_sets import Pair_ord
from hf_syntax import (
    _proof_lt_binary_left,
    _proof_lt_binary_right,
    _unfold_rec_via_F_def,
    mono_iff_binary_step,
)
from tactics import or_chain_collapse


# ---------------------------------------------------------------------------
# Stage 0 -- SK terms as tagged HF tuples.
#
#   S_t   := Pair_ord 0 0
#   K_t   := Pair_ord (SUC0 0) 0
#   App_t := \\t u. Pair_ord (SUC0 (SUC0 0)) (Pair_ord t u)
#
# A nat0 ``t`` is a well-formed SK term iff it lies in the inductive
# closure of {S_t, K_t} under App_t.  The predicate ``is_sk_term`` is
# primitive recursive on the structural decoder for Pair_ord (each
# unfolding strictly reduces the nat0 by Foundation, so HF1-5 give
# termination).
# ---------------------------------------------------------------------------


_tag_S = ZERO
_tag_K = mk_suc0(ZERO)
_tag_App = mk_suc0(mk_suc0(ZERO))


S_T_DEF = define(
    "S_t",
    nat0_ty,
    mk_app(Pair_ord, _tag_S, ZERO),
)
S_t = mk_const("S_t", [])


K_T_DEF = define(
    "K_t",
    nat0_ty,
    mk_app(Pair_ord, _tag_K, ZERO),
)
K_t = mk_const("K_t", [])


_t_n0 = Var("t", nat0_ty)
_u_n0 = Var("u", nat0_ty)


# ``define_with_at`` yields both ``App_t = \t u. body`` and the pointwise
# ``!t u. App_t t u = body``; the latter feeds the NAT0_LT_APP_T_*
# size lemmas required by ``define_wf_lt``.
APP_T_DEF, APP_T_AT = define_with_at(
    "App_t",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t:nat0. \\u:nat0. Pair_ord (SUC0 (SUC0 0)) (Pair_ord t u)",
)
App_t = mk_const("App_t", [])

# Tag literal for App_t, used by the size-lemma builders.
_APP_T_TAG = "SUC0 (SUC0 0)"


# NAT0_LT_APP_T_L : |- !a b. nat0_lt a (App_t a b)
# NAT0_LT_APP_T_R : |- !a b. nat0_lt b (App_t a b)
# These bound the recursion depth so ``define_wf_lt`` can take a least
# fixed point.  Identical shape to the Imp_f / Insert_t cases in
# ``hf_syntax.py``; we reuse the private builders directly.
NAT0_LT_APP_T_L = _proof_lt_binary_left(
    "NAT0_LT_APP_T_L", "a", "b", "App_t", APP_T_AT, _APP_T_TAG
)
NAT0_LT_APP_T_R = _proof_lt_binary_right(
    "NAT0_LT_APP_T_R", "a", "b", "App_t", APP_T_AT, _APP_T_TAG
)


# ``is_sk_term`` is the SK-closure predicate, defined by well-founded
# recursion on Pair_ord-depth via ``define_wf_lt`` (the same pattern
# ``hf_syntax.IS_TERM_DEF`` uses for is_term).
#
# Body of the recursion functional ``_is_sk_term_F : (nat0 -> bool) ->
# nat0 -> bool``:
#
#   _is_sk_term_F f n  :=  n = S_t \/
#                          n = K_t \/
#                          ?a b. n = App_t a b /\ f a /\ f b
#
# The S_t / K_t disjuncts are non-recursive in f; only the App_t branch
# feeds back, and there only at strictly-smaller arguments (NAT0_LT_APP_T_*).
# That makes ``_is_sk_term_F`` monotone for the WF-lt fixed point.
#
# Trade-off vs. the impredicative encoding (previously tried):
#   * Impredicative: three intro rules trivial, inversion (CASES) hard.
#   * define_wf_lt: needs setup (size lemmas + monotonicity), but
#     ``IS_SK_TERM_REC`` is bidirectional, so intros, inversion, and
#     structural induction all become routine downstream.
_pred_ty = parse_type("nat0 -> bool")
_F_pred_ty = parse_type("(nat0 -> bool) -> nat0 -> bool")


_IS_SK_TERM_F_DEF = define(
    "_is_sk_term_F",
    _F_pred_ty,
    "\\f:nat0->bool. \\n:nat0. "
    "n = S_t \\/ n = K_t \\/ "
    "(?a b. n = App_t a b /\\ f a /\\ f b)",
)
_IS_SK_TERM_F = mk_const("_is_sk_term_F", [])


@proof
def IS_SK_TERM_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
    ==> _is_sk_term_F f n = _is_sk_term_F g n.

    Monotonicity of the recursion body.  The S_t and K_t disjuncts
    don't mention f at all (REFL); only the App_t disjunct uses the
    size lemmas NAT0_LT_APP_T_L/R to recover f-eq at strictly-smaller
    arguments.
    """
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _is_sk_term_F f n = _is_sk_term_F g n",
        types={"f": _pred_ty, "g": _pred_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_S = REFL(p._parse("n = S_t"))
    eq_K = REFL(p._parse("n = K_t"))
    eq_app = mono_iff_binary_step(
        App_t, NAT0_LT_APP_T_L, NAT0_LT_APP_T_R, h_th
    )
    body_eq = or_chain_collapse([eq_S, eq_K, eq_app])

    p.thus("_is_sk_term_F f n = _is_sk_term_F g n").by_unfold(
        body_eq, _IS_SK_TERM_F_DEF
    )


IS_SK_TERM_DEF, _IS_SK_TERM_REC_RAW = define_wf_lt(
    "is_sk_term",
    _pred_ty,
    _IS_SK_TERM_F,
    IS_SK_TERM_MONO,
)
is_sk_term = mk_const("is_sk_term", [])


# IS_SK_TERM_REC : |- !n. is_sk_term n =
#                          n = S_t \/ n = K_t \/
#                          (?a b. n = App_t a b /\ is_sk_term a /\ is_sk_term b).
# The headline recursion equation; everything downstream is a SPEC away.
IS_SK_TERM_REC = _unfold_rec_via_F_def(_IS_SK_TERM_REC_RAW, _IS_SK_TERM_F_DEF)


@proof
def IS_SK_TERM_S(p):
    """|- is_sk_term S_t.  First-disjunct witness from IS_SK_TERM_REC."""
    p.goal("is_sk_term S_t")
    # Strategy: build the RHS-disjunction of IS_SK_TERM_REC at S_t via
    # DISJ1(REFL S_t), then EQ_MP via the (symmetric) specialized REC.
    spec = SPEC(S_t, IS_SK_TERM_REC)  # |- is_sk_term S_t = (S_t = S_t \/ ...)
    rhs_disj_th = DISJ1(REFL(S_t), p._parse(
        "S_t = K_t \\/ (?a b. S_t = App_t a b /\\ is_sk_term a /\\ is_sk_term b)"
    ))
    p.thus("is_sk_term S_t").by_eq_mp(spec, rhs_disj_th)


@proof
def IS_SK_TERM_K(p):
    """|- is_sk_term K_t.  Second-disjunct witness."""
    p.goal("is_sk_term K_t")
    spec = SPEC(K_t, IS_SK_TERM_REC)
    # K_t case: DISJ2 past ``K_t = S_t``, then DISJ1 on REFL K_t.
    inner = DISJ1(REFL(K_t), p._parse(
        "?a b. K_t = App_t a b /\\ is_sk_term a /\\ is_sk_term b"
    ))
    rhs_disj_th = DISJ2(p._parse("K_t = S_t"), inner)
    p.thus("is_sk_term K_t").by_eq_mp(spec, rhs_disj_th)


@proof
def IS_SK_TERM_APP(p):
    """|- !a b. is_sk_term a /\\ is_sk_term b ==> is_sk_term (App_t a b).

    Third-disjunct witness: build ``?a' b'. App_t a b = App_t a' b'
    /\\ is_sk_term a' /\\ is_sk_term b'`` by witnessing a' := a,
    b' := b with REFL.  Then chain through DISJ2 / DISJ2 and EQ_MP via
    REC.
    """
    from tactics import CONJ
    p.goal("!a b. is_sk_term a /\\ is_sk_term b ==> is_sk_term (App_t a b)")
    p.fix("a b")
    p.assume("(ha, hb): is_sk_term a /\\ is_sk_term b")
    # Use witness builders: the inner body is ``App_t a b = App_t a' b'
    # /\\ is_sk_term a' /\\ is_sk_term b'`` -- witness (a, b).
    # DSL friction: parser identifiers can't contain primes, so we use
    # x, y as the fresh bound names for the existential witnesses.
    p.have(
        "inner: ?x y. App_t a b = App_t x y /\\ "
        "       is_sk_term x /\\ is_sk_term y"
    ).by_exists(["a", "b"], "ha", "hb")
    p.have(
        "rhs: App_t a b = S_t \\/ App_t a b = K_t \\/ "
        "     (?x y. App_t a b = App_t x y /\\ "
        "      is_sk_term x /\\ is_sk_term y)"
    ).by_disj("inner")
    spec = SPEC(mk_app(App_t, p._parse("a"), p._parse("b")), IS_SK_TERM_REC)
    p.thus("is_sk_term (App_t a b)").by_eq_mp(spec, "rhs")


# IS_SK_TERM_CASES coincides with IS_SK_TERM_REC up to surface phrasing;
# we re-export under the historical name so downstream consumers find it.
IS_SK_TERM_CASES = IS_SK_TERM_REC


# Structural-intro registry: feed atoms (S_t, K_t) + the App-style
# recursive rule into the DSL so ``p.thus(...).by_tree(unfold=[...])``
# can discharge any concrete ``is_sk_term term`` goal without the
# IS_SK_TERM_APP cascade.
register_intro_set(
    is_sk_term,
    atoms=[(S_t, IS_SK_TERM_S), (K_t, IS_SK_TERM_K)],
    app=(App_t, IS_SK_TERM_APP),
)


# ---------------------------------------------------------------------------
# Stage 1 -- constructor injectivity and disjointness.
#
# Three lemmas we need for the head-redex reductions and the normal-form
# proofs:
#   APP_T_INJ    -- !a1 b1 a2 b2. App_t a1 b1 = App_t a2 b2
#                                   ==> a1 = a2 /\ b1 = b2.
#   S_T_NEQ_K_T  -- ~(S_t = K_t).
#   S_T_NEQ_APP_T, K_T_NEQ_APP_T -- !x y. ~(S_t = App_t x y),
#                                   !x y. ~(K_t = App_t x y).
#
# Tags: S_t = Pair_ord 0 0, K_t = Pair_ord 1 0, App_t a b =
# Pair_ord 2 (Pair_ord a b).  Disjointness is therefore one
# PAIR_ORD_INJ at slot 0 plus a tag-numeral inequality (cf.
# ``hf_syntax._TAG_NEQS``).
# ---------------------------------------------------------------------------


from hf_syntax import _proof_binary_inj, _TAG_NEQS  # noqa: E402
from hf_sets import PAIR_ORD_INJ  # noqa: E402
from tactics import CONJUNCT1  # noqa: E402


APP_T_INJ = _proof_binary_inj(
    "APP_T_INJ", "a1", "b1", "a2", "b2", "App_t", APP_T_AT, _APP_T_TAG
)


@proof
def S_T_NEQ_K_T(p):
    """|- ~(S_t = K_t).

    S_t = Pair_ord 0 0, K_t = Pair_ord (SUC0 0) 0; PAIR_ORD_INJ at slot
    0 reduces ``S_t = K_t`` to ``0 = SUC0 0``, contradicting AXIOM_3_0
    (packaged here as _TAG_NEQS[(0, 1)]).
    """
    p.goal("~(S_t = K_t)")
    with p.suppose("h: S_t = K_t"):
        # Rewrite via the definitions to expose the Pair_ord shape.
        p.have("h_po: Pair_ord 0 0 = Pair_ord (SUC0 0) 0").by_rewrite_of(
            "h", [S_T_DEF, K_T_DEF]
        )
        p.have("h_inj: 0 = SUC0 0 /\\ 0 = 0").by(
            PAIR_ORD_INJ, "0", "0", "SUC0 0", "0", "h_po"
        )
        p.have("h_tag: 0 = SUC0 0").by_thm(CONJUNCT1(p.fact("h_inj")))
        p.have("h_neg: ~(0 = SUC0 0)").by_thm(_TAG_NEQS[(0, 1)])
        p.absurd().by_conj("h_neg", "h_tag")


def _proof_atom_neq_app_t(thm_name, atom_const, atom_def, atom_tag_str, atom_tag_idx):
    """Build ``|- !x y. ~(atom = App_t x y)`` for atom in {S_t, K_t}."""

    @proof
    def _THM(p):
        from tactics import SPECL

        p.goal(f"!x y. ~({atom_const} = App_t x y)")
        p.fix("x y")
        with p.suppose(f"h: {atom_const} = App_t x y"):
            app_inst = SPECL([p._parse("x"), p._parse("y")], APP_T_AT)
            # ``atom = Pair_ord atom_tag 0`` from its definition (which is
            # itself a Pair_ord-application; pyzar's S_T_DEF / K_T_DEF
            # read in reverse).
            p.have(
                f"h_po: Pair_ord ({atom_tag_str}) 0 = "
                f"       Pair_ord (SUC0 (SUC0 0)) (Pair_ord x y)"
            ).by_rewrite_of("h", [atom_def, app_inst])
            p.have(
                f"h_inj: ({atom_tag_str}) = SUC0 (SUC0 0) /\\ 0 = Pair_ord x y"
            ).by(
                PAIR_ORD_INJ,
                f"({atom_tag_str})",
                "0",
                "SUC0 (SUC0 0)",
                "Pair_ord x y",
                "h_po",
            )
            p.have(f"h_tag: ({atom_tag_str}) = SUC0 (SUC0 0)").by_thm(
                CONJUNCT1(p.fact("h_inj"))
            )
            p.have(f"h_neg: ~(({atom_tag_str}) = SUC0 (SUC0 0))").by_thm(
                _TAG_NEQS[(atom_tag_idx, 2)]
            )
            p.absurd().by_conj("h_neg", "h_tag")

    return _THM


S_T_NEQ_APP_T = _proof_atom_neq_app_t("S_T_NEQ_APP_T", "S_t", S_T_DEF, "0", 0)
K_T_NEQ_APP_T = _proof_atom_neq_app_t("K_T_NEQ_APP_T", "K_t", K_T_DEF, "SUC0 0", 1)


# ---------------------------------------------------------------------------
# DSL helper: discharge ``~(?bv1...bvn. LHS = RHS)`` by head-tag clash.
#
# LHS must be concrete over {S_t, K_t, App_t}; RHS may mention the
# existentially bound variables (which can pattern-match anything).
# The helper walks LHS/RHS in parallel, finds the first APP_T_INJ-
# descent path leading to a clashing pair, and emits the
# choose+inj+absurd chain.  Three clash kinds:
#
#   atom-atom   (e.g. S_t vs K_t)              -- closed by S_T_NEQ_K_T
#   atom-App_t  (e.g. S_t vs App_t _ _)        -- closed by S_T_NEQ_APP_T
#                                                 or K_T_NEQ_APP_T
#   App_t-atom  (sym of the above)             -- SYM + S_T_NEQ_APP_T
#                                                 or K_T_NEQ_APP_T
#
# Without this helper each negation in IS_NORMAL_I_T / HALTS_K_OMEGA_FALSE
# / DIAG_TERM cost ~20 lines of suppose+choose+APP_T_INJ+CONJUNCT
# boilerplate; with it they become one-liners.
# ---------------------------------------------------------------------------


def _split_app_t(t):
    """Split ``App_t a b`` (i.e. ``Comb(Comb(App_t, a), b)``) into
    ``(a, b)``; return ``(None, None)`` if ``t`` isn't an App_t-Comb.
    """
    from basics import is_comb, is_const
    if not is_comb(t):
        return None, None
    head, R = t.fun, t.arg
    if not is_comb(head):
        return None, None
    op, L = head.fun, head.arg
    if is_const(op) and op.name == "App_t":
        return L, R
    return None, None


_ATOM_NAMES = {"S_t", "K_t"}


def _find_shape_clash(lhs, rhs, bvar_set):
    """Walk lhs/rhs in parallel.  Return a list of descents
    (``"L"`` / ``"R"``) ending in a clash kind, or ``None`` if no
    structural clash exists (e.g. rhs is a bvar at the conflict
    site, allowing the existential to match).

    Clash kinds at the leaf: ``"atom_atom"``, ``"atom_app"``,
    ``"app_atom"``.
    """
    from basics import is_const, is_var
    if is_var(rhs) and rhs.name in bvar_set:
        return None  # rhs side is unconstrained here
    lhs_atom = is_const(lhs) and lhs.name in _ATOM_NAMES
    rhs_atom = is_const(rhs) and rhs.name in _ATOM_NAMES
    if lhs_atom and rhs_atom:
        if lhs.name == rhs.name:
            return None
        return [("clash", "atom_atom")]
    if lhs_atom:
        rL, rR = _split_app_t(rhs)
        if rL is None:
            return None
        return [("clash", "atom_app")]
    if rhs_atom:
        lL, lR = _split_app_t(lhs)
        if lL is None:
            return None
        return [("clash", "app_atom")]
    lL, lR = _split_app_t(lhs)
    rL, rR = _split_app_t(rhs)
    if lL is None or rL is None:
        return None
    left = _find_shape_clash(lL, rL, bvar_set)
    if left is not None:
        return [("L",)] + left
    right = _find_shape_clash(lR, rR, bvar_set)
    if right is not None:
        return [("R",)] + right
    return None


def _atom_neq_app_t_thm(atom):
    """Return the ``atom ≠ App_t _ _`` lemma for ``atom``
    (must be ``S_t`` or ``K_t``).
    """
    if atom.name == "S_t":
        return S_T_NEQ_APP_T
    if atom.name == "K_t":
        return K_T_NEQ_APP_T
    from fusion import HolError
    raise HolError(f"_atom_neq_app_t_thm: no neq lemma for atom {atom.name}")


def shape_neq(p, label, neg_term_str):
    """Register ``label`` proving ``~(?v1...vn. LHS = RHS)`` via
    head-tag clash detection.

    ``LHS`` must be a concrete term over ``{S_t, K_t, App_t}``;
    ``RHS`` may mention the existentially bound variables.  Walks
    both kernel terms in parallel; finds the first L/R-descent path
    through ``APP_T_INJ`` leading to a clashing pair (atom-atom,
    atom-App_t, or App_t-atom); emits the corresponding
    ``suppose``+``choose``+``APP_T_INJ``+absurd chain.

    Raises if no structural clash exists (so e.g. tautological
    negations fail loudly).
    """
    from tactics import CONJUNCT1 as _C1, CONJUNCT2 as _C2
    from basics import is_const, is_comb, is_abs, dest_const
    from axioms import dest_neg
    from fusion import HolError

    neg_tm = p._parse(neg_term_str)
    body = dest_neg(neg_tm)
    # Strip existentials, collecting bvar names.
    bvar_names = []
    cur = body
    while is_comb(cur) and is_const(cur.fun) and cur.fun.name == "?" and is_abs(cur.arg):
        bvar_names.append(cur.arg.bvar.name)
        cur = cur.arg.body
    lhs, rhs = dest_eq(cur)
    bvar_set = set(bvar_names)

    path = _find_shape_clash(lhs, rhs, bvar_set)
    if path is None:
        raise HolError(
            f"shape_neq: no head-tag clash found in {neg_term_str}"
        )

    # Open: with p.have(label).proof(): with p.suppose("h: <body>"):
    body_str = pp(body)
    with p.have(f"{label}: {pp(neg_tm)}").proof():
        with p.suppose(f"_sn_h: {body_str}"):
            # Chain choose's for every bound variable.
            cur_eq_label = "_sn_h"
            for name in bvar_names:
                p.choose(name, from_=cur_eq_label)
                cur_eq_label = f"{name}_eq"
            # Walk path emitting APP_T_INJ + CONJUNCT.
            cur_lhs, cur_rhs = lhs, rhs
            for i, step in enumerate(path[:-1]):
                lL, lR = _split_app_t(cur_lhs)
                rL, rR = _split_app_t(cur_rhs)
                pair_label = f"_sn_p{i}"
                p.have(
                    f"{pair_label}: {pp(lL)} = {pp(rL)} /\\ "
                    f"{pp(lR)} = {pp(rR)}"
                ).by(
                    APP_T_INJ, pp(lL), pp(lR), pp(rL), pp(rR), cur_eq_label
                )
                pick_label = f"_sn_e{i}"
                if step[0] == "L":
                    p.have(f"{pick_label}: {pp(lL)} = {pp(rL)}").by_thm(
                        _C1(p.fact(pair_label))
                    )
                    cur_lhs, cur_rhs = lL, rL
                else:
                    p.have(f"{pick_label}: {pp(lR)} = {pp(rR)}").by_thm(
                        _C2(p.fact(pair_label))
                    )
                    cur_lhs, cur_rhs = lR, rR
                cur_eq_label = pick_label

            # Leaf clash.
            _, kind = path[-1]
            if kind == "atom_atom":
                # cur_lhs, cur_rhs are S_t / K_t (different).  Only one
                # such pair exists; use S_T_NEQ_K_T (oriented S_t = K_t).
                if cur_lhs.name == "S_t":
                    # cur_lhs = cur_rhs is literally S_t = K_t.
                    p.absurd().by_conj(S_T_NEQ_K_T, cur_eq_label)
                else:
                    # K_t = S_t; flip.
                    p.have(f"_sn_sym: S_t = K_t").by_thm(SYM(p.fact(cur_eq_label)))
                    p.absurd().by_conj(S_T_NEQ_K_T, "_sn_sym")
            elif kind == "atom_app":
                # cur_lhs (atom) = cur_rhs (App_t r1 r2).
                rL, rR = _split_app_t(cur_rhs)
                neq_lemma = _atom_neq_app_t_thm(cur_lhs)
                p.have(
                    f"_sn_neg: ~({pp(cur_lhs)} = App_t ({pp(rL)}) ({pp(rR)}))"
                ).by(neq_lemma, pp(rL), pp(rR))
                p.absurd().by_conj("_sn_neg", cur_eq_label)
            else:  # "app_atom"
                # cur_lhs (App_t l1 l2) = cur_rhs (atom).
                lL, lR = _split_app_t(cur_lhs)
                neq_lemma = _atom_neq_app_t_thm(cur_rhs)
                p.have(
                    f"_sn_neg: ~({pp(cur_rhs)} = App_t ({pp(lL)}) ({pp(lR)}))"
                ).by(neq_lemma, pp(lL), pp(lR))
                p.have(
                    f"_sn_sym: {pp(cur_rhs)} = App_t ({pp(lL)}) ({pp(lR)})"
                ).by_thm(SYM(p.fact(cur_eq_label)))
                p.absurd().by_conj("_sn_neg", "_sn_sym")


# ---------------------------------------------------------------------------
# Stage 1 -- one-step reduction with leftmost-outermost congruence.
#
# Strategy: fire a K- or S- redex at the leftmost-outermost position.
# When the top is not a redex but is an App_t, descend into the LEFT
# child; if the left is a fixed point, descend into the RIGHT.  Leaves
# (S_t, K_t) and "fully normal" terms are unchanged.
#
# This is a wf-recursive function on the nat0 encoding (subterms are
# strictly smaller nat0s by NAT0_LT_APP_T_L/R), defined via
# ``define_wf_lt`` over a SELECT-shaped functional body.
#
#   _sk_step_F f t  :=  @r.
#     (?x y. t = App_t (App_t K_t x) y /\ r = x)                       -- K-redex
#     \/ (~K /\ ?x y z. t = App_t (App_t (App_t S_t x) y) z /\
#                       r = App_t (App_t x z) (App_t y z))             -- S-redex
#     \/ (~K /\ ~S /\ ?a b. t = App_t a b /\
#          ((~(f a = a) /\ r = App_t (f a) b)                          -- descend L
#           \/ (f a = a /\ ~(f b = b) /\ r = App_t a (f b))             -- descend R
#           \/ (f a = a /\ f b = b /\ r = t)))                          -- App fixed
#     \/ (~K /\ ~S /\ ~(?a b. t = App_t a b) /\ r = t)                  -- leaf fixed
#
# The guards make the disjunction functional (mutually exclusive by
# construction), so the SELECT picks the unique satisfying ``r``.
#
# DSL friction: ``define_wf_lt`` doesn't accept a SELECT-shaped body
# directly -- the monotonicity proof has to dive under ``@r.`` and
# show pointwise body-equality, then lift via AP_TERM Eps.  No
# pre-built helper here (the existing ``mono_iff_*`` family targets
# top-level disjunctions of constructor-existentials, not nested
# SELECT predicates), so SK_STEP_MONO is hand-rolled.
_sk_step_fn_ty = parse_type("nat0 -> nat0")
_F_sk_step_ty = parse_type("(nat0 -> nat0) -> nat0 -> nat0")


_SK_STEP_F_DEF = define(
    "_sk_step_F",
    _F_sk_step_ty,
    "\\f:nat0->nat0. \\t:nat0. "
    "@r:nat0. "
    "(?x y. t = App_t (App_t K_t x) y /\\ r = x) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ?x y z. t = App_t (App_t (App_t S_t x) y) z /\\ "
    "         r = App_t (App_t x z) (App_t y z)) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " (?a b. t = App_t a b /\\ "
    "        ((~(f a = a) /\\ r = App_t (f a) b) \\/ "
    "         (f a = a /\\ ~(f b = b) /\\ r = App_t a (f b)) \\/ "
    "         (f a = a /\\ f b = b /\\ r = t)))) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " ~(?a b. t = App_t a b) /\\ r = t)",
)
_SK_STEP_F = mk_const("_sk_step_F", [])


def _prove_sk_step_F_at():
    """|- !f t. _sk_step_F f t = body[f, t]  (two BETAs)."""
    from tactics import AP_THM, BETA_CONV, TRANS, GENL
    f_var = Var("f", _sk_step_fn_ty)
    t_var = Var("t", nat0_ty)
    th_f = AP_THM(_SK_STEP_F_DEF, f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_ft = AP_THM(th_f_eq, t_var)
    th_ft_eq = TRANS(th_ft, BETA_CONV(rand(th_ft._concl)))
    return GENL([f_var, t_var], th_ft_eq)


_SK_STEP_F_AT = _prove_sk_step_F_at()


def _lift_select_eq(r_var, pw_eq_th):
    """Given ``|- P r = Q r`` with ``r`` free (and not in hypotheses),
    return ``|- (@r. P r) = (@r. Q r)``.

    Two-step lift: ``ABS`` over ``r`` to land on
    ``(\\r. P r) = (\\r. Q r)``, then ``AP_TERM`` the polymorphic ``@``
    constant instantiated at ``r``'s type.  Generic enough to promote
    to ``tactics.py`` if more SELECT-recursive definitions arrive.
    """
    from tactics import AP_TERM as _AP_TERM
    from fusion import ABS as _ABS, aty as _aty
    abs_eq = _ABS(r_var, pw_eq_th)
    eps_const = mk_const("@", [(r_var.ty, _aty)])
    return _AP_TERM(eps_const, abs_eq)


@proof
def SK_STEP_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                 ==> _sk_step_F f n = _sk_step_F g n.

    Body is ``@r. D1 \\/ D2 \\/ D3 \\/ D4``:
      D1 (K-redex), D2 (~K /\\ S-redex), D4 (~K /\\ ~S /\\ ~App /\\ r=t)
        are f-free; REFL each.
      D3 (~K /\\ ~S /\\ ?a b. n = App_t a b /\\ inner) uses ``f a`` and
        ``f b``; for ``a, b < n`` (NAT0_LT_APP_T_L/R) the IH gives
        ``f a = g a`` / ``f b = g b``.  Handled by
        ``_mono_iff_value_binary_pw_step``.

    Stitch per-disjunct iffs via ``or_chain_collapse``; lift through
    the SELECT via ``_lift_select_eq``; chain through the two
    SPECL'd ``_SK_STEP_F_AT`` equations.
    """
    from tactics import (
        AP_TERM as _AP_TERM,
        SPECL as _SPECL,
        TRANS as _TRANS,
        SYM as _SYM,
        or_chain_collapse as _or_collapse,
    )
    from hf_syntax import _mono_iff_value_binary_pw_step, _extract_nfg
    from fusion import mk_comb as _mk_comb
    from axioms import (
        mk_and as _mk_and, mk_or as _mk_or, mk_not as _mk_not,
        mk_exists as _mk_exists,
    )
    from basics import mk_eq as _mk_eq

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _sk_step_F f n = _sk_step_F g n",
        types={
            "f": _sk_step_fn_ty,
            "g": _sk_step_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")
    n_t, f_t, g_t, k_ty = _extract_nfg(h_th)
    r_var = Var("r", nat0_ty)

    # ---- Build the 4 disjuncts at fresh r, sharing structure -------------
    # K-shape, S-shape, App-shape (used in negations and as targets).
    x_v = Var("x", nat0_ty)
    y_v = Var("y", nat0_ty)
    z_v = Var("z", nat0_ty)
    a_v = Var("a", nat0_ty)
    b_v = Var("b", nat0_ty)
    K_redex_body = _mk_eq(
        n_t, mk_app(App_t, mk_app(App_t, K_t, x_v), y_v)
    )
    K_shape = _mk_exists(x_v, _mk_exists(y_v, K_redex_body))
    S_redex_body = _mk_eq(
        n_t,
        mk_app(App_t, mk_app(App_t, mk_app(App_t, S_t, x_v), y_v), z_v),
    )
    S_shape = _mk_exists(x_v, _mk_exists(y_v, _mk_exists(z_v, S_redex_body)))
    App_body = _mk_eq(n_t, mk_app(App_t, a_v, b_v))
    App_shape = _mk_exists(a_v, _mk_exists(b_v, App_body))

    # D1: ?x y. n = App_t (App_t K_t x) y /\ r = x
    D1 = _mk_exists(
        x_v,
        _mk_exists(
            y_v,
            _mk_and(K_redex_body, _mk_eq(r_var, x_v)),
        ),
    )
    # D2: ~K /\ ?x y z. n = App_t (App_t (App_t S_t x) y) z /\ r = App_t (App_t x z) (App_t y z)
    S_reduct_val = mk_app(
        App_t,
        mk_app(App_t, x_v, z_v),
        mk_app(App_t, y_v, z_v),
    )
    D2 = _mk_and(
        _mk_not(K_shape),
        _mk_exists(
            x_v,
            _mk_exists(
                y_v,
                _mk_exists(
                    z_v,
                    _mk_and(S_redex_body, _mk_eq(r_var, S_reduct_val)),
                ),
            ),
        ),
    )
    # D3 (built from the rest_builder via the helper).
    # D4: ~K /\ ~S /\ ~App /\ r = n
    D4 = _mk_and(
        _mk_not(K_shape),
        _mk_and(
            _mk_not(S_shape),
            _mk_and(_mk_not(App_shape), _mk_eq(r_var, n_t)),
        ),
    )

    # ---- Per-disjunct iffs -----------------------------------------------
    eq_D1 = REFL(D1)
    eq_D2 = REFL(D2)
    eq_D4 = REFL(D4)

    # _mono_iff_value_binary_pw_step's ``args`` are extra arguments
    # applied AFTER the recursive call ``f w`` -- for our case
    # ``f : nat0 -> nat0`` the recursive call is already complete at
    # ``f a`` / ``f b``, so ``args=[]``.  ``r_var`` is captured by
    # closure rather than threaded as an arg.
    def _D3_rest_builder(fn, a, b, args):
        fn_a = mk_app(fn, a)
        fn_b = mk_app(fn, b)
        da = _mk_and(
            _mk_not(_mk_eq(fn_a, a)),
            _mk_eq(r_var, mk_app(App_t, fn_a, b)),
        )
        db = _mk_and(
            _mk_eq(fn_a, a),
            _mk_and(
                _mk_not(_mk_eq(fn_b, b)),
                _mk_eq(r_var, mk_app(App_t, a, fn_b)),
            ),
        )
        dc = _mk_and(
            _mk_eq(fn_a, a),
            _mk_and(_mk_eq(fn_b, b), _mk_eq(r_var, n_t)),
        )
        return _mk_or(da, _mk_or(db, dc))

    eq_D3_inner = _mono_iff_value_binary_pw_step(
        App_t,
        NAT0_LT_APP_T_L, NAT0_LT_APP_T_R,
        h_th,
        args=[],
        rest_builder=_D3_rest_builder,
        recurses_l=True,
    )
    # |- (?a b. n = App_t a b /\ rest_f) = (?a b. n = App_t a b /\ rest_g)

    # Prefix ~S, then ~K via partial-application AP_TERM on /\.
    AND_C = mk_const("/\\", [])
    eq_D3_with_ns = _AP_TERM(_mk_comb(AND_C, _mk_not(S_shape)), eq_D3_inner)
    eq_D3 = _AP_TERM(_mk_comb(AND_C, _mk_not(K_shape)), eq_D3_with_ns)

    # ---- Stitch via or_chain_collapse ------------------------------------
    body_eq_at_r = _or_collapse([eq_D1, eq_D2, eq_D3, eq_D4])
    # |- body[f, n, r] = body[g, n, r]   (r free)

    # ---- Lift through SELECT and chain through _SK_STEP_F_AT -------------
    select_eq = _lift_select_eq(r_var, body_eq_at_r)
    spec_f = _SPECL([f_t, n_t], _SK_STEP_F_AT)
    spec_g = _SPECL([g_t, n_t], _SK_STEP_F_AT)
    final = _TRANS(spec_f, _TRANS(select_eq, _SYM(spec_g)))

    p.thus("_sk_step_F f n = _sk_step_F g n").by_thm(final)


# Well-founded recursive definition.
#   SK_STEP_DEF      : |- sk_step = (@h. !n. h n = _sk_step_F h n)
#   _SK_STEP_REC_RAW : |- !n. sk_step n = _sk_step_F sk_step n
SK_STEP_DEF, _SK_STEP_REC_RAW = define_wf_lt(
    "sk_step",
    _sk_step_fn_ty,
    _SK_STEP_F,
    SK_STEP_MONO,
)
sk_step = mk_const("sk_step", [])


# SK_STEP_REC : |- !n. sk_step n = body[sk_step, n]
# (the un-helpered RHS, ready for case-splits).
SK_STEP_REC = _unfold_rec_via_F_def(_SK_STEP_REC_RAW, _SK_STEP_F_DEF)


# ``is_normal`` is *defined* as the fixed-point condition of sk_step.
# Under leftmost-outermost congruence reduction this is equivalent to
# "no redex anywhere in t".  Making it the definition collapses
# IS_NORMAL_IMP_FIXED and IS_NORMAL_CASES to direct unfolds.
IS_NORMAL_DEF = define(
    "is_normal",
    parse_type("nat0 -> bool"),
    "\\t:nat0. sk_step t = t",
)
is_normal = mk_const("is_normal", [])


# ---------------------------------------------------------------------------
# DSL helpers for the SK_STEP_REC case-split pattern.  Without these,
# each of SK_STEP_K / SK_STEP_S / SK_STEP_LEAF_S / SK_STEP_LEAF_K
# has to spell the 4-disjunct body verbatim at three sites (existence
# witness, post-select body fact, each case spec), which is ~150 lines
# per proof.

def _select_via_rec(rec_th, args, ex_th):
    """Like ``by_select_def``, but works with a REC-shape equation
    ``|- !n. f n = @r. body[f, n, r]`` instead of a direct lambda def.

    Returns ``|- body[f, args, f args]`` (the body with the SELECT
    substituted out for ``f`` at the given args).
    """
    from tactics import REWRITE_RULE, CHOOSE_WITNESS, SYM as _SYM, SPECL as _SPECL
    from axioms import dest_exists as _dest_ex
    if not isinstance(args, (list, tuple)):
        args = [args]
    spec = _SPECL(args, rec_th)  # |- f args = @r. body[f, args, r]
    pred = _dest_ex(ex_th._concl)
    if pred is None:
        raise ValueError("_select_via_rec: ex_th is not existential")
    chosen = CHOOSE_WITNESS(pred, ex_th)  # |- body[f, args, @r. body]
    return REWRITE_RULE([_SYM(spec)], chosen)


def _sk_step_disjuncts(t, r):
    """Return the four disjunct strings of the ``_sk_step_F`` body
    applied at input ``t``, with the SELECT-bound variable substituted
    by ``r`` (literal ``"r"`` for the existence witness; ``"sk_step
    (<t>)"`` for the post-select body and case specs).

    Existential bound names are ``a, b, c`` (renamed from the
    definition's ``x, y, z`` so they don't shadow caller-free vars
    like ``x, y, z`` from the outer goal).
    """
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    App_shape = f"?a b. {t} = App_t a b"
    D1 = f"(?a b. {t} = App_t (App_t K_t a) b /\\ {r} = a)"
    D2 = (
        f"(~({K_shape}) /\\ "
        f" ?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"         {r} = App_t (App_t a c) (App_t b c))"
    )
    D3_inner = (
        f"((~(sk_step a = a) /\\ {r} = App_t (sk_step a) b) \\/ "
        f" (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"  {r} = App_t a (sk_step b)) \\/ "
        f" (sk_step a = a /\\ sk_step b = b /\\ {r} = {t}))"
    )
    D3 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ "
        f" (?a b. {t} = App_t a b /\\ {D3_inner}))"
    )
    D4 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ ~({App_shape}) /\\ "
        f" {r} = {t})"
    )
    return [D1, D2, D3, D4]


def _sk_step_body(t, r):
    return " \\/ ".join(_sk_step_disjuncts(t, r))


def _sk_step_select_at(p, t, witness_r, inner_branch_th):
    """Build the body-at-sk_step fact for input ``t``.

    Combines:
      1. ``ex: ?r. body[t, r]``      (existence witness via inner_branch_th + by_disj)
      2. ``_select_via_rec``         (fold SELECT to ``sk_step t``)

    Args:
      t                : input term, as a string.
      witness_r        : the ``r``-value to witness with, as a string.
      inner_branch_th  : a fact label or theorem proving the firing
                         disjunct's body at ``r := witness_r``.

    The caller registers ``inner_branch_th`` as a fact in scope
    (e.g. ``p.have("inner_K: ?a b. t = App_t (App_t K_t a) b /\\ r0 = a")``
    with ``r0 = witness_r``).  This helper DISJ-chains it into the
    full 4-disjunct shape, EXISTS-introduces ``r``, and feeds to
    ``_select_via_rec``.

    Returns the kernel theorem ``|- body[t, sk_step t]``.
    """
    body_at_r = _sk_step_body(t, witness_r)
    body_at_r_var = _sk_step_body(t, "r")
    p.have(f"_step_disj_rhs: {body_at_r}").by_disj(inner_branch_th)
    p.have(f"_step_ex: ?r. {body_at_r_var}").by_witness(witness_r, "_step_disj_rhs")
    return _select_via_rec(SK_STEP_REC, [p._parse(t)], p.fact("_step_ex"))


@proof
def SK_STEP_K(p):
    """|- !x y. sk_step (App_t (App_t K_t x) y) = x.

    K-redex disjunct of the 4-disjunct body fires at ``r := x``;
    APP_T_INJ chain identifies the K-redex's bound ``a`` with our
    ``x``.  The S-, App-, and leaf-branches all carry ``~K`` and are
    refuted via the obvious K-redex existence of the input.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal("!x y. sk_step (App_t (App_t K_t x) y) = x")
    p.fix("x y")
    t = "App_t (App_t K_t x) y"
    sk_t = f"sk_step ({t})"
    # K-disjunct witness at r := x: ?a b. t = App_t (App_t K_t a) b /\ x = a.
    p.have(
        f"inner_K: ?a b. {t} = App_t (App_t K_t a) b /\\ x = a"
    ).by_exists(
        ["x", "y"], REFL(p._parse(t)), REFL(p._parse("x"))
    )
    body_th = _sk_step_select_at(p, t, "x", "inner_K")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)
    # K-redex existence at the input; refutes ~K guards in cases 2-4.
    p.have(f"is_kred: ?a b. {t} = App_t (App_t K_t a) b").by_exists(
        ["x", "y"], REFL(p._parse(t))
    )
    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_sk)")
            p.have(
                "h_o: App_t K_t x = App_t K_t a /\\ y = b"
            ).by(APP_T_INJ, "App_t K_t x", "y", "App_t K_t a", "b", "h_app")
            p.have("h_o1: App_t K_t x = App_t K_t a").by_thm(_C1(p.fact("h_o")))
            p.have("h_i: K_t = K_t /\\ x = a").by(
                APP_T_INJ, "K_t", "x", "K_t", "a", "h_o1"
            )
            p.have("h_xa: x = a").by_thm(_C2(p.fact("h_i")))
            p.thus(f"{sk_t} = x").by_rewrite_of("h_sk", [SYM(p.fact("h_xa"))])
        with p.case(f"h2: {D2}"):
            p.split("h2", "(h_nk, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(h_nk, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(h_nk, _, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")


@proof
def SK_STEP_S(p):
    """|- !x y z. sk_step (App_t (App_t (App_t S_t x) y) z)
                  = App_t (App_t x z) (App_t y z).

    S-redex disjunct (index 1, guarded by ``~K``) fires at the natural
    witness; refute K-branch via ``not_kred`` (APP_T_INJ chain shows
    an S-input can't unify with a K-redex shape); refute App-rec and
    leaf branches via the obvious S-redex existence of the input.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!x y z. sk_step (App_t (App_t (App_t S_t x) y) z) "
        "         = App_t (App_t x z) (App_t y z)"
    )
    p.fix("x y z")
    t = "App_t (App_t (App_t S_t x) y) z"
    sk_t = f"sk_step ({t})"
    val = "App_t (App_t x z) (App_t y z)"

    # not_kred: ~(?a b. t = App_t (App_t K_t a) b).  S-input has head
    # S_t, not K_t; tag clash via K_T_NEQ_APP_T after two APP_T_INJ peels.
    with p.have(
        f"not_kred: ~(?a b. {t} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex_kred: ?a b. {t} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex_kred")
            p.choose("b", from_="a_eq")
            p.have(
                "h_o: App_t (App_t S_t x) y = App_t K_t a /\\ z = b"
            ).by(APP_T_INJ, "App_t (App_t S_t x) y", "z",
                 "App_t K_t a", "b", "b_eq")
            p.have("h_o1: App_t (App_t S_t x) y = App_t K_t a").by_thm(
                _C1(p.fact("h_o"))
            )
            p.have("h_m: App_t S_t x = K_t /\\ y = a").by(
                APP_T_INJ, "App_t S_t x", "y", "K_t", "a", "h_o1"
            )
            p.have("ASx_eq_K: App_t S_t x = K_t").by_thm(_C1(p.fact("h_m")))
            p.have("K_neq: ~(K_t = App_t S_t x)").by(K_T_NEQ_APP_T, "S_t", "x")
            p.have("K_eq: K_t = App_t S_t x").by_thm(SYM(p.fact("ASx_eq_K")))
            p.absurd().by_conj("K_neq", "K_eq")

    # S-disjunct inner witness at r := val.
    p.have(
        f"inner_S_inner: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"                       {val} = App_t (App_t a c) (App_t b c)"
    ).by_exists(
        ["x", "y", "z"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    p.have(
        f"inner_S: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f" (?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"          {val} = App_t (App_t a c) (App_t b c))"
    ).by_thm(_CONJ(p.fact("not_kred"), p.fact("inner_S_inner")))
    body_th = _sk_step_select_at(p, t, val, "inner_S")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)

    # is_sred: refutes ~S guards in branches 3, 4.
    p.have(
        f"is_sred: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    ).by_exists(["x", "y", "z"], REFL(p._parse(t)))

    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # K-branch on S-input: extract a, b and contradict not_kred.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, h_sk)")
            # h_app: t = App_t (App_t (App_t S_t a) b) c.  Three APP_T_INJ peels
            # identify x = a, y = b, z = c.
            p.have(
                "h_o: App_t (App_t S_t x) y = App_t (App_t S_t a) b /\\ z = c"
            ).by(APP_T_INJ, "App_t (App_t S_t x) y", "z",
                 "App_t (App_t S_t a) b", "c", "h_app")
            p.have("h_o1: App_t (App_t S_t x) y = App_t (App_t S_t a) b").by_thm(
                _C1(p.fact("h_o"))
            )
            p.have("h_zc: z = c").by_thm(_C2(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t x = App_t S_t a /\\ y = b"
            ).by(APP_T_INJ, "App_t S_t x", "y", "App_t S_t a", "b", "h_o1")
            p.have("h_m1: App_t S_t x = App_t S_t a").by_thm(_C1(p.fact("h_m")))
            p.have("h_yb: y = b").by_thm(_C2(p.fact("h_m")))
            p.have(
                "h_i: S_t = S_t /\\ x = a"
            ).by(APP_T_INJ, "S_t", "x", "S_t", "a", "h_m1")
            p.have("h_xa: x = a").by_thm(_C2(p.fact("h_i")))
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_xa")), SYM(p.fact("h_yb")), SYM(p.fact("h_zc"))],
            )
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, h_ns, _)")
            p.absurd().by_conj("h_ns", "is_sred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, h_ns, _, _)")
            p.absurd().by_conj("h_ns", "is_sred")


@proof
def SK_STEP_LEFT(p):
    """|- !u v.
            ~(?a b. App_t u v = App_t (App_t K_t a) b)
            ==> ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)
            ==> ~(sk_step u = u)
            ==> sk_step (App_t u v) = App_t (sk_step u) v.

    Descend-left congruence: when the outer App is neither a K- nor an
    S-redex and the left child is non-normal, sk_step descends into the
    left.  D3 (App-recurse) of the 4-disjunct body fires at the
    descend-left sub-disjunct with witness (a, b) := (u, v); the
    sub-disjunct's ``~(sk_step a = a)`` premise is exactly our third
    hypothesis.  D1/D2 contradict the first two hypotheses, D4 the
    obvious fact that ``App_t u v`` is an App.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!u v. ~(?a b. App_t u v = App_t (App_t K_t a) b) ==> "
        "      ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c) ==> "
        "      ~(sk_step u = u) ==> "
        "      sk_step (App_t u v) = App_t (sk_step u) v"
    )
    p.fix("u v")
    p.assume("not_kred: ~(?a b. App_t u v = App_t (App_t K_t a) b)")
    p.assume("not_sred: ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)")
    p.assume("not_norm_u: ~(sk_step u = u)")

    t = "App_t u v"
    sk_t = f"sk_step ({t})"
    val = "App_t (sk_step u) v"
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"

    # Build the descend-left D3-inner witness, at (a, b) := (u, v), r := val.
    # Sub-disjunct 1: ~(sk_step u = u) /\ val = App_t (sk_step u) v.
    p.have(
        f"sub1: ~(sk_step u = u) /\\ {val} = App_t (sk_step u) v"
    ).by_thm(_CONJ(p.fact("not_norm_u"), REFL(p._parse(val))))
    triple_at_uv = (
        f"(~(sk_step u = u) /\\ {val} = App_t (sk_step u) v) \\/ "
        f"(sk_step u = u /\\ ~(sk_step v = v) /\\ "
        f" {val} = App_t u (sk_step v)) \\/ "
        f"(sk_step u = u /\\ sk_step v = v /\\ {val} = {t})"
    )
    p.have(f"triple_uv: {triple_at_uv}").by_disj("sub1")
    inner_ex = (
        f"?a b. {t} = App_t a b /\\ "
        f"((~(sk_step a = a) /\\ {val} = App_t (sk_step a) b) \\/ "
        f" (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"  {val} = App_t a (sk_step b)) \\/ "
        f" (sk_step a = a /\\ sk_step b = b /\\ {val} = {t}))"
    )
    p.have(f"inner_ex: {inner_ex}").by_exists(["u", "v"], "triple_uv")
    p.have(
        f"inner_d3: ~({K_shape}) /\\ ~({S_shape}) /\\ ({inner_ex})"
    ).by_thm(
        _CONJ(p.fact("not_kred"), _CONJ(p.fact("not_sred"), p.fact("inner_ex")))
    )

    body_th = _sk_step_select_at(p, t, val, "inner_d3")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)

    # App-shape witness for D4 contradiction.
    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["u", "v"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # D1 carries the K-redex existence directly.
            p.choose("a_d1", from_="h1")
            p.choose("b_d1", from_="a_d1_eq")
            p.split("b_d1_eq", "(h_app, _)")
            p.have(f"h_kred: {K_shape}").by_exists(
                ["a_d1", "b_d1"], "h_app"
            )
            p.absurd().by_conj("not_kred", "h_kred")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a_d2", from_="h2_ex")
            p.choose("b_d2", from_="a_d2_eq")
            p.choose("c_d2", from_="b_d2_eq")
            p.split("c_d2_eq", "(h_app, _)")
            p.have(f"h_sred: {S_shape}").by_exists(
                ["a_d2", "b_d2", "c_d2"], "h_app"
            )
            p.absurd().by_conj("not_sred", "h_sred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_ex)")
            p.choose("a3", from_="h3_ex")
            p.choose("b3", from_="a3_eq")
            p.split("b3_eq", "(h_app, h_triple)")
            # u = a3, v = b3 via APP_T_INJ.
            p.have("h_inj: u = a3 /\\ v = b3").by(
                APP_T_INJ, "u", "v", "a3", "b3", "h_app"
            )
            p.have("h_ua: u = a3").by_thm(_C1(p.fact("h_inj")))
            p.have("h_vb: v = b3").by_thm(_C2(p.fact("h_inj")))
            with p.cases_on("h_triple"):
                with p.case(
                    f"hsub1: ~(sk_step a3 = a3) /\\ "
                    f"       {sk_t} = App_t (sk_step a3) b3"
                ):
                    p.split("hsub1", "(_, h_sk)")
                    p.thus(f"{sk_t} = {val}").by_rewrite_of(
                        "h_sk",
                        [SYM(p.fact("h_ua")), SYM(p.fact("h_vb"))],
                    )
                with p.case(
                    f"hsub2: sk_step a3 = a3 /\\ ~(sk_step b3 = b3) /\\ "
                    f"       {sk_t} = App_t a3 (sk_step b3)"
                ):
                    p.split("hsub2", "(h_sk_a, _, _)")
                    # sk_step a3 = a3; rewrite a3 → u gives sk_step u = u,
                    # contradicting not_norm_u.
                    p.have("h_sk_u: sk_step u = u").by_rewrite_of(
                        "h_sk_a", [SYM(p.fact("h_ua"))]
                    )
                    p.absurd().by_conj("not_norm_u", "h_sk_u")
                with p.case(
                    f"hsub3: sk_step a3 = a3 /\\ sk_step b3 = b3 /\\ "
                    f"       {sk_t} = {t}"
                ):
                    p.split("hsub3", "(h_sk_a, _, _)")
                    p.have("h_sk_u: sk_step u = u").by_rewrite_of(
                        "h_sk_a", [SYM(p.fact("h_ua"))]
                    )
                    p.absurd().by_conj("not_norm_u", "h_sk_u")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


@proof
def SK_STEP_RIGHT(p):
    """|- !u v.
            ~(?a b. App_t u v = App_t (App_t K_t a) b)
            ==> ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)
            ==> sk_step u = u
            ==> ~(sk_step v = v)
            ==> sk_step (App_t u v) = App_t u (sk_step v).

    Descend-right congruence: when the outer App is neither a K- nor an
    S-redex, the left child is already normal, and the right child is
    non-normal, sk_step descends into the right.  D3 of the 4-disjunct
    body fires at the descend-right sub-disjunct with witness
    (a, b) := (u, v).  Same dispatch shape as ``SK_STEP_LEFT``; sub2
    fires, sub1 contradicts ``sk_step u = u`` (after ``a = u``), sub3
    contradicts ``~(sk_step v = v)`` (after ``b = v``).
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!u v. ~(?a b. App_t u v = App_t (App_t K_t a) b) ==> "
        "      ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c) ==> "
        "      sk_step u = u ==> "
        "      ~(sk_step v = v) ==> "
        "      sk_step (App_t u v) = App_t u (sk_step v)"
    )
    p.fix("u v")
    p.assume("not_kred: ~(?a b. App_t u v = App_t (App_t K_t a) b)")
    p.assume("not_sred: ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)")
    p.assume("norm_u: sk_step u = u")
    p.assume("not_norm_v: ~(sk_step v = v)")

    t = "App_t u v"
    sk_t = f"sk_step ({t})"
    val = "App_t u (sk_step v)"
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"

    # Build the descend-right D3-inner witness at (a, b) := (u, v), r := val.
    # Sub-disjunct 2: sk_step u = u /\ ~(sk_step v = v) /\ val = App_t u (sk_step v).
    p.have(
        f"sub2: sk_step u = u /\\ ~(sk_step v = v) /\\ "
        f"      {val} = App_t u (sk_step v)"
    ).by_thm(
        _CONJ(
            p.fact("norm_u"),
            _CONJ(p.fact("not_norm_v"), REFL(p._parse(val))),
        )
    )
    triple_at_uv = (
        f"(~(sk_step u = u) /\\ {val} = App_t (sk_step u) v) \\/ "
        f"(sk_step u = u /\\ ~(sk_step v = v) /\\ "
        f" {val} = App_t u (sk_step v)) \\/ "
        f"(sk_step u = u /\\ sk_step v = v /\\ {val} = {t})"
    )
    p.have(f"triple_uv: {triple_at_uv}").by_disj("sub2")

    inner_ex = (
        f"?a b. {t} = App_t a b /\\ "
        f"((~(sk_step a = a) /\\ {val} = App_t (sk_step a) b) \\/ "
        f" (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"  {val} = App_t a (sk_step b)) \\/ "
        f" (sk_step a = a /\\ sk_step b = b /\\ {val} = {t}))"
    )
    p.have(f"inner_ex: {inner_ex}").by_exists(["u", "v"], "triple_uv")
    p.have(
        f"inner_d3: ~({K_shape}) /\\ ~({S_shape}) /\\ ({inner_ex})"
    ).by_thm(
        _CONJ(p.fact("not_kred"), _CONJ(p.fact("not_sred"), p.fact("inner_ex")))
    )

    body_th = _sk_step_select_at(p, t, val, "inner_d3")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)

    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["u", "v"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            p.choose("a_d1", from_="h1")
            p.choose("b_d1", from_="a_d1_eq")
            p.split("b_d1_eq", "(h_app, _)")
            p.have(f"h_kred: {K_shape}").by_exists(
                ["a_d1", "b_d1"], "h_app"
            )
            p.absurd().by_conj("not_kred", "h_kred")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a_d2", from_="h2_ex")
            p.choose("b_d2", from_="a_d2_eq")
            p.choose("c_d2", from_="b_d2_eq")
            p.split("c_d2_eq", "(h_app, _)")
            p.have(f"h_sred: {S_shape}").by_exists(
                ["a_d2", "b_d2", "c_d2"], "h_app"
            )
            p.absurd().by_conj("not_sred", "h_sred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_ex)")
            p.choose("a3", from_="h3_ex")
            p.choose("b3", from_="a3_eq")
            p.split("b3_eq", "(h_app, h_triple)")
            p.have("h_inj: u = a3 /\\ v = b3").by(
                APP_T_INJ, "u", "v", "a3", "b3", "h_app"
            )
            p.have("h_ua: u = a3").by_thm(_C1(p.fact("h_inj")))
            p.have("h_vb: v = b3").by_thm(_C2(p.fact("h_inj")))
            with p.cases_on("h_triple"):
                with p.case(
                    f"hsub1: ~(sk_step a3 = a3) /\\ "
                    f"       {sk_t} = App_t (sk_step a3) b3"
                ):
                    p.split("hsub1", "(h_nn_a, _)")
                    # ~(sk_step a3 = a3); rewrite a3 → u gives
                    # ~(sk_step u = u), contradicting norm_u.
                    p.have("h_nn_u: ~(sk_step u = u)").by_rewrite_of(
                        "h_nn_a", [SYM(p.fact("h_ua"))]
                    )
                    p.absurd().by_conj("h_nn_u", "norm_u")
                with p.case(
                    f"hsub2: sk_step a3 = a3 /\\ ~(sk_step b3 = b3) /\\ "
                    f"       {sk_t} = App_t a3 (sk_step b3)"
                ):
                    p.split("hsub2", "(_, _, h_sk)")
                    # h_sk: sk_t = App_t a3 (sk_step b3); rewrite a3 → u, b3 → v.
                    p.thus(f"{sk_t} = {val}").by_rewrite_of(
                        "h_sk",
                        [SYM(p.fact("h_ua")), SYM(p.fact("h_vb"))],
                    )
                with p.case(
                    f"hsub3: sk_step a3 = a3 /\\ sk_step b3 = b3 /\\ "
                    f"       {sk_t} = {t}"
                ):
                    p.split("hsub3", "(_, h_sk_b, _)")
                    p.have("h_sk_v: sk_step v = v").by_rewrite_of(
                        "h_sk_b", [SYM(p.fact("h_vb"))]
                    )
                    p.absurd().by_conj("not_norm_v", "h_sk_v")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


@proof
def SK_STEP_APP_FIXED(p):
    """|- !u v.
            ~(?a b. App_t u v = App_t (App_t K_t a) b)
            ==> ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)
            ==> sk_step u = u
            ==> sk_step v = v
            ==> sk_step (App_t u v) = App_t u v.

    Both-children-normal fixed point: when the outer App is neither a
    K- nor an S-redex and both children are sk_step-fixed, D3-sub3
    (the "no progress" inner branch) fires and ``sk_step`` returns
    the App self-equal.  Mirrors ``SK_STEP_LEFT``/``SK_STEP_RIGHT``;
    sub3 fires, sub1/sub2 contradict the two normality hypotheses.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!u v. ~(?a b. App_t u v = App_t (App_t K_t a) b) ==> "
        "      ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c) ==> "
        "      sk_step u = u ==> "
        "      sk_step v = v ==> "
        "      sk_step (App_t u v) = App_t u v"
    )
    p.fix("u v")
    p.assume("not_kred: ~(?a b. App_t u v = App_t (App_t K_t a) b)")
    p.assume("not_sred: ~(?a b c. App_t u v = App_t (App_t (App_t S_t a) b) c)")
    p.assume("norm_u: sk_step u = u")
    p.assume("norm_v: sk_step v = v")

    t = "App_t u v"
    sk_t = f"sk_step ({t})"
    val = t  # the App itself
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"

    # Sub-disjunct 3: sk_step u = u /\ sk_step v = v /\ val = t.
    p.have(
        f"sub3: sk_step u = u /\\ sk_step v = v /\\ {val} = {t}"
    ).by_thm(
        _CONJ(
            p.fact("norm_u"),
            _CONJ(p.fact("norm_v"), REFL(p._parse(t))),
        )
    )
    triple_at_uv = (
        f"(~(sk_step u = u) /\\ {val} = App_t (sk_step u) v) \\/ "
        f"(sk_step u = u /\\ ~(sk_step v = v) /\\ "
        f" {val} = App_t u (sk_step v)) \\/ "
        f"(sk_step u = u /\\ sk_step v = v /\\ {val} = {t})"
    )
    p.have(f"triple_uv: {triple_at_uv}").by_disj("sub3")

    inner_ex = (
        f"?a b. {t} = App_t a b /\\ "
        f"((~(sk_step a = a) /\\ {val} = App_t (sk_step a) b) \\/ "
        f" (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"  {val} = App_t a (sk_step b)) \\/ "
        f" (sk_step a = a /\\ sk_step b = b /\\ {val} = {t}))"
    )
    p.have(f"inner_ex: {inner_ex}").by_exists(["u", "v"], "triple_uv")
    p.have(
        f"inner_d3: ~({K_shape}) /\\ ~({S_shape}) /\\ ({inner_ex})"
    ).by_thm(
        _CONJ(p.fact("not_kred"), _CONJ(p.fact("not_sred"), p.fact("inner_ex")))
    )

    body_th = _sk_step_select_at(p, t, val, "inner_d3")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)

    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["u", "v"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            p.choose("a_d1", from_="h1")
            p.choose("b_d1", from_="a_d1_eq")
            p.split("b_d1_eq", "(h_app, _)")
            p.have(f"h_kred: {K_shape}").by_exists(
                ["a_d1", "b_d1"], "h_app"
            )
            p.absurd().by_conj("not_kred", "h_kred")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a_d2", from_="h2_ex")
            p.choose("b_d2", from_="a_d2_eq")
            p.choose("c_d2", from_="b_d2_eq")
            p.split("c_d2_eq", "(h_app, _)")
            p.have(f"h_sred: {S_shape}").by_exists(
                ["a_d2", "b_d2", "c_d2"], "h_app"
            )
            p.absurd().by_conj("not_sred", "h_sred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_ex)")
            p.choose("a3", from_="h3_ex")
            p.choose("b3", from_="a3_eq")
            p.split("b3_eq", "(h_app, h_triple)")
            p.have("h_inj: u = a3 /\\ v = b3").by(
                APP_T_INJ, "u", "v", "a3", "b3", "h_app"
            )
            p.have("h_ua: u = a3").by_thm(_C1(p.fact("h_inj")))
            p.have("h_vb: v = b3").by_thm(_C2(p.fact("h_inj")))
            with p.cases_on("h_triple"):
                with p.case(
                    f"hsub1: ~(sk_step a3 = a3) /\\ "
                    f"       {sk_t} = App_t (sk_step a3) b3"
                ):
                    p.split("hsub1", "(h_nn_a, _)")
                    # h_nn_a rewrites via a3 → u to ~(sk_step u = u),
                    # contradicting norm_u.
                    p.have("h_nn_u: ~(sk_step u = u)").by_rewrite_of(
                        "h_nn_a", [SYM(p.fact("h_ua"))]
                    )
                    p.absurd().by_conj("h_nn_u", "norm_u")
                with p.case(
                    f"hsub2: sk_step a3 = a3 /\\ ~(sk_step b3 = b3) /\\ "
                    f"       {sk_t} = App_t a3 (sk_step b3)"
                ):
                    p.split("hsub2", "(_, h_nn_b, _)")
                    p.have("h_nn_v: ~(sk_step v = v)").by_rewrite_of(
                        "h_nn_b", [SYM(p.fact("h_vb"))]
                    )
                    p.absurd().by_conj("h_nn_v", "norm_v")
                with p.case(
                    f"hsub3: sk_step a3 = a3 /\\ sk_step b3 = b3 /\\ "
                    f"       {sk_t} = {t}"
                ):
                    p.split("hsub3", "(_, _, h_sk)")
                    p.thus(f"{sk_t} = {val}").by_thm(p.fact("h_sk"))
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


@proof
def SK_STEP_K_UNDER_LEFT(p):
    """|- !x y z. ~(x = App_t (App_t K_t x) y) ==>
                  sk_step (App_t (App_t (App_t K_t x) y) z) = App_t x z.

    Composed congruence: a K-redex sitting one App deep on the left.
    Internally: ``SK_STEP_LEFT`` at ``(App_t (App_t K_t x) y, z)`` to
    descend, then ``SK_STEP_K`` at ``(x, y)`` to fire the inner K-redex.

    The two structural guard hypotheses of ``SK_STEP_LEFT`` (~K-shape
    and ~S-shape at the outer term) are discharged inline from the
    concrete outer shape via the APP_T_INJ + K_T_NEQ_APP_T /
    S_T_NEQ_K_T chain.  Only the third guard -- non-normality of the
    inner K-redex, equivalent to ``~(x = App_t (App_t K_t x) y)`` after
    one ``SK_STEP_K`` evaluation -- is exposed as a hypothesis because
    it depends on ``x``.

    Use this in place of a raw ``SK_STEP_LEFT`` whenever the descend
    target is a K-redex; the caller only needs to discharge the
    self-equality hypothesis (typically obvious by shape inspection of
    a concrete ``x``).
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2, TRANS

    p.goal(
        "!x y z. ~(x = App_t (App_t K_t x) y) ==> "
        "        sk_step (App_t (App_t (App_t K_t x) y) z) = App_t x z"
    )
    p.fix("x y z")
    p.assume("not_self: ~(x = App_t (App_t K_t x) y)")

    outer = "App_t (App_t (App_t K_t x) y) z"
    inner = "App_t (App_t K_t x) y"

    # H1: ~K-shape at outer.
    with p.have(
        f"h1: ~(?p q. {outer} = App_t (App_t K_t p) q)"
    ).proof():
        with p.suppose(f"ex_k: ?p q. {outer} = App_t (App_t K_t p) q"):
            p.choose("p_w", from_="ex_k")
            p.choose("q_w", from_="p_w_eq")
            p.have(f"e1: {inner} = App_t K_t p_w /\\ z = q_w").by(
                APP_T_INJ, inner, "z", "App_t K_t p_w", "q_w", "q_w_eq"
            )
            p.have(f"e1a: {inner} = App_t K_t p_w").by_thm(_C1(p.fact("e1")))
            p.have("e2: App_t K_t x = K_t /\\ y = p_w").by(
                APP_T_INJ, "App_t K_t x", "y", "K_t", "p_w", "e1a"
            )
            p.have("e2a: App_t K_t x = K_t").by_thm(_C1(p.fact("e2")))
            p.have("k_neq: ~(K_t = App_t K_t x)").by(K_T_NEQ_APP_T, "K_t", "x")
            p.have("k_eq: K_t = App_t K_t x").by_thm(SYM(p.fact("e2a")))
            p.absurd().by_conj("k_neq", "k_eq")

    # H2: ~S-shape at outer.
    with p.have(
        f"h2: ~(?p q r. {outer} = App_t (App_t (App_t S_t p) q) r)"
    ).proof():
        with p.suppose(
            f"ex_s: ?p q r. {outer} = App_t (App_t (App_t S_t p) q) r"
        ):
            p.choose("p_w", from_="ex_s")
            p.choose("q_w", from_="p_w_eq")
            p.choose("r_w", from_="q_w_eq")
            p.have(f"e1: {inner} = App_t (App_t S_t p_w) q_w /\\ z = r_w").by(
                APP_T_INJ, inner, "z",
                "App_t (App_t S_t p_w) q_w", "r_w", "r_w_eq",
            )
            p.have(
                f"e1a: {inner} = App_t (App_t S_t p_w) q_w"
            ).by_thm(_C1(p.fact("e1")))
            p.have("e2: App_t K_t x = App_t S_t p_w /\\ y = q_w").by(
                APP_T_INJ, "App_t K_t x", "y",
                "App_t S_t p_w", "q_w", "e1a",
            )
            p.have(
                "e2a: App_t K_t x = App_t S_t p_w"
            ).by_thm(_C1(p.fact("e2")))
            p.have("e3: K_t = S_t /\\ x = p_w").by(
                APP_T_INJ, "K_t", "x", "S_t", "p_w", "e2a"
            )
            p.have("k_eq_s: K_t = S_t").by_thm(_C1(p.fact("e3")))
            p.have("s_eq_k: S_t = K_t").by_thm(SYM(p.fact("k_eq_s")))
            p.absurd().by_conj(S_T_NEQ_K_T, "s_eq_k")

    # H3: ~(sk_step inner = inner) -- reduces to ~(x = inner) via SK_STEP_K.
    with p.have(f"h3: ~(sk_step ({inner}) = {inner})").proof():
        with p.suppose(f"h_eq: sk_step ({inner}) = {inner}"):
            p.have(f"sk_inner: sk_step ({inner}) = x").by(
                SK_STEP_K, "x", "y"
            )
            p.have(f"x_eq_inner: x = {inner}").by_thm(
                TRANS(SYM(p.fact("sk_inner")), p.fact("h_eq"))
            )
            p.absurd().by_conj("not_self", "x_eq_inner")

    # Apply SK_STEP_LEFT and SK_STEP_K, then compose.
    p.have(
        f"left_step: sk_step ({outer}) = App_t (sk_step ({inner})) z"
    ).by(SK_STEP_LEFT, inner, "z", "h1", "h2", "h3")
    p.have(f"k_step: sk_step ({inner}) = x").by(SK_STEP_K, "x", "y")
    p.thus(f"sk_step ({outer}) = App_t x z").by_rewrite_of(
        "left_step", ["k_step"]
    )


@proof
def SK_STEP_S_UNDER_LEFT(p):
    """|- !x y z w. ~(App_t (App_t x z) (App_t y z) =
                       App_t (App_t (App_t S_t x) y) z) ==>
                     sk_step (App_t (App_t (App_t (App_t S_t x) y) z) w)
                       = App_t (App_t (App_t x z) (App_t y z)) w.

    Composed congruence: an S-redex sitting one App deep on the left.
    Sister of ``SK_STEP_K_UNDER_LEFT``: descend via ``SK_STEP_LEFT`` at
    ``(App_t (App_t (App_t S_t x) y) z, w)``, then ``SK_STEP_S`` at
    ``(x, y, z)`` fires the inner S-redex.

    Structural guards on the outer term (~K-shape, ~S-shape) are
    discharged inline -- the outer first-arg ``App_t (App_t (App_t S_t
    x) y) z`` differs from both ``K_t`` (via APP_T_INJ + K_T_NEQ_APP_T)
    and ``App_t S_t _`` (via APP_T_INJ + S_T_NEQ_APP_T at the third
    level).  Only the non-normality guard -- that the S-redex's
    contractum doesn't coincide with the redex itself -- is exposed,
    since it depends on ``x, y, z``.
    """
    from tactics import CONJUNCT1 as _C1, TRANS

    p.goal(
        "!x y z w. ~(App_t (App_t x z) (App_t y z) = "
        "             App_t (App_t (App_t S_t x) y) z) ==> "
        "          sk_step (App_t (App_t (App_t (App_t S_t x) y) z) w) "
        "          = App_t (App_t (App_t x z) (App_t y z)) w"
    )
    p.fix("x y z w")
    p.assume(
        "not_self: ~(App_t (App_t x z) (App_t y z) "
        "          = App_t (App_t (App_t S_t x) y) z)"
    )

    inner = "App_t (App_t (App_t S_t x) y) z"
    outer = f"App_t ({inner}) w"
    contract = "App_t (App_t x z) (App_t y z)"

    # H1: ~K-shape at outer.  APP_T_INJ peels:
    #   App_t inner w = App_t (App_t K_t p) q   →   inner = App_t K_t p
    #   App_t (App_t S_t x) y = K_t   →   K_t = App_t (App_t S_t x) y
    # contradicts K_T_NEQ_APP_T.
    with p.have(
        f"h1: ~(?p q. {outer} = App_t (App_t K_t p) q)"
    ).proof():
        with p.suppose(f"ex_k: ?p q. {outer} = App_t (App_t K_t p) q"):
            p.choose("p_w", from_="ex_k")
            p.choose("q_w", from_="p_w_eq")
            p.have(f"e1: {inner} = App_t K_t p_w /\\ w = q_w").by(
                APP_T_INJ, inner, "w", "App_t K_t p_w", "q_w", "q_w_eq"
            )
            p.have(f"e1a: {inner} = App_t K_t p_w").by_thm(_C1(p.fact("e1")))
            p.have(
                "e2: App_t (App_t S_t x) y = K_t /\\ z = p_w"
            ).by(
                APP_T_INJ, "App_t (App_t S_t x) y", "z", "K_t", "p_w", "e1a"
            )
            p.have(
                "e2a: App_t (App_t S_t x) y = K_t"
            ).by_thm(_C1(p.fact("e2")))
            p.have("k_neq: ~(K_t = App_t (App_t S_t x) y)").by(
                K_T_NEQ_APP_T, "App_t S_t x", "y"
            )
            p.have("k_eq: K_t = App_t (App_t S_t x) y").by_thm(
                SYM(p.fact("e2a"))
            )
            p.absurd().by_conj("k_neq", "k_eq")

    # H2: ~S-shape at outer.  APP_T_INJ peels three levels:
    #   App_t inner w = App_t (App_t (App_t S_t p) q) r
    #     →   inner = App_t (App_t S_t p) q
    #   App_t (App_t S_t x) y = App_t S_t p
    #     →   App_t S_t x = S_t
    # contradicts S_T_NEQ_APP_T.
    with p.have(
        f"h2: ~(?p q r. {outer} = App_t (App_t (App_t S_t p) q) r)"
    ).proof():
        with p.suppose(
            f"ex_s: ?p q r. {outer} = App_t (App_t (App_t S_t p) q) r"
        ):
            p.choose("p_w", from_="ex_s")
            p.choose("q_w", from_="p_w_eq")
            p.choose("r_w", from_="q_w_eq")
            p.have(f"e1: {inner} = App_t (App_t S_t p_w) q_w /\\ w = r_w").by(
                APP_T_INJ, inner, "w",
                "App_t (App_t S_t p_w) q_w", "r_w", "r_w_eq",
            )
            p.have(f"e1a: {inner} = App_t (App_t S_t p_w) q_w").by_thm(
                _C1(p.fact("e1"))
            )
            p.have(
                "e2: App_t (App_t S_t x) y = App_t S_t p_w /\\ z = q_w"
            ).by(
                APP_T_INJ, "App_t (App_t S_t x) y", "z",
                "App_t S_t p_w", "q_w", "e1a",
            )
            p.have("e2a: App_t (App_t S_t x) y = App_t S_t p_w").by_thm(
                _C1(p.fact("e2"))
            )
            p.have("e3: App_t S_t x = S_t /\\ y = p_w").by(
                APP_T_INJ, "App_t S_t x", "y", "S_t", "p_w", "e2a"
            )
            p.have("e3a: App_t S_t x = S_t").by_thm(_C1(p.fact("e3")))
            p.have("s_neq: ~(S_t = App_t S_t x)").by(
                S_T_NEQ_APP_T, "S_t", "x"
            )
            p.have("s_eq: S_t = App_t S_t x").by_thm(SYM(p.fact("e3a")))
            p.absurd().by_conj("s_neq", "s_eq")

    # H3: ~(sk_step inner = inner) -- by SK_STEP_S, sk_step inner = contract;
    # then contract = inner contradicts not_self.
    with p.have(f"h3: ~(sk_step ({inner}) = {inner})").proof():
        with p.suppose(f"h_eq: sk_step ({inner}) = {inner}"):
            p.have(f"sk_inner: sk_step ({inner}) = {contract}").by(
                SK_STEP_S, "x", "y", "z"
            )
            p.have(f"c_eq_inner: {contract} = {inner}").by_thm(
                TRANS(SYM(p.fact("sk_inner")), p.fact("h_eq"))
            )
            p.absurd().by_conj("not_self", "c_eq_inner")

    # Apply SK_STEP_LEFT then SK_STEP_S, then compose.
    p.have(
        f"left_step: sk_step ({outer}) = App_t (sk_step ({inner})) w"
    ).by(SK_STEP_LEFT, inner, "w", "h1", "h2", "h3")
    p.have(f"s_step: sk_step ({inner}) = {contract}").by(
        SK_STEP_S, "x", "y", "z"
    )
    p.thus(f"sk_step ({outer}) = App_t ({contract}) w").by_rewrite_of(
        "left_step", ["s_step"]
    )


@proof
def SK_STEP_K_UNDER_LEFT_LEFT(p):
    """|- !x y z w. ~(x = App_t (App_t K_t x) y) ==>
                    sk_step (App_t (App_t (App_t (App_t K_t x) y) z) w)
                      = App_t (App_t x z) w.

    Depth-2 K congruence: a K-redex sitting two App layers deep on the
    leftmost spine.  Composes SK_STEP_K_UNDER_LEFT (fires the inner
    K-redex ``App_t (App_t (App_t K_t x) y) z -> App_t x z``) with
    SK_STEP_LEFT (lifts that step through the outer App).

    Single exposed hypothesis: the same self-equality guard as
    SK_STEP_K_UNDER_LEFT's -- ``~(x = App_t (App_t K_t x) y)`` -- since
    structural guards on the outer App are dischargeable internally
    (its LHS root ``App_t (App_t (App_t K_t x) y) z`` differs from K_t
    and App_t S_t _ via the same APP_T_INJ + atom-NEQ chain used in the
    depth-1 sibling).

    Used at Step 4 of Y_FIXED_POINT (replaces the in-trace "inline
    SK_STEP_K_UNDER_LEFT + SK_STEP_LEFT" composition).
    """
    from tactics import CONJUNCT1 as _C1, TRANS as _TRANS

    p.goal(
        "!x y z w. ~(x = App_t (App_t K_t x) y) ==> "
        "          sk_step (App_t (App_t (App_t (App_t K_t x) y) z) w) "
        "          = App_t (App_t x z) w"
    )
    p.fix("x y z w")
    p.assume("not_self_inner: ~(x = App_t (App_t K_t x) y)")

    inner_lhs = "App_t (App_t (App_t K_t x) y) z"
    outer = f"App_t ({inner_lhs}) w"
    inner_val = "App_t x z"

    # Fire the inner K-redex via the depth-1 sibling.
    p.have(
        f"inner_step: sk_step ({inner_lhs}) = {inner_val}"
    ).by(SK_STEP_K_UNDER_LEFT, "x", "y", "z", "not_self_inner")

    # H1 (~K-shape outer).  APP_T_INJ twice:
    #   outer = App_t (App_t K_t p) q  ->  inner_lhs = App_t K_t p
    #                                  ->  App_t (App_t K_t x) y = K_t.
    # SYM and K_T_NEQ_APP_T close.
    with p.have(f"h1: ~(?p q. {outer} = App_t (App_t K_t p) q)").proof():
        with p.suppose(f"ex_k: ?p q. {outer} = App_t (App_t K_t p) q"):
            p.choose("p_w", from_="ex_k")
            p.choose("q_w", from_="p_w_eq")
            p.have(f"e1: {inner_lhs} = App_t K_t p_w /\\ w = q_w").by(
                APP_T_INJ, inner_lhs, "w", "App_t K_t p_w", "q_w", "q_w_eq"
            )
            p.have(f"e1a: {inner_lhs} = App_t K_t p_w").by_thm(
                _C1(p.fact("e1"))
            )
            p.have(
                "e2: App_t (App_t K_t x) y = K_t /\\ z = p_w"
            ).by(
                APP_T_INJ, "App_t (App_t K_t x) y", "z", "K_t", "p_w", "e1a"
            )
            p.have(
                "e2a: App_t (App_t K_t x) y = K_t"
            ).by_thm(_C1(p.fact("e2")))
            p.have("k_neq: ~(K_t = App_t (App_t K_t x) y)").by(
                K_T_NEQ_APP_T, "App_t K_t x", "y"
            )
            p.have("k_eq: K_t = App_t (App_t K_t x) y").by_thm(
                SYM(p.fact("e2a"))
            )
            p.absurd().by_conj("k_neq", "k_eq")

    # H2 (~S-shape outer).  APP_T_INJ three peels:
    #   outer = App_t (App_t (App_t S_t p) q) r
    #     ->  inner_lhs = App_t (App_t S_t p) q
    #     ->  App_t (App_t K_t x) y = App_t S_t p
    #     ->  App_t K_t x = S_t.
    # SYM and S_T_NEQ_APP_T(K_t, x) close.
    with p.have(
        f"h2: ~(?p q r. {outer} = App_t (App_t (App_t S_t p) q) r)"
    ).proof():
        with p.suppose(
            f"ex_s: ?p q r. {outer} = App_t (App_t (App_t S_t p) q) r"
        ):
            p.choose("p_w", from_="ex_s")
            p.choose("q_w", from_="p_w_eq")
            p.choose("r_w", from_="q_w_eq")
            p.have(
                f"e1: {inner_lhs} = App_t (App_t S_t p_w) q_w /\\ w = r_w"
            ).by(
                APP_T_INJ, inner_lhs, "w",
                "App_t (App_t S_t p_w) q_w", "r_w", "r_w_eq",
            )
            p.have(
                f"e1a: {inner_lhs} = App_t (App_t S_t p_w) q_w"
            ).by_thm(_C1(p.fact("e1")))
            p.have(
                "e2: App_t (App_t K_t x) y = App_t S_t p_w /\\ z = q_w"
            ).by(
                APP_T_INJ, "App_t (App_t K_t x) y", "z",
                "App_t S_t p_w", "q_w", "e1a",
            )
            p.have(
                "e2a: App_t (App_t K_t x) y = App_t S_t p_w"
            ).by_thm(_C1(p.fact("e2")))
            p.have("e3: App_t K_t x = S_t /\\ y = p_w").by(
                APP_T_INJ, "App_t K_t x", "y", "S_t", "p_w", "e2a"
            )
            p.have("e3a: App_t K_t x = S_t").by_thm(_C1(p.fact("e3")))
            p.have("s_neq: ~(S_t = App_t K_t x)").by(
                S_T_NEQ_APP_T, "K_t", "x"
            )
            p.have("s_eq: S_t = App_t K_t x").by_thm(SYM(p.fact("e3a")))
            p.absurd().by_conj("s_neq", "s_eq")

    # H3 (~self-step of inner_lhs).  ``inner_step`` rewrites
    # sk_step inner_lhs to ``App_t x z``; suppose inner_lhs is a fixed
    # point.  Then App_t x z = inner_lhs; APP_T_INJ peels x =
    # App_t (App_t K_t x) y, contradicting not_self_inner.
    # DSL friction: the analogous H3 block appears verbatim in
    # SK_STEP_K_UNDER_LEFT (line 1348) and SK_STEP_S_UNDER_LEFT (1479).
    # A small `_h3_inner_nonself(p, inner_step_eq, not_self)` helper
    # would dedupe the three copies, but each variant differs in the
    # APP_T_INJ peel depth -- pulling it out cleanly needs a small DSL
    # on top of "peel-and-contradict".
    with p.have(f"h3: ~(sk_step ({inner_lhs}) = {inner_lhs})").proof():
        with p.suppose(f"h_eq: sk_step ({inner_lhs}) = {inner_lhs}"):
            p.have(
                f"val_eq_inner: {inner_val} = {inner_lhs}"
            ).by_thm(_TRANS(SYM(p.fact("inner_step")), p.fact("h_eq")))
            p.have(
                "peel: x = App_t (App_t K_t x) y /\\ z = z"
            ).by(
                APP_T_INJ, "x", "z",
                "App_t (App_t K_t x) y", "z", "val_eq_inner",
            )
            p.have("x_eq: x = App_t (App_t K_t x) y").by_thm(
                _C1(p.fact("peel"))
            )
            p.absurd().by_conj("not_self_inner", "x_eq")

    # SK_STEP_LEFT lifts the inner step through the outer App.
    p.have(
        f"left_step: sk_step ({outer}) = App_t (sk_step ({inner_lhs})) w"
    ).by(SK_STEP_LEFT, inner_lhs, "w", "h1", "h2", "h3")
    p.thus(f"sk_step ({outer}) = App_t ({inner_val}) w").by_rewrite_of(
        "left_step", ["inner_step"]
    )


def _atom_neq_App_negations(p, atom, atom_neq_lemma):
    """For an atom term (S_t or K_t), prove the three "atom is not
    App_t-shaped" existentials:
      ``~(?x y. atom = App_t (App_t K_t x) y)``,
      ``~(?x y z. atom = App_t (App_t (App_t S_t x) y) z)``,
      ``~(?a b. atom = App_t a b)``.
    Returns the three theorems.  Uses S_T_NEQ_APP_T / K_T_NEQ_APP_T.
    """
    from tactics import CONJ as _CONJ
    atom_str = atom  # display name only
    nK_th = None
    nS_th = None
    nApp_th = None
    with p.have(f"nApp_{atom_str}: ~(?a b. {atom_str} = App_t a b)").proof():
        with p.suppose(f"hex: ?a b. {atom_str} = App_t a b"):
            p.choose("a", from_="hex")
            p.choose("b", from_="a_eq")
            p.have(f"hneq: ~({atom_str} = App_t a b)").by(atom_neq_lemma, "a", "b")
            p.absurd().by_conj("hneq", "b_eq")
    with p.have(
        f"nK_{atom_str}: ~(?x y. {atom_str} = App_t (App_t K_t x) y)"
    ).proof():
        with p.suppose(f"hex: ?x y. {atom_str} = App_t (App_t K_t x) y"):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            p.have(f"hneq: ~({atom_str} = App_t (App_t K_t x) y)").by(
                atom_neq_lemma, "App_t K_t x", "y"
            )
            p.absurd().by_conj("hneq", "y_eq")
    with p.have(
        f"nS_{atom_str}: ~(?x y z. {atom_str} = App_t (App_t (App_t S_t x) y) z)"
    ).proof():
        with p.suppose(
            f"hex: ?x y z. {atom_str} = App_t (App_t (App_t S_t x) y) z"
        ):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            p.choose("z", from_="y_eq")
            p.have(
                f"hneq: ~({atom_str} = App_t (App_t (App_t S_t x) y) z)"
            ).by(atom_neq_lemma, "App_t (App_t S_t x) y", "z")
            p.absurd().by_conj("hneq", "z_eq")
    return f"nK_{atom_str}", f"nS_{atom_str}", f"nApp_{atom_str}"


def _prove_sk_step_leaf(p, atom_str, atom_neq_lemma):
    """Shared body of SK_STEP_LEAF_S / SK_STEP_LEAF_K.  Proves
    ``sk_step <atom> = <atom>`` where ``atom`` is ``S_t`` or ``K_t``
    (a leaf with no App_t shape).  The leaf-disjunct (index 3) fires;
    all three App-shaped branches are refuted via ``atom_neq_lemma``.
    """
    from tactics import CONJ as _CONJ
    t = atom_str
    sk_t = f"sk_step {t}"
    nK_lbl, nS_lbl, nApp_lbl = _atom_neq_App_negations(p, t, atom_neq_lemma)
    # Leaf-disjunct inner: nK /\ nS /\ nApp /\ atom = atom.
    p.have(
        f"inner_leaf: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f"~(?a b c. {t} = App_t (App_t (App_t S_t a) b) c) /\\ "
        f"~(?a b. {t} = App_t a b) /\\ {t} = {t}"
    ).by_thm(
        _CONJ(
            p.fact(nK_lbl),
            _CONJ(
                p.fact(nS_lbl),
                _CONJ(p.fact(nApp_lbl), REFL(p._parse(t))),
            ),
        )
    )
    body_th = _sk_step_select_at(p, t, t, "inner_leaf")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)
    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # ?a b. atom = App_t (App_t K_t a) b /\ sk_step atom = a.
            # The existential is what nK rules out.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nK_lbl, "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                f"h_sred_ex: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], p.fact("h_app"))
            p.absurd().by_conj(nS_lbl, "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_app)")
            p.choose("a", from_="h3_app")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_app_ex: ?a b. {t} = App_t a b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nApp_lbl, "h_app_ex")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, _, h_sk)")
            p.thus(f"{sk_t} = {t}").by_thm(p.fact("h_sk"))


@proof
def SK_STEP_LEAF_S(p):
    """|- sk_step S_t = S_t.  Leaf disjunct fires; App-branches all
    refuted via S_T_NEQ_APP_T."""
    p.goal("sk_step S_t = S_t")
    _prove_sk_step_leaf(p, "S_t", S_T_NEQ_APP_T)


@proof
def SK_STEP_LEAF_K(p):
    """|- sk_step K_t = K_t.  Same structure as SK_STEP_LEAF_S."""
    p.goal("sk_step K_t = K_t")
    _prove_sk_step_leaf(p, "K_t", K_T_NEQ_APP_T)


@proof
def IS_NORMAL_S(p):
    """|- is_normal S_t.  Trivial under is_normal := sk_step t = t."""
    p.goal("is_normal S_t")
    # is_normal S_t unfolds to sk_step S_t = S_t (SK_STEP_LEAF_S).
    p.thus("is_normal S_t").by_unfold(SK_STEP_LEAF_S, IS_NORMAL_DEF)


@proof
def IS_NORMAL_K(p):
    """|- is_normal K_t.  Trivial under is_normal := sk_step t = t."""
    p.goal("is_normal K_t")
    p.thus("is_normal K_t").by_unfold(SK_STEP_LEAF_K, IS_NORMAL_DEF)


@proof
def IS_NORMAL_IMP_FIXED(p):
    """|- !t. is_normal t ==> sk_step t = t.

    Trivial under is_normal := sk_step t = t: is_normal t IS
    sk_step t = t after one unfold.
    """
    p.goal("!t. is_normal t ==> sk_step t = t")
    p.fix("t")
    p.assume("h_norm: is_normal t")
    p.thus("sk_step t = t").by_unfold("h_norm", IS_NORMAL_DEF)


@proof
def IS_NORMAL_CASES(p):
    """|- !t. is_sk_term t ==> (is_normal t = (sk_step t = t)).

    Trivial under is_normal := sk_step t = t: both sides are
    definitionally equal.  The is_sk_term hypothesis is unused but
    retained in the signature for downstream interface stability.
    """
    p.goal("!t. is_sk_term t ==> (is_normal t = (sk_step t = t))")
    p.fix("t")
    p.assume("h_st: is_sk_term t")  # unused
    # is_normal t  unfolds to  sk_step t = t  via IS_NORMAL_DEF.
    p.thus("is_normal t = (sk_step t = t)").by_unfold(
        REFL(p._parse("sk_step t = t")), IS_NORMAL_DEF
    )


# ---------------------------------------------------------------------------
# Stage 2 -- multi-step reduction and halting.
#
#   sk_iter 0 t       = t
#   sk_iter (SUC n) t = sk_step (sk_iter n t)
#
#   reduces_in n t u  :=  sk_iter n t = u
#   halts t           :=  ?n. is_normal (sk_iter n t)
#
# ``halts`` is therefore a Sigma_1 predicate over nat0: r.e., not
# (we will show) recursive in the SK sense.
# ---------------------------------------------------------------------------


# ``sk_iter`` is defined by primitive recursion on the iteration count
# (the first argument). Using ``define_unary_0`` with result type
# ``nat0 -> nat0`` makes ``sk_iter n`` a function:
#
#   sk_iter 0          = \t. t
#   sk_iter (SUC0 n)   = \t. sk_step (sk_iter n t)
#
# The point-free form yields the SK_ITER_BASE / SK_ITER_STEP equations
# directly; SK_ITER_ZERO / SK_ITER_SUC just AP_THM at t and BETA.
from nat0 import define_unary_0  # noqa: E402

_n0_t_var = Var("t", nat0_ty)
_n0_k_var = Var("k", nat0_ty)
_n0_a_var = Var("a", parse_type("nat0 -> nat0"))

# c : nat0 -> nat0  ==  \t. t.
_c_sk_iter = mk_abs(_n0_t_var, _n0_t_var)

# h : nat0 -> (nat0 -> nat0) -> (nat0 -> nat0)
#   == \k. \a. \t. sk_step (a t).
_h_sk_iter = mk_abs(
    _n0_k_var,
    mk_abs(
        _n0_a_var,
        mk_abs(_n0_t_var, mk_app(sk_step, mk_app(_n0_a_var, _n0_t_var))),
    ),
)

SK_ITER_BASE, SK_ITER_STEP = define_unary_0(
    "sk_iter",
    parse_type("nat0 -> nat0 -> nat0"),
    _c_sk_iter,
    _h_sk_iter,
    result_ty=parse_type("nat0 -> nat0"),
)
sk_iter = mk_const("sk_iter", [])
# SK_ITER_BASE : |- sk_iter 0 = (\t. t)
# SK_ITER_STEP : |- !n. sk_iter (SUC0 n) = (\t. sk_step (sk_iter n t))


# halts t := ?n. is_normal (sk_iter n t).
HALTS_DEF = define(
    "halts",
    parse_type("nat0 -> bool"),
    "\\t:nat0. ?n:nat0. is_normal (sk_iter n t)",
)
halts = mk_const("halts", [])


@proof
def SK_ITER_ZERO(p):
    """|- !t. sk_iter 0 t = t.

    AP_THM SK_ITER_BASE at t, then BETA_CONV reduces ``(\\t. t) t`` to t.
    """
    from tactics import AP_THM, BETA_CONV, TRANS

    # SK_ITER_BASE : |- sk_iter 0 = \t. t
    # AP_THM at t  : |- sk_iter 0 t = (\t. t) t
    ap = AP_THM(SK_ITER_BASE, _n0_t_var)
    # BETA the RHS : |- (\t. t) t = t
    bet = BETA_CONV(rand(ap._concl))
    # TRANS gives  : |- sk_iter 0 t = t
    spec_th = TRANS(ap, bet)
    p.goal("!t. sk_iter 0 t = t")
    from tactics import GEN
    p.thus("!t. sk_iter 0 t = t").by_thm(GEN(_n0_t_var, spec_th))


@proof
def SK_ITER_SUC(p):
    """|- !n t. sk_iter (SUC0 n) t = sk_step (sk_iter n t).

    SPEC SK_ITER_STEP at n, AP_THM at t, BETA.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, SPEC, GENL

    n_var = Var("n", nat0_ty)
    # SPEC at n  : |- sk_iter (SUC0 n) = \t. sk_step (sk_iter n t)
    step_at_n = SPEC(n_var, SK_ITER_STEP)
    # AP_THM at t: |- sk_iter (SUC0 n) t = (\t. sk_step (sk_iter n t)) t
    ap = AP_THM(step_at_n, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!n t. sk_iter (SUC0 n) t = sk_step (sk_iter n t)")
    p.thus("!n t. sk_iter (SUC0 n) t = sk_step (sk_iter n t)").by_thm(
        GENL([n_var, _n0_t_var], spec_th)
    )


@proof
def HALTS_AT(p):
    """|- !t. halts t = (?n. is_normal (sk_iter n t)).

    Direct unfold of HALTS_DEF via AP_THM + BETA.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    # HALTS_DEF: |- halts = \t. ?n. is_normal (sk_iter n t).
    ap = AP_THM(HALTS_DEF, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. halts t = (?n. is_normal (sk_iter n t))")
    p.thus("!t. halts t = (?n. is_normal (sk_iter n t))").by_thm(
        GEN(_n0_t_var, spec_th)
    )


# ---------------------------------------------------------------------------
# sk_reduce -- block helper for head-redex sk_iter traces.
#
# A trace lemma of shape ``sk_iter k start = end`` (or its existential
# closure ``?n. sk_iter n start = end``) is a head-by-head reduction
# punctuated by definitional fold/unfold.  Hand-rolled, each head step
# costs two named ``have``s (one ``SK_ITER_SUC`` unfold + one
# ``by_rewrite_of`` to collapse the inner iter) plus per-step bookkeeping
# for the SUC0-tower witness.  See ``I_T_REDUCES`` for the unfactored
# shape and ``Y_FIXED_POINT``'s docstring for the friction inventory.
#
# Usage::
#
#     with sk_reduce(p, "App_t I_t x", "x") as r:
#         r.rewrite(I_T_DEF)                       # align: unfold I_t at start
#         r.step(SK_STEP_S, "K_t", "K_t", "x")     # head S-redex
#         r.step(SK_STEP_K, "x", "App_t K_t x")    # head K-redex
#
# On exit the surrounding goal is discharged.  Two goal shapes are
# auto-detected:
#
#   sk_iter <SUC0-tower> start = end       -- concrete (e.g. I_T_REDUCES)
#   ?n. sk_iter n start = end              -- existential
#
# If the goal matches neither, the running equation is registered as a
# plain fact instead.
#
# Each ``step``'s rule must fire on the whole current term:
# ``sk_step LHS = RHS`` (or ``... ==> sk_step LHS = RHS`` with the
# antecedents passed via ``mp=[...]``).  Head redexes (top S/K shape)
# use ``SK_STEP_S`` / ``SK_STEP_K`` directly; deeper redexes use the
# ``SK_STEP_LEFT`` / ``SK_STEP_RIGHT`` congruence lemmas, whose three
# guard hypotheses (~K-shape, ~S-shape, non-normality of the relevant
# child) are discharged by the caller and passed via ``mp=[...]``.
# ---------------------------------------------------------------------------


def sk_reduce(p, start, end, *, prefix="_sr", extras=None):
    """Open a head-redex sk_iter trace.  See module-level comment above.

    ``extras`` (optional): close a *parametric* existential goal of shape
    ``?n W1...Wm. sk_iter n start = end[W1...Wm] [/\\ side[W1...Wm]]``.
    Pass a tuple ``(extra_witnesses, *side_facts)``:
      * ``extra_witnesses`` -- list of term strings / kernel terms, one
        per outer existential AFTER the iter index (so the existential
        prefix is ``?n W1...Wm.`` with n outermost; ``end`` must already
        be the form with the W-witnesses substituted in).
      * ``side_facts`` -- zero or more fact-label/kernel-theorem
        arguments proving each side conjunct (if the body is a
        conjunction).  The trace's iter equation is supplied
        automatically as the first by_exists rule.

    The close uses ``by_exists([tower, *extras], iter_eq, *side_facts)``,
    so by_exists's auto-CONJ-discharge handles the per-conjunct rule
    matching.
    """
    return _SkReduce(p, start, end, prefix, extras)


class _SkReduce:
    def __init__(self, p, start, end, prefix, extras=None):
        self.p = p
        self.prefix = prefix
        self.start = p._parse(start) if isinstance(start, str) else start
        self.end = p._parse(end) if isinstance(end, str) else end
        self.extras = extras
        self.current = self.start
        # SUC0-tower kernel term, grown on every step.
        self.tower = p._parse("0")
        # Cached constants.
        self._sk_step = p._parse("sk_step")
        self._sk_iter = p._parse("sk_iter")
        # Seed: |- sk_iter 0 start = start.
        self._running = SPEC(self.start, SK_ITER_ZERO)
        self._closed = False

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc_type is None and not self._closed:
            self._close()
        return False

    # -- public ops --------------------------------------------------------

    def step(self, rule, *args, mp=()):
        """Apply one head-redex rule.  ``rule`` is a kernel theorem of
        shape ``!v1...vk. H1 ==> ... ==> Hm ==> sk_step LHS = RHS``;
        ``args`` are term-string or kernel-term specialisations for
        v1...vk.  ``mp`` is an optional sequence of fact references (label
        / theorem) MP'd onto the antecedents after SPECL -- use for
        congruence rules like ``SK_STEP_LEFT`` whose statement is
        guarded by ``~K-shape``, ``~S-shape``, ``~(sk_step a = a)``.
        After SPECL + MP, the instantiated ``LHS`` must alpha-match the
        current term -- call ``rewrite`` first to align if it doesn't.
        """
        arg_ts = [self.p._parse(a) if isinstance(a, str) else a for a in args]
        step_th = SPECL(arg_ts, rule) if arg_ts else rule
        for h in mp:
            h_th = self.p.fact(h) if isinstance(h, str) else h
            step_th = MP(step_th, h_th)
        try:
            lhs, rhs = dest_eq(step_th._concl)
        except HolError:
            raise HolError(
                "sk_reduce.step: rule conclusion is not an equation after "
                "SPECL+MP (remaining antecedents? pass them via mp=[...])"
            )
        try:
            head = rator(lhs)
        except HolError:
            raise HolError("sk_reduce.step: rule LHS is not of shape `sk_step _`")
        if not aconv(head, self._sk_step):
            raise HolError(
                f"sk_reduce.step: rule LHS head is {pp(head)}, not sk_step"
            )
        T = rand(lhs)
        if not aconv(T, self.current):
            raise HolError(
                "sk_reduce.step: rule fires on "
                f"sk_step ({pp(T)}); current is {pp(self.current)} -- "
                "call .rewrite(...) to align before .step()"
            )
        # iter_unfold: sk_iter (SUC0 tower) start = sk_step (sk_iter tower start)
        iter_unfold = SPECL([self.tower, self.start], SK_ITER_SUC)
        # Replace the inner ``sk_iter tower start`` by ``current`` via the
        # running fact: sk_step (sk_iter tower start) = sk_step current.
        inner = AP_TERM(self._sk_step, self._running)
        # Compose: sk_iter (SUC0 tower) start = sk_step current.
        iter_aligned = TRANS(iter_unfold, inner)
        # Apply step_th: sk_iter (SUC0 tower) start = rhs.
        self._running = TRANS(iter_aligned, step_th)
        self.current = rhs
        self.tower = mk_suc0(self.tower)

    def rewrite(self, *rules):
        """Rewrite the current term via REWRITE_CONV with ``rules``
        (kernel theorems or fact labels).  Useful for unfolding a defined
        symbol on the start side (so the next ``step`` sees the redex
        shape) or folding mid-trace.  Does not bump the iter count.
        """
        if not rules:
            return
        rule_ths = [self.p.fact(r) if isinstance(r, str) else r for r in rules]
        eq = REWRITE_CONV(rule_ths, self.current)
        lhs, rhs = dest_eq(eq._concl)
        if aconv(lhs, rhs):
            return  # REFL -- nothing to do.
        self._running = TRANS(self._running, eq)
        self.current = rhs

    def qed(self):
        """Explicit close.  Called automatically on block exit."""
        self._close()

    # -- internals ---------------------------------------------------------

    def _close(self):
        if self._closed:
            return
        self._closed = True
        if not aconv(self.current, self.end):
            raise HolError(
                "sk_reduce: trace ended at "
                f"{pp(self.current)}; expected end = {pp(self.end)}"
            )
        # Build the kernel theorem to register.
        # Concrete: |- sk_iter tower start = end  (already self._running).
        concrete_th = self._running
        # Existential lift: |- ?n. sk_iter n start = end.
        n_var = Var("n", nat0_ty)
        body_at_n = mk_eq(
            mk_app(self._sk_iter, n_var, self.start),
            self.end,
        )
        existential_term = mk_exists(n_var, body_at_n)
        ex_th = EXISTS(mk_abs(n_var, body_at_n), self.tower, concrete_th)

        # Inspect surrounding goal to decide how to discharge.
        fr = self.p._frames[-1]
        goal = fr.goal
        concrete_term = mk_eq(
            mk_app(self._sk_iter, self.tower, self.start),
            self.end,
        )

        # Extras path: parametric existential ``?n W1...Wm. body[W, n]``.
        # The tower closes the n existential; user supplies witnesses for
        # the remaining W-existentials plus any side-conjunct facts.
        # by_exists handles the by-conjunct dispatch.
        if self.extras is not None and goal is not None:
            extra_witnesses, *side_facts = self.extras
            parsed_wits = [
                self.p._parse(w) if isinstance(w, str) else w
                for w in extra_witnesses
            ]
            side_ths = [
                self.p.fact(f) if isinstance(f, str) else f
                for f in side_facts
            ]
            self.p.thus(pp(goal)).by_exists(
                [self.tower, *parsed_wits],
                concrete_th,
                *side_ths,
            )
            return

        if goal is not None and aconv(goal, concrete_term):
            self.p.thus(pp(concrete_term)).by_thm(concrete_th)
        elif goal is not None and aconv(goal, existential_term):
            self.p.thus(pp(existential_term)).by_thm(ex_th)
        else:
            # Surrounding goal isn't a trace target -- register the
            # existential as a fact for the caller to use.
            self.p.have(
                f"{self.prefix}_ex: {pp(existential_term)}"
            ).by_thm(ex_th)


# ---------------------------------------------------------------------------
# Stage 3 -- the standard combinators.
#
#   I_t  := App_t (App_t S_t K_t) K_t           -- identity
#   KI_t := App_t K_t I_t                       -- "false" Church bool
#   D_t  := App_t S_t (App_t I_t I_t)           -- self-duplicator (Curry)
#   Omega_t := App_t D_t D_t                    -- canonical loop
#
# Reductions:
#   I_t x   -->  x                              (S K K x --> K x (K x) --> x;
#                                                see I_T_REDUCES, 2 steps)
#   sk_step Omega_t  =  App_t (I_t SII) (I_t SII)
#                                               (one S-redex step, NOT a
#                                                self-loop; see OMEGA_T_STEP1)
#
# Hence Omega_t never reaches a normal form, but proving
# ``~ halts Omega_t`` requires a size-measure on nat0 terms and a
# 3-step strict-growth lemma -- see OMEGA_NON_HALTING's docstring for
# the DSL friction inventory.
# ---------------------------------------------------------------------------


I_T_DEF = define(
    "I_t",
    nat0_ty,
    mk_app(App_t, mk_app(App_t, S_t, K_t), K_t),
)
I_t = mk_const("I_t", [])


KI_T_DEF = define(
    "KI_t",
    nat0_ty,
    mk_app(App_t, K_t, I_t),
)
KI_t = mk_const("KI_t", [])


# D_t := S I I  -- the self-applicator
_D_self_t = mk_app(App_t, mk_app(App_t, S_t, I_t), I_t)


OMEGA_T_DEF = define(
    "Omega_t",
    nat0_ty,
    mk_app(App_t, _D_self_t, _D_self_t),
)
Omega_t = mk_const("Omega_t", [])


@proof
def IS_SK_TERM_I_T(p):
    """|- is_sk_term I_t.  Unfolds I_t to ``App_t (App_t S_t K_t) K_t``
    and applies the structural-intro tree (S_t, K_t leaves + App_t)."""
    p.goal("is_sk_term I_t")
    p.thus("is_sk_term I_t").by_tree(unfold=[I_T_DEF])


@proof
def IS_SK_TERM_KI_T(p):
    """|- is_sk_term KI_t.  ``KI_t = App_t K_t I_t`` -- one App over a
    leaf (K_t) and the I_t combinator (which unfolds to atoms)."""
    p.goal("is_sk_term KI_t")
    p.thus("is_sk_term KI_t").by_tree(unfold=[KI_T_DEF, I_T_DEF])


@proof
def IS_SK_TERM_OMEGA_T(p):
    """|- is_sk_term Omega_t.

    ``Omega_t = App_t (App_t (App_t S_t I_t) I_t) (App_t (App_t S_t I_t) I_t)``;
    structural-intro through OMEGA_T_DEF + I_T_DEF.
    """
    p.goal("is_sk_term Omega_t")
    p.thus("is_sk_term Omega_t").by_tree(unfold=[OMEGA_T_DEF, I_T_DEF])


@proof
def I_T_REDUCES(p):
    """|- !x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x.

    I = SKK; in two head steps via ``sk_reduce``:
        sk_iter 0 (I x) = I x = App_t (App_t (App_t S_t K_t) K_t) x  [unfold I_t]
        sk_iter 1 (I x) = App_t (App_t K_t x) (App_t K_t x)          [SK_STEP_S]
        sk_iter 2 (I x) = x                                          [SK_STEP_K]

    The is_sk_term hypothesis isn't actually used by the head-redex
    rules -- they fire on any term of the right shape -- but it's
    carried in the goal for interface consistency with downstream.
    """
    p.goal("!x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x")
    p.fix("x")
    p.assume("h_st: is_sk_term x")  # unused (see docstring)
    with sk_reduce(p, "App_t I_t x", "x") as r:
        r.rewrite(I_T_DEF)
        r.step(SK_STEP_S, "K_t", "K_t", "x")
        r.step(SK_STEP_K, "x", "App_t K_t x")


@proof
def IS_NORMAL_I_T(p):
    """|- is_normal I_t.

    ``I_t = App_t (App_t S_t K_t) K_t`` (via ``I_T_DEF``).  The outer
    App is not a K-redex (head is ``App_t S_t K_t``, not ``K_t``) nor an
    S-redex (only two nested Apps starting at ``S_t``, S-redex shape
    needs three).  Both children are normal:
      * ``App_t S_t K_t``: same no-redex argument applied recursively;
        both ``S_t`` and ``K_t`` are leaf normal forms.
      * ``K_t``: leaf normal (SK_STEP_LEAF_K).
    Hence D3-sub3 fires twice (once at each App layer), yielding
    ``sk_step I_t = I_t``.  Then ``by_unfold IS_NORMAL_DEF`` bridges
    to ``is_normal I_t``.

    The four "head-tag clash" non-redex hypotheses are discharged
    mechanically by ``shape_neq`` (~50 LOC saved vs. inline
    APP_T_INJ chains).
    """
    p.goal("is_normal I_t")

    # ---- inner: sk_step (App_t S_t K_t) = App_t S_t K_t -------------------
    inner = "App_t S_t K_t"
    shape_neq(
        p, "not_kred_inner",
        f"~(?a b. {inner} = App_t (App_t K_t a) b)",
    )
    shape_neq(
        p, "not_sred_inner",
        f"~(?a b c. {inner} = App_t (App_t (App_t S_t a) b) c)",
    )
    p.have(
        f"inner_fixed: sk_step ({inner}) = {inner}"
    ).by(
        SK_STEP_APP_FIXED, "S_t", "K_t",
        "not_kred_inner", "not_sred_inner",
        SK_STEP_LEAF_S, SK_STEP_LEAF_K,
    )

    # ---- outer: sk_step I_t = I_t -----------------------------------------
    outer = "App_t (App_t S_t K_t) K_t"
    shape_neq(
        p, "not_kred_outer",
        f"~(?a b. {outer} = App_t (App_t K_t a) b)",
    )
    shape_neq(
        p, "not_sred_outer",
        f"~(?a b c. {outer} = App_t (App_t (App_t S_t a) b) c)",
    )
    p.have(
        f"outer_fixed: sk_step ({outer}) = {outer}"
    ).by(
        SK_STEP_APP_FIXED, "App_t S_t K_t", "K_t",
        "not_kred_outer", "not_sred_outer",
        "inner_fixed", SK_STEP_LEAF_K,
    )

    # Fold the unfolded shape back to I_t, then collapse via IS_NORMAL_DEF.
    p.have("step_I: sk_step I_t = I_t").by_rewrite_of(
        "outer_fixed", [SYM(I_T_DEF)]
    )
    p.thus("is_normal I_t").by_unfold("step_I", IS_NORMAL_DEF)


@proof
def SK_STEP_K_DESC_RIGHT(p):
    """|- !Z. ~(sk_step Z = Z)
              ==> sk_step (App_t K_t Z) = App_t K_t (sk_step Z).

    Single-arg K (i.e. K_t applied to one argument) is NOT a K-redex
    (K-redex needs ``App_t (App_t K_t _) _``).  With K_t-headed App
    not matching either head-redex shape and K_t leaf-normal, when
    the argument Z is non-fixed, ``sk_step`` descends right by
    ``SK_STEP_RIGHT``.
    """
    p.goal(
        "!Z. ~(sk_step Z = Z) ==> "
        "    sk_step (App_t K_t Z) = App_t K_t (sk_step Z)"
    )
    p.fix("Z")
    p.assume("not_fixed: ~(sk_step Z = Z)")
    shape_neq(
        p, "not_kred",
        "~(?a b. App_t K_t Z = App_t (App_t K_t a) b)",
    )
    shape_neq(
        p, "not_sred",
        "~(?a b c. App_t K_t Z = App_t (App_t (App_t S_t a) b) c)",
    )
    p.thus(
        "sk_step (App_t K_t Z) = App_t K_t (sk_step Z)"
    ).by(
        SK_STEP_RIGHT, "K_t", "Z",
        "not_kred", "not_sred",
        SK_STEP_LEAF_K, "not_fixed",
    )


# ---------------------------------------------------------------------------
# Stage 3b -- ``sk_size`` measure and arithmetic helpers for the
# eventual OMEGA_NON_HALTING proof.
#
# Definition (well-founded recursion on Pair_ord depth, same as
# ``sk_step``):
#
#   sk_size n  :=  if ?a b. n = App_t a b
#                  then SUC0 (n0plus (sk_size a) (sk_size b))
#                  else SUC0 0
#
# Unfolders:
#   SK_SIZE_S    :  |- sk_size S_t = SUC0 0
#   SK_SIZE_K    :  |- sk_size K_t = SUC0 0
#   SK_SIZE_APP  :  |- !a b. sk_size (App_t a b)
#                            = SUC0 (n0plus (sk_size a) (sk_size b))
#
# Strict-growth helper (used by OMEGA_NON_HALTING):
#   SK_SIZE_GROWTH_OMEGA_SHAPE
#                :  |- !t. nat0_lt (sk_size t)
#                          (sk_size (App_t (App_t I_t t) (App_t I_t t)))
#
# DSL friction inventory for sk_size (compared to ``sk_step``, which
# uses the same SELECT-shaped body but with four disjuncts):
#   * ``sk_size`` only needs two disjuncts (``App_t a b`` vs. leaf),
#     so MONO is half the length and we reuse
#     ``mono_iff_value_binary_pw_step`` directly for the App_t branch.
#   * The leaf disjunct is f-free, so its MONO contribution is REFL.
#   * Unfolding equations re-use ``_select_via_rec`` and the
#     ``_atom_neq_App_negations`` helper introduced for SK_STEP_LEAF_S/K.
# ---------------------------------------------------------------------------


_F_sk_size_ty = parse_type("(nat0 -> nat0) -> nat0 -> nat0")


_SK_SIZE_F_DEF = define(
    "_sk_size_F",
    _F_sk_size_ty,
    "\\f:nat0->nat0. \\n:nat0. "
    "@r:nat0. "
    "(?a b. n = App_t a b /\\ r = SUC0 (n0plus (f a) (f b))) \\/ "
    "(~(?a b. n = App_t a b) /\\ r = SUC0 0)",
)
_SK_SIZE_F = mk_const("_sk_size_F", [])


def _prove_sk_size_F_at():
    """|- !f t. _sk_size_F f t = body[f, t]  (two BETAs).

    DSL friction: this is the same shape as ``_prove_sk_step_F_at``
    (and ``_prove_F_at`` in bits.py); a generic 2-BETA peel helper
    would dedupe these three sites but doesn't exist yet.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GENL
    f_var = Var("f", _sk_step_fn_ty)
    t_var = Var("t", nat0_ty)
    th_f = AP_THM(_SK_SIZE_F_DEF, f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_ft = AP_THM(th_f_eq, t_var)
    th_ft_eq = TRANS(th_ft, BETA_CONV(rand(th_ft._concl)))
    return GENL([f_var, t_var], th_ft_eq)


_SK_SIZE_F_AT = _prove_sk_size_F_at()


@proof
def SK_SIZE_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                ==> _sk_size_F f n = _sk_size_F g n.

    Body is ``@r. D1 \\/ D2`` where:
      D1 (?a b. n = App_t a b /\\ r = SUC0 (n0plus (f a) (f b)))
        recurses through ``f a`` / ``f b``; the helper
        ``mono_iff_value_binary_pw_step`` handles it directly.
      D2 (~App-shape /\\ r = SUC0 0) is f-free; REFL.

    Same stitching pattern as ``SK_STEP_MONO`` but with two disjuncts
    instead of four.
    """
    from tactics import (
        AP_TERM as _AP_TERM,
        SPECL as _SPECL,
        TRANS as _TRANS,
        SYM as _SYM,
        or_chain_collapse as _or_collapse,
    )
    from hf_syntax import _mono_iff_value_binary_pw_step, _extract_nfg
    from axioms import mk_and as _mk_and, mk_not as _mk_not, mk_exists as _mk_exists
    from basics import mk_eq as _mk_eq

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _sk_size_F f n = _sk_size_F g n",
        types={
            "f": _sk_step_fn_ty,
            "g": _sk_step_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")
    n_t, f_t, g_t, _ = _extract_nfg(h_th)
    r_var = Var("r", nat0_ty)
    a_var = Var("a", nat0_ty)
    b_var = Var("b", nat0_ty)

    # App-shape (used in D2's negation).
    App_body = _mk_eq(n_t, mk_app(App_t, a_var, b_var))
    App_shape = _mk_exists(a_var, _mk_exists(b_var, App_body))

    # D2 is f-free.
    D2 = _mk_and(_mk_not(App_shape), _mk_eq(r_var, p._parse("SUC0 0")))
    eq_D2 = REFL(D2)

    # D1 = ?a b. n = App_t a b /\ r = SUC0 (n0plus (f a) (f b))
    # ``rest_builder(fn, a, b, args)`` returns the conjunct after
    # ``n = App_t a b /\ ...``; we want
    # ``r = SUC0 (n0plus (fn a) (fn b))``.
    SUC0_C = p._parse("SUC0")
    N0PLUS_C = p._parse("n0plus")

    def _D1_rest_builder(fn, a, b, args):
        fa = mk_app(fn, a)
        fb = mk_app(fn, b)
        sum_ = mk_app(N0PLUS_C, fa, fb)
        suc = mk_app(SUC0_C, sum_)
        return _mk_eq(r_var, suc)

    eq_D1 = _mono_iff_value_binary_pw_step(
        App_t,
        NAT0_LT_APP_T_L, NAT0_LT_APP_T_R,
        h_th,
        args=[],
        rest_builder=_D1_rest_builder,
        recurses_l=True,
    )

    body_eq_at_r = _or_collapse([eq_D1, eq_D2])
    select_eq = _lift_select_eq(r_var, body_eq_at_r)
    spec_f = _SPECL([f_t, n_t], _SK_SIZE_F_AT)
    spec_g = _SPECL([g_t, n_t], _SK_SIZE_F_AT)
    final = _TRANS(spec_f, _TRANS(select_eq, _SYM(spec_g)))

    p.thus("_sk_size_F f n = _sk_size_F g n").by_thm(final)


SK_SIZE_DEF, _SK_SIZE_REC_RAW = define_wf_lt(
    "sk_size",
    _sk_step_fn_ty,
    _SK_SIZE_F,
    SK_SIZE_MONO,
)
sk_size = mk_const("sk_size", [])


# SK_SIZE_REC : |- !n. sk_size n = body[sk_size, n]
SK_SIZE_REC = _unfold_rec_via_F_def(_SK_SIZE_REC_RAW, _SK_SIZE_F_DEF)


def _sk_size_disjuncts(t, r):
    """Return the two disjunct strings of ``_sk_size_F``'s body at
    input ``t`` with the SELECT-bound variable substituted by ``r``.
    Existential names ``a, b`` are chosen to avoid shadowing common
    outer-scope names like ``x, y``.
    """
    D1 = f"(?a b. {t} = App_t a b /\\ {r} = SUC0 (n0plus (sk_size a) (sk_size b)))"
    D2 = f"(~(?a b. {t} = App_t a b) /\\ {r} = SUC0 0)"
    return [D1, D2]


def _sk_size_body(t, r):
    return " \\/ ".join(_sk_size_disjuncts(t, r))


def _sk_size_select_at(p, t, witness_r, inner_branch_th):
    """Mirror of ``_sk_step_select_at`` for sk_size's two-disjunct body."""
    body_at_r = _sk_size_body(t, witness_r)
    body_at_r_var = _sk_size_body(t, "r")
    p.have(f"_size_disj_rhs: {body_at_r}").by_disj(inner_branch_th)
    p.have(f"_size_ex: ?r. {body_at_r_var}").by_witness(
        witness_r, "_size_disj_rhs"
    )
    return _select_via_rec(SK_SIZE_REC, [p._parse(t)], p.fact("_size_ex"))


@proof
def SK_SIZE_APP(p):
    """|- !a b. sk_size (App_t a b) = SUC0 (n0plus (sk_size a) (sk_size b)).

    The App-shape disjunct (D1) fires at the natural witness; D2 is
    refuted by the obvious App-existence of the input.
    """
    from tactics import CONJ as _CONJ
    from tactics import CONJUNCT1 as _C1, CONJUNCT2 as _C2  # noqa: F841
    # DSL friction: ``_sk_size_disjuncts`` uses bound names ``a, b``, so
    # the surface goal vars must avoid those.  We use ``u, v`` for the
    # App_t arguments throughout this proof.
    p.goal(
        "!u v. sk_size (App_t u v) = SUC0 (n0plus (sk_size u) (sk_size v))"
    )
    p.fix("u v")
    t = "App_t u v"
    sk_t = f"sk_size ({t})"
    witness = "SUC0 (n0plus (sk_size u) (sk_size v))"

    # D1 inner at (u, v): ?a b. App_t u v = App_t a b /\ witness = SUC0 (n0plus (sk_size a) (sk_size b)).
    p.have(
        f"inner_app: ?a b. {t} = App_t a b /\\ "
        f"            {witness} = SUC0 (n0plus (sk_size a) (sk_size b))"
    ).by_exists(["u", "v"], REFL(p._parse(t)), REFL(p._parse(witness)))
    body_th = _sk_size_select_at(p, t, witness, "inner_app")
    p.have(f"body: {_sk_size_body(t, sk_t)}").by_thm(body_th)

    # App existence at the input; refutes ~App guard in D2.
    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["u", "v"], REFL(p._parse(t))
    )

    D1, D2 = _sk_size_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # ?a b. App_t u v = App_t a b /\ sk_size (App_t u v) = SUC0 (n0plus (sk_size a) (sk_size b)).
            # ``cases_on`` auto-chooses the outermost existential (a, registered
            # via ``a_eq``); we choose ``b`` manually.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_sz)")
            # APP_T_INJ: App_t u v = App_t a b ==> u = a /\ v = b.
            p.have("h_o: u = a /\\ v = b").by(
                APP_T_INJ, "u", "v", "a", "b", "h_app"
            )
            p.have("h_ua: u = a").by_thm(_C1(p.fact("h_o")))
            p.have("h_vb: v = b").by_thm(_C2(p.fact("h_o")))
            # Rewrite h_sz to put back u, v.
            p.thus(
                f"{sk_t} = SUC0 (n0plus (sk_size u) (sk_size v))"
            ).by_rewrite_of("h_sz", [SYM(p.fact("h_ua")), SYM(p.fact("h_vb"))])
        with p.case(f"h2: {D2}"):
            p.split("h2", "(h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


def _prove_sk_size_leaf(p, atom_str, atom_neq_lemma):
    """Shared body of SK_SIZE_S / SK_SIZE_K.  Proves
    ``sk_size <atom> = SUC0 0`` for atom in {S_t, K_t}.  The leaf
    disjunct (D2) fires; D1 is refuted via the atom's non-App shape.
    """
    from tactics import CONJ as _CONJ
    t = atom_str
    sk_t = f"sk_size {t}"
    # Reuse _atom_neq_App_negations to get nApp_<atom>: ~(?a b. atom = App_t a b)
    # (the other two are unused here but cheap to derive).
    _, _, nApp_lbl = _atom_neq_App_negations(p, t, atom_neq_lemma)
    p.have(
        f"inner_leaf: ~(?a b. {t} = App_t a b) /\\ SUC0 0 = SUC0 0"
    ).by_thm(_CONJ(p.fact(nApp_lbl), REFL(p._parse("SUC0 0"))))
    body_th = _sk_size_select_at(p, t, "SUC0 0", "inner_leaf")
    p.have(f"body: {_sk_size_body(t, sk_t)}").by_thm(body_th)
    D1, D2 = _sk_size_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # cases_on auto-chooses outer ``a``; we only choose ``b``.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_app_ex: ?a b. {t} = App_t a b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nApp_lbl, "h_app_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h_sz)")
            p.thus(f"{sk_t} = SUC0 0").by_thm(p.fact("h_sz"))


@proof
def SK_SIZE_S(p):
    """|- sk_size S_t = SUC0 0.  D2 fires; D1 refuted via S_T_NEQ_APP_T."""
    p.goal("sk_size S_t = SUC0 0")
    _prove_sk_size_leaf(p, "S_t", S_T_NEQ_APP_T)


@proof
def SK_SIZE_K(p):
    """|- sk_size K_t = SUC0 0.  Same shape as SK_SIZE_S."""
    p.goal("sk_size K_t = SUC0 0")
    _prove_sk_size_leaf(p, "K_t", K_T_NEQ_APP_T)


# ---------------------------------------------------------------------------
# Arithmetic helper: ``n0plus`` is strictly bounded by SUC0 over its
# growth -- specifically ``nat0_lt a (SUC0 (n0plus a b))``.  This is the
# core inequality used by SK_SIZE_GROWTH_OMEGA_SHAPE: ``sk_size t``
# appears as one summand in ``sk_size (App_t (I_t t) (I_t t))`` and the
# overall result is SUC0 of a sum that includes a strictly-positive
# constant.
#
# Proof by induction on ``b``: base ``n0plus a 0 = a``, SUC0 a > a by
# NAT0_LT_SUC0; step ``n0plus a (SUC0 b) = SUC0 (n0plus a b)``, lift IH
# through one more SUC0 via NAT0_LT_TRANS.
# ---------------------------------------------------------------------------


from nat0_order import NAT0_LT_SUC0, NAT0_LT_TRANS  # noqa: E402
from hf_sets import N0PLUS_BASE, N0PLUS_STEP  # noqa: E402


@proof
def NAT0_LT_SUC0_N0PLUS_L(p):
    """|- !a b. nat0_lt a (SUC0 (n0plus a b)).

    Pulled out as a named lemma so the growth proof reads cleanly.

    DSL friction: ``by_rewrite_of`` with ``SYM`` of the n0plus equation
    loops because REWRITE_CONV treats free vars as schematic.  We
    do the substitution manually via two ``AP_TERM`` hops and
    ``by_eq_mp``.
    """
    from tactics import AP_TERM as _APT
    p.goal("!a b. nat0_lt a (SUC0 (n0plus a b))")
    p.fix("a")
    SUC0_C = p._parse("SUC0")
    NAT0_LT_a = p._parse("nat0_lt a")
    with p.induction("b"):
        with p.base():
            p.have("h_base: n0plus a 0 = a").by(N0PLUS_BASE, "a")
            p.have("h_lt: nat0_lt a (SUC0 a)").by(NAT0_LT_SUC0, "a")
            # eq_suc: SUC0 (n0plus a 0) = SUC0 a;
            # eq_lt:  nat0_lt a (SUC0 (n0plus a 0)) = nat0_lt a (SUC0 a).
            eq_suc = _APT(SUC0_C, p.fact("h_base"))
            eq_lt = _APT(NAT0_LT_a, eq_suc)
            p.thus("nat0_lt a (SUC0 (n0plus a 0))").by_eq_mp(eq_lt, "h_lt")
        with p.step("IH"):
            # ``induction("b")`` reuses ``b`` as the step variable.
            p.have(
                "h_step: n0plus a (SUC0 b) = SUC0 (n0plus a b)"
            ).by(N0PLUS_STEP, "a", "b")
            p.have(
                "h_lt_one: nat0_lt (SUC0 (n0plus a b)) (SUC0 (SUC0 (n0plus a b)))"
            ).by(NAT0_LT_SUC0, "SUC0 (n0plus a b)")
            p.have(
                "h_ih_lift: nat0_lt a (SUC0 (SUC0 (n0plus a b)))"
            ).by(NAT0_LT_TRANS, "a", "SUC0 (n0plus a b)",
                 "SUC0 (SUC0 (n0plus a b))", "IH", "h_lt_one")
            eq_suc = _APT(SUC0_C, p.fact("h_step"))
            eq_lt = _APT(NAT0_LT_a, eq_suc)
            p.thus(
                "nat0_lt a (SUC0 (n0plus a (SUC0 b)))"
            ).by_eq_mp(eq_lt, "h_ih_lift")


# ---------------------------------------------------------------------------
# Strict-growth lemma for the Omega-shape:
#   |- !t. nat0_lt (sk_size t) (sk_size (App_t (App_t I_t t) (App_t I_t t)))
#
# Direct computation:
#   sk_size (App_t (App_t I_t t) (App_t I_t t))
#     = SUC0 (n0plus (sk_size (App_t I_t t)) (sk_size (App_t I_t t)))
#                                                       [SK_SIZE_APP]
#   sk_size (App_t I_t t) = SUC0 (n0plus (sk_size I_t) (sk_size t))
#                                                       [SK_SIZE_APP]
# Therefore the result is SUC0 (n0plus (SUC0 X) (SUC0 X)) where
# X = n0plus (sk_size I_t) (sk_size t); each summand strictly exceeds
# ``sk_size t`` by NAT0_LT_SUC0_N0PLUS_L plus one SUC0 wrap.
#
# DSL friction: the chain of "SUC0 lifts" wants a ``nat0_lt_suc0_chain``
# helper; without it we do three NAT0_LT_TRANS hops by hand.  Worth
# packaging if a fourth use-site appears.
# ---------------------------------------------------------------------------


@proof
def NAT0_LT_SUC0_N0PLUS_R(p):
    """|- !a b. nat0_lt b (SUC0 (n0plus a b)).

    The right-summand companion to NAT0_LT_SUC0_N0PLUS_L.  Direct
    induction on ``b``:
      base: nat0_lt 0 (SUC0 (n0plus a 0)) = nat0_lt 0 (SUC0 a);
            standard zero-vs-successor (NAT0_LT_0_SUC0 in nat0_order).
      step: nat0_lt (SUC0 n) (SUC0 (n0plus a (SUC0 n)))
            = nat0_lt (SUC0 n) (SUC0 (SUC0 (n0plus a n))) [N0PLUS_STEP];
            from IH ``nat0_lt n (SUC0 (n0plus a n))`` lift via
            NAT0_LT_SUC0_MONO.
    """
    from nat0_order import NAT0_LT_0_SUC0, NAT0_LT_SUC0_MONO
    from tactics import AP_TERM as _APT
    p.goal("!a b. nat0_lt b (SUC0 (n0plus a b))")
    p.fix("a")
    SUC0_C = p._parse("SUC0")
    with p.induction("b"):
        with p.base():
            p.have("h_base: n0plus a 0 = a").by(N0PLUS_BASE, "a")
            p.have("h_lt: nat0_lt 0 (SUC0 a)").by(NAT0_LT_0_SUC0, "a")
            # eq_suc: SUC0 (n0plus a 0) = SUC0 a; lift via nat0_lt 0.
            NAT0_LT_0 = p._parse("nat0_lt 0")
            eq_suc = _APT(SUC0_C, p.fact("h_base"))
            eq_lt = _APT(NAT0_LT_0, eq_suc)
            p.thus("nat0_lt 0 (SUC0 (n0plus a 0))").by_eq_mp(eq_lt, "h_lt")
        with p.step("IH"):
            p.have(
                "h_step: n0plus a (SUC0 b) = SUC0 (n0plus a b)"
            ).by(N0PLUS_STEP, "a", "b")
            p.have(
                "h_mono: nat0_lt (SUC0 b) (SUC0 (SUC0 (n0plus a b)))"
            ).by(NAT0_LT_SUC0_MONO, "b", "SUC0 (n0plus a b)", "IH")
            NAT0_LT_SUCb = p._parse("nat0_lt (SUC0 b)")
            eq_suc = _APT(SUC0_C, p.fact("h_step"))
            eq_lt = _APT(NAT0_LT_SUCb, eq_suc)
            p.thus(
                "nat0_lt (SUC0 b) (SUC0 (n0plus a (SUC0 b)))"
            ).by_eq_mp(eq_lt, "h_mono")


# ---------------------------------------------------------------------------
# n0plus left-side recursion equations.  ``N0PLUS_BASE``/``N0PLUS_STEP``
# in hf_sets handle the *right* argument (n0plus x 0 = x, n0plus x (SUC0 y)
# = SUC0 (n0plus x y)).  For the SK_ITER_ADD induction on the outer count
# we need the *left*-side mirror.  Each is a small induction on the right
# argument, using the existing right-side equations and AP_TERM(SUC0).
# ---------------------------------------------------------------------------


@proof
def N0PLUS_LEFT_ZERO(p):
    """|- !m. n0plus 0 m = m.

    Induction on m:
      base m=0:  n0plus 0 0 = 0  [N0PLUS_BASE].
      step:      n0plus 0 (SUC0 m) = SUC0 (n0plus 0 m)   [N0PLUS_STEP]
                                   = SUC0 m              [IH, AP_TERM(SUC0)].
    """
    from tactics import AP_TERM as _APT
    p.goal("!m. n0plus 0 m = m")
    SUC0_C = p._parse("SUC0")
    with p.induction("m"):
        with p.base():
            p.thus("n0plus 0 0 = 0").by(N0PLUS_BASE, "0")
        with p.step("IH"):
            p.have(
                "h_step: n0plus 0 (SUC0 m) = SUC0 (n0plus 0 m)"
            ).by(N0PLUS_STEP, "0", "m")
            # AP_TERM SUC0 on IH: SUC0 (n0plus 0 m) = SUC0 m.
            ih_suc = _APT(SUC0_C, p.fact("IH"))
            p.have(
                "ih_suc: SUC0 (n0plus 0 m) = SUC0 m"
            ).by_thm(ih_suc)
            # DSL friction: by_trans for two-step equation chains is
            # cleaner than nested by_thm(TRANS(...)).
            from tactics import TRANS as _TRANS
            p.thus("n0plus 0 (SUC0 m) = SUC0 m").by_thm(
                _TRANS(p.fact("h_step"), p.fact("ih_suc"))
            )


@proof
def N0PLUS_SUC_L(p):
    """|- !n m. n0plus (SUC0 n) m = SUC0 (n0plus n m).

    Induction on m (with n fixed):
      base m=0:  n0plus (SUC0 n) 0 = SUC0 n      [N0PLUS_BASE]
                 SUC0 (n0plus n 0) = SUC0 n      [N0PLUS_BASE + AP_TERM]
                 chain: both = SUC0 n.
      step:      n0plus (SUC0 n) (SUC0 m)
                  = SUC0 (n0plus (SUC0 n) m)     [N0PLUS_STEP]
                  = SUC0 (SUC0 (n0plus n m))     [IH, AP_TERM(SUC0)]
                  = SUC0 (n0plus n (SUC0 m))     [N0PLUS_STEP back + AP_TERM(SUC0)].
    """
    from tactics import AP_TERM as _APT, TRANS as _TRANS, SYM as _SYM
    p.goal("!n m. n0plus (SUC0 n) m = SUC0 (n0plus n m)")
    p.fix("n")
    SUC0_C = p._parse("SUC0")
    with p.induction("m"):
        with p.base():
            # LHS = n0plus (SUC0 n) 0 = SUC0 n by N0PLUS_BASE.
            p.have(
                "h_l: n0plus (SUC0 n) 0 = SUC0 n"
            ).by(N0PLUS_BASE, "SUC0 n")
            # RHS = SUC0 (n0plus n 0) = SUC0 n via N0PLUS_BASE + AP_TERM(SUC0).
            p.have("h_r0: n0plus n 0 = n").by(N0PLUS_BASE, "n")
            h_r_suc = _APT(SUC0_C, p.fact("h_r0"))
            p.have("h_r: SUC0 (n0plus n 0) = SUC0 n").by_thm(h_r_suc)
            # Chain: LHS = SUC0 n = RHS.
            p.thus(
                "n0plus (SUC0 n) 0 = SUC0 (n0plus n 0)"
            ).by_thm(_TRANS(p.fact("h_l"), _SYM(p.fact("h_r"))))
        with p.step("IH"):
            # IH : n0plus (SUC0 n) m = SUC0 (n0plus n m).
            # h_l: n0plus (SUC0 n) (SUC0 m) = SUC0 (n0plus (SUC0 n) m).
            p.have(
                "h_l: n0plus (SUC0 n) (SUC0 m) = SUC0 (n0plus (SUC0 n) m)"
            ).by(N0PLUS_STEP, "SUC0 n", "m")
            # AP_TERM(SUC0) on IH: SUC0 (n0plus (SUC0 n) m) = SUC0 (SUC0 (n0plus n m)).
            ih_suc = _APT(SUC0_C, p.fact("IH"))
            p.have(
                "h_mid: SUC0 (n0plus (SUC0 n) m) = SUC0 (SUC0 (n0plus n m))"
            ).by_thm(ih_suc)
            # AP_TERM(SUC0) on SYM(N0PLUS_STEP at n, m):
            #   SUC0 (SUC0 (n0plus n m)) = SUC0 (n0plus n (SUC0 m)).
            p.have(
                "h_step_r: n0plus n (SUC0 m) = SUC0 (n0plus n m)"
            ).by(N0PLUS_STEP, "n", "m")
            h_r_suc = _APT(SUC0_C, _SYM(p.fact("h_step_r")))
            p.have(
                "h_r: SUC0 (SUC0 (n0plus n m)) = SUC0 (n0plus n (SUC0 m))"
            ).by_thm(h_r_suc)
            # Chain three.
            p.thus(
                "n0plus (SUC0 n) (SUC0 m) = SUC0 (n0plus n (SUC0 m))"
            ).by_thm(_TRANS(p.fact("h_l"), _TRANS(p.fact("h_mid"), p.fact("h_r"))))


@proof
def N0PLUS_ASSOC(p):
    """|- !a b c. n0plus (n0plus a b) c = n0plus a (n0plus b c).

    Standard nat0 associativity.  Induct on ``c`` with ``a, b`` free:
      base c=0:  both sides reduce to ``n0plus a b`` via N0PLUS_BASE
                 (right-arg) applied twice -- on the outer c and on the
                 inner ``n0plus b 0``.
      step:      LHS = SUC0 (n0plus (n0plus a b) c)   [N0PLUS_STEP at outer c]
                     = SUC0 (n0plus a (n0plus b c))   [IH, AP_TERM SUC0]
                 RHS = n0plus a (SUC0 (n0plus b c))   [N0PLUS_STEP inside
                                                       + AP_TERM(n0plus a)]
                     = SUC0 (n0plus a (n0plus b c))   [N0PLUS_STEP].
                 Chain via TRANS.
    """
    from tactics import (
        AP_TERM as _APT,
        TRANS as _TRANS,
        SYM as _SYM,
    )

    p.goal(
        "!a b c. n0plus (n0plus a b) c = n0plus a (n0plus b c)"
    )
    p.fix("a b")
    SUC0_C = p._parse("SUC0")
    n0plus_a = p._parse("n0plus a")
    with p.induction("c"):
        with p.base():
            p.have(
                "h_l: n0plus (n0plus a b) 0 = n0plus a b"
            ).by(N0PLUS_BASE, "n0plus a b")
            p.have("h_b0: n0plus b 0 = b").by(N0PLUS_BASE, "b")
            # AP_TERM(n0plus a) on h_b0: n0plus a (n0plus b 0) = n0plus a b.
            h_r = _APT(n0plus_a, p.fact("h_b0"))
            p.have(
                "h_r: n0plus a (n0plus b 0) = n0plus a b"
            ).by_thm(h_r)
            p.thus(
                "n0plus (n0plus a b) 0 = n0plus a (n0plus b 0)"
            ).by_thm(_TRANS(p.fact("h_l"), _SYM(p.fact("h_r"))))
        with p.step("IH"):
            # LHS step: n0plus (n0plus a b) (SUC0 c) = SUC0 (n0plus (n0plus a b) c).
            p.have(
                "h_l_step: n0plus (n0plus a b) (SUC0 c) "
                "          = SUC0 (n0plus (n0plus a b) c)"
            ).by(N0PLUS_STEP, "n0plus a b", "c")
            # IH lifted by SUC0: SUC0 (n0plus (n0plus a b) c) = SUC0 (n0plus a (n0plus b c)).
            ih_lift = _APT(SUC0_C, p.fact("IH"))
            p.have(
                "h_l_ih: SUC0 (n0plus (n0plus a b) c) "
                "       = SUC0 (n0plus a (n0plus b c))"
            ).by_thm(ih_lift)
            # RHS step: n0plus b (SUC0 c) = SUC0 (n0plus b c); lift by n0plus a.
            p.have(
                "h_bs: n0plus b (SUC0 c) = SUC0 (n0plus b c)"
            ).by(N0PLUS_STEP, "b", "c")
            h_r_inner = _APT(n0plus_a, p.fact("h_bs"))
            p.have(
                "h_r_inner: n0plus a (n0plus b (SUC0 c)) "
                "          = n0plus a (SUC0 (n0plus b c))"
            ).by_thm(h_r_inner)
            # n0plus a (SUC0 (n0plus b c)) = SUC0 (n0plus a (n0plus b c)).
            p.have(
                "h_r_step: n0plus a (SUC0 (n0plus b c)) "
                "         = SUC0 (n0plus a (n0plus b c))"
            ).by(N0PLUS_STEP, "a", "n0plus b c")
            # Chain LHS = ... = SUC0 (n0plus a (n0plus b c)) = ... = RHS.
            p.thus(
                "n0plus (n0plus a b) (SUC0 c) "
                "= n0plus a (n0plus b (SUC0 c))"
            ).by_thm(_TRANS(
                _TRANS(p.fact("h_l_step"), p.fact("h_l_ih")),
                _TRANS(_SYM(p.fact("h_r_step")), _SYM(p.fact("h_r_inner"))),
            ))


@proof
def N0PLUS_DECOMP(p):
    """|- !L n. ~(nat0_lt n L) ==> ?k. n = n0plus k L.

    Decomposition: any ``n >= L`` factors as ``k + L``.  Equivalent to nat0
    subtraction's existence half.  Induct on ``L`` with ``n`` free:

      Base L=0: ?k. n = n0plus k 0 -- witness k := n via N0PLUS_BASE.
      Step L -> SUC0 L: from ~(nat0_lt n (SUC0 L)).
        * n != 0, else ~(nat0_lt 0 (SUC0 L)) contradicts NAT0_LT_0_SUC0.
          NAT0_NEQ_ZERO_PRED gives ?dp. n = SUC0 dp.
        * ~(nat0_lt (SUC0 dp) (SUC0 L)) -- substitute the predecessor form
          into the original hypothesis.
        * Contrapositive of NAT0_LT_SUC0_MONO turns this into
          ~(nat0_lt dp L).
        * IH at dp yields ?k. dp = n0plus k L; lift via SYM(N0PLUS_STEP):
          n = SUC0 dp = SUC0 (n0plus k L) = n0plus k (SUC0 L).

    Used by OMEGA_T_REACHES_LARGE_SIZE to recover the public-form witness
    ``k`` once the depth induction guarantees ``n >= L``.
    """
    from tactics import (
        AP_TERM as _APT,
        TRANS as _TRANS,
        SYM as _SYM,
    )
    from nat0_order import (
        NAT0_LT_0_SUC0,
        NAT0_LT_SUC0_MONO,
        NAT0_NEQ_ZERO_PRED,
    )

    p.goal(
        "!L n. ~(nat0_lt n L) ==> ?k. n = n0plus k L"
    )
    SUC0_C = p._parse("SUC0")
    with p.induction("L"):
        with p.base():
            p.fix("n")
            p.assume("h_not: ~(nat0_lt n 0)")
            # n = n0plus n 0 by N0PLUS_BASE; witness k := n.
            p.have("h_base: n0plus n 0 = n").by(N0PLUS_BASE, "n")
            p.have("h_n_eq: n = n0plus n 0").by_thm(_SYM(p.fact("h_base")))
            p.thus("?k. n = n0plus k 0").by_witness("n", "h_n_eq")
        with p.step("IH"):
            # IH : !n. ~(nat0_lt n L) ==> ?k. n = n0plus k L.
            p.fix("n")
            p.assume("h_not: ~(nat0_lt n (SUC0 L))")
            # n != 0: else NAT0_LT_0_SUC0 contradicts h_not.
            with p.have("h_n_neq_0: ~(n = 0)").proof():
                with p.suppose("h_eq_0: n = 0"):
                    p.have(
                        "h_lt_0_SUC0_L: nat0_lt 0 (SUC0 L)"
                    ).by(NAT0_LT_0_SUC0, "L")
                    # AP_THM rewrite to put n on the LHS of the lt:
                    # nat0_lt 0 (SUC0 L) = nat0_lt n (SUC0 L) under h_eq_0 (SYM).
                    nat0_lt_SUC0_L = p._parse("\\u. nat0_lt u (SUC0 L)")
                    # DSL friction: by_rewrite_of with the choose-style or hypothetical
                    # eq ``h_eq_0: n = 0`` is direction-sensitive.  Use AP_THM on a
                    # constructed lambda to lift the substitution explicitly.
                    from tactics import BETA_CONV
                    # Skip lambda; just AP_TERM nat0_lt then AP_THM at (SUC0 L).
                    from tactics import AP_THM as _AP_THM
                    # nat0_lt n = nat0_lt 0 (AP_TERM nat0_lt h_eq_0).
                    eq_fn = _APT(p._parse("nat0_lt"), p.fact("h_eq_0"))
                    # Then AP_THM at SUC0 L: nat0_lt n (SUC0 L) = nat0_lt 0 (SUC0 L).
                    eq_at = _AP_THM(eq_fn, p._parse("SUC0 L"))
                    p.have(
                        "h_eq_lt: nat0_lt n (SUC0 L) = nat0_lt 0 (SUC0 L)"
                    ).by_thm(eq_at)
                    p.have(
                        "h_lt_at_n: nat0_lt n (SUC0 L)"
                    ).by_eq_mp(_SYM(p.fact("h_eq_lt")), "h_lt_0_SUC0_L")
                    p.absurd().by_conj("h_not", "h_lt_at_n")
            # NAT0_NEQ_ZERO_PRED: ?dp. n = SUC0 dp.
            p.have(
                "h_pred: ?dp:nat0. n = SUC0 dp"
            ).by(NAT0_NEQ_ZERO_PRED, "n", "h_n_neq_0")
            p.choose("dp", from_="h_pred")
            # dp_eq : n = SUC0 dp.

            # Lift h_not to ``~(nat0_lt (SUC0 dp) (SUC0 L))`` by substituting n.
            # Build the rewrite equation via AP_THM(AP_TERM(nat0_lt, dp_eq), SUC0 L).
            from tactics import AP_THM as _AP_THM
            eq_fn = _APT(p._parse("nat0_lt"), p.fact("dp_eq"))
            eq_at = _AP_THM(eq_fn, p._parse("SUC0 L"))
            # eq_at : nat0_lt n (SUC0 L) = nat0_lt (SUC0 dp) (SUC0 L).
            # Apply to h_not's body via AP_TERM(~).  DSL friction: ``~`` does
            # not parse as a standalone term, so build the kernel ``Const("~")``
            # directly with mk_const.
            not_eq = _APT(mk_const("~", []), eq_at)
            # not_eq : ~(nat0_lt n (SUC0 L)) = ~(nat0_lt (SUC0 dp) (SUC0 L)).
            p.have(
                "h_not_succ: ~(nat0_lt (SUC0 dp) (SUC0 L))"
            ).by_eq_mp(not_eq, "h_not")

            # Contrapositive of NAT0_LT_SUC0_MONO turns this into ~(nat0_lt dp L).
            with p.have("h_not_dp_L: ~(nat0_lt dp L)").proof():
                with p.suppose("h_dp_L: nat0_lt dp L"):
                    p.have(
                        "h_succ: nat0_lt (SUC0 dp) (SUC0 L)"
                    ).by(NAT0_LT_SUC0_MONO, "dp", "L", "h_dp_L")
                    p.absurd().by_conj("h_not_succ", "h_succ")

            # Apply IH at dp.
            p.have(
                "h_ih: ?k. dp = n0plus k L"
            ).by("IH", "dp", "h_not_dp_L")
            p.choose("k", from_="h_ih")
            # k_eq : dp = n0plus k L.

            # Build n = n0plus k (SUC0 L):
            #   n = SUC0 dp                        (dp_eq)
            #     = SUC0 (n0plus k L)              (AP_TERM SUC0 k_eq)
            #     = n0plus k (SUC0 L)              (SYM N0PLUS_STEP at k, L).
            suc_k = _APT(SUC0_C, p.fact("k_eq"))
            # suc_k : SUC0 dp = SUC0 (n0plus k L).
            p.have(
                "h_step_eq: n0plus k (SUC0 L) = SUC0 (n0plus k L)"
            ).by(N0PLUS_STEP, "k", "L")
            # Chain: n = SUC0 dp = SUC0 (n0plus k L) = n0plus k (SUC0 L).
            p.have(
                "h_n_eq: n = n0plus k (SUC0 L)"
            ).by_thm(_TRANS(
                p.fact("dp_eq"),
                _TRANS(suc_k, _SYM(p.fact("h_step_eq"))),
            ))
            p.thus("?k. n = n0plus k (SUC0 L)").by_witness("k", "h_n_eq")


# OMEGA_DEPTH_SEQ moved to just before OMEGA_T_REACHES_LARGE_SIZE (it
# references I_pow / Omega_t which are defined later in this file).


@proof
def NAT0_LT_N0PLUS_MONO_R(p):
    """|- !a b c. nat0_lt b c ==> nat0_lt (n0plus a b) (n0plus a c).

    Right-argument strict monotonicity of n0plus.  Induct on ``c`` with
    ``b`` free; the step uses NAT0_LT_SUC0_CASES to split
    ``b < SUC0 c`` into ``b = c`` (NAT0_LT_SUC0) and ``b < c`` (IH +
    NAT0_LT_TRANS).

    Used by OMEGA_TRAJ_I_DEPTH_STEP to convert per-layer size growth
    ``sk_size (I_pow k SII) < sk_size (I_pow (SUC0 k) SII)`` into
    Omega-shape size growth (a = sk_size of an I-application wrapper).
    """
    from nat0_order import (
        NAT0_LT_SUC0,
        NAT0_LT_TRANS,
        NAT0_NOT_LT_ZERO,
        NAT0_LT_SUC0_CASES,
    )
    from tactics import AP_TERM as _APT, TRANS as _TRANS, SYM as _SYM

    p.goal(
        "!a b c. nat0_lt b c ==> nat0_lt (n0plus a b) (n0plus a c)"
    )
    p.fix("a")
    # DSL friction: ``induction("c")`` peels only the outermost forall, but the
    # public statement is ``!a b c.``.  We prove a (c, b)-swapped helper inside
    # ``.proof()`` so c is induct-peelable, then specialize back at the end.
    with p.have(
        "swapped: !c b. nat0_lt b c "
        "        ==> nat0_lt (n0plus a b) (n0plus a c)"
    ).proof():
        with p.induction("c"):
            with p.base():
                # Vacuous: ~(nat0_lt b 0).
                p.fix("b")
                p.assume("h: nat0_lt b 0")
                p.have("h_not: ~(nat0_lt b 0)").by(NAT0_NOT_LT_ZERO, "b")
                p.absurd().by_conj("h_not", "h")
            with p.step("IH"):
                # IH:  !b. nat0_lt b c ==> nat0_lt (n0plus a b) (n0plus a c)
                # Goal: !b. nat0_lt b (SUC0 c) ==>
                #            nat0_lt (n0plus a b) (n0plus a (SUC0 c))
                p.fix("b")
                p.assume("h_lt: nat0_lt b (SUC0 c)")
                p.have(
                    "h_step_R: n0plus a (SUC0 c) = SUC0 (n0plus a c)"
                ).by(N0PLUS_STEP, "a", "c")
                p.have(
                    "h_cases: b = c \\/ nat0_lt b c"
                ).by(NAT0_LT_SUC0_CASES, "b", "c", "h_lt")
                with p.cases_on("h_cases"):
                    with p.case("h_eq: b = c"):
                        # Target collapses to nat0_lt (n0plus a b) (SUC0 (n0plus a b))
                        # after substituting c := b on the right via SYM(h_eq).
                        p.have(
                            "h_succ: nat0_lt (n0plus a b) "
                            "                (SUC0 (n0plus a b))"
                        ).by(NAT0_LT_SUC0, "n0plus a b")
                        # AP_TERM(n0plus a) on h_eq: n0plus a b = n0plus a c.
                        h_n0_eq = _APT(p._parse("n0plus a"), p.fact("h_eq"))
                        # SUC0-wrap: SUC0 (n0plus a b) = SUC0 (n0plus a c).
                        h_suc_n0 = _APT(p._parse("SUC0"), h_n0_eq)
                        # Chain with SYM(h_step_R):
                        #   SUC0 (n0plus a b) = n0plus a (SUC0 c).
                        h_chain = _TRANS(h_suc_n0, _SYM(p.fact("h_step_R")))
                        # AP_TERM(nat0_lt (n0plus a b)) lifts the rhs swap.
                        h_lt_eq = _APT(
                            p._parse("nat0_lt (n0plus a b)"), h_chain
                        )
                        p.thus(
                            "nat0_lt (n0plus a b) "
                            "         (n0plus a (SUC0 c))"
                        ).by_eq_mp(h_lt_eq, "h_succ")
                    with p.case("h_lt_inner: nat0_lt b c"):
                        # IH at b: nat0_lt (n0plus a b) (n0plus a c).
                        p.have(
                            "ih_b: nat0_lt (n0plus a b) (n0plus a c)"
                        ).by("IH", "b", "h_lt_inner")
                        p.have(
                            "h_lt_one: nat0_lt (n0plus a c) "
                            "                   (SUC0 (n0plus a c))"
                        ).by(NAT0_LT_SUC0, "n0plus a c")
                        p.have(
                            "h_trans: nat0_lt (n0plus a b) "
                            "                  (SUC0 (n0plus a c))"
                        ).by(
                            NAT0_LT_TRANS,
                            "n0plus a b",
                            "n0plus a c",
                            "SUC0 (n0plus a c)",
                            "ih_b",
                            "h_lt_one",
                        )
                        # Fold SUC0 (n0plus a c) -> n0plus a (SUC0 c).
                        h_fold = _APT(
                            p._parse("nat0_lt (n0plus a b)"),
                            _SYM(p.fact("h_step_R")),
                        )
                        p.thus(
                            "nat0_lt (n0plus a b) "
                            "         (n0plus a (SUC0 c))"
                        ).by_eq_mp(h_fold, "h_trans")
    # Recover the (a, b, c) public order from swapped (c, b).
    p.fix("b c")
    p.assume("h_bc: nat0_lt b c")
    p.thus(
        "nat0_lt (n0plus a b) (n0plus a c)"
    ).by("swapped", "c", "b", "h_bc")


@proof
def NAT0_LT_N0PLUS_MONO_L(p):
    """|- !a b c. nat0_lt a b ==> nat0_lt (n0plus a c) (n0plus b c).

    Left-argument strict monotonicity of n0plus.  Induct on ``c``:
    base via N0PLUS_BASE (right-arg) folds both summands to a, b;
    step via N0PLUS_STEP + NAT0_LT_SUC0_MONO on the IH.
    """
    from nat0_order import NAT0_LT_SUC0_MONO
    from tactics import (
        AP_TERM as _APT,
        MK_COMB as _MK,
        SYM as _SYM,
    )

    p.goal(
        "!a b c. nat0_lt a b ==> nat0_lt (n0plus a c) (n0plus b c)"
    )
    # DSL friction: same swap as MONO_R -- prove (c, a, b)-ordered helper, then
    # specialize back into the public (a, b, c) order.
    with p.have(
        "swapped: !c a b. nat0_lt a b "
        "        ==> nat0_lt (n0plus a c) (n0plus b c)"
    ).proof():
        with p.induction("c"):
            with p.base():
                # Goal: !a b. nat0_lt a b ==> nat0_lt (n0plus a 0) (n0plus b 0).
                p.fix("a b")
                p.assume("h_lt: nat0_lt a b")
                p.have("h_a: n0plus a 0 = a").by(N0PLUS_BASE, "a")
                p.have("h_b: n0plus b 0 = b").by(N0PLUS_BASE, "b")
                # Build  nat0_lt (n0plus a 0) (n0plus b 0) = nat0_lt a b
                # via MK_COMB(AP_TERM(nat0_lt, h_a), h_b).
                e1 = _APT(p._parse("nat0_lt"), p.fact("h_a"))
                e2 = _MK(e1, p.fact("h_b"))
                p.thus(
                    "nat0_lt (n0plus a 0) (n0plus b 0)"
                ).by_eq_mp(_SYM(e2), "h_lt")
            with p.step("IH"):
                # IH:  !a b. nat0_lt a b ==> nat0_lt (n0plus a c) (n0plus b c)
                # Goal: !a b. nat0_lt a b ==>
                #            nat0_lt (n0plus a (SUC0 c)) (n0plus b (SUC0 c))
                p.fix("a b")
                p.assume("h_lt: nat0_lt a b")
                p.have(
                    "ih_ab: nat0_lt (n0plus a c) (n0plus b c)"
                ).by("IH", "a", "b", "h_lt")
                p.have(
                    "h_mono: nat0_lt (SUC0 (n0plus a c)) "
                    "                (SUC0 (n0plus b c))"
                ).by(
                    NAT0_LT_SUC0_MONO,
                    "n0plus a c",
                    "n0plus b c",
                    "ih_ab",
                )
                p.have(
                    "h_step_a: n0plus a (SUC0 c) = SUC0 (n0plus a c)"
                ).by(N0PLUS_STEP, "a", "c")
                p.have(
                    "h_step_b: n0plus b (SUC0 c) = SUC0 (n0plus b c)"
                ).by(N0PLUS_STEP, "b", "c")
                # nat0_lt (n0plus a (SUC0 c)) (n0plus b (SUC0 c))
                #   = nat0_lt (SUC0 (n0plus a c)) (SUC0 (n0plus b c)).
                e1 = _APT(p._parse("nat0_lt"), p.fact("h_step_a"))
                e2 = _MK(e1, p.fact("h_step_b"))
                p.thus(
                    "nat0_lt (n0plus a (SUC0 c)) "
                    "         (n0plus b (SUC0 c))"
                ).by_eq_mp(e2, "h_mono")
    # Specialize swapped at (c, a, b) to recover (a, b, c) public order.
    p.fix("a b c")
    p.assume("h_ab: nat0_lt a b")
    p.thus(
        "nat0_lt (n0plus a c) (n0plus b c)"
    ).by("swapped", "c", "a", "b", "h_ab")


@proof
def SK_SIZE_GROWTH_OMEGA_SHAPE(p):
    """|- !t. nat0_lt (sk_size t)
                      (sk_size (App_t (App_t I_t t) (App_t I_t t))).

    Two-hop chain via NAT0_LT_TRANS:
      sk_size t
        < sk_size (App_t I_t t)                           [NAT0_LT_SUC0_N0PLUS_R]
        < sk_size (App_t (App_t I_t t) (App_t I_t t))     [NAT0_LT_SUC0_N0PLUS_L]
    """
    p.goal(
        "!t. nat0_lt (sk_size t) "
        "             (sk_size (App_t (App_t I_t t) (App_t I_t t)))"
    )
    p.fix("t")

    # Step 1: sk_size (App_t I_t t) = SUC0 (n0plus (sk_size I_t) (sk_size t)).
    p.have(
        "sz_It: sk_size (App_t I_t t) "
        "       = SUC0 (n0plus (sk_size I_t) (sk_size t))"
    ).by(SK_SIZE_APP, "I_t", "t")

    # sk_size t < SUC0 (n0plus (sk_size I_t) (sk_size t)) [_R at a=sk_size I_t, b=sk_size t].
    p.have(
        "h_lt_It_pre: nat0_lt (sk_size t) "
        "             (SUC0 (n0plus (sk_size I_t) (sk_size t)))"
    ).by(NAT0_LT_SUC0_N0PLUS_R, "sk_size I_t", "sk_size t")

    # Fold RHS to sk_size (App_t I_t t).
    p.have(
        "h_lt_It: nat0_lt (sk_size t) (sk_size (App_t I_t t))"
    ).by_rewrite_of("h_lt_It_pre", [SYM(p.fact("sz_It"))])

    # Step 2: sk_size (App_t (App_t I_t t) (App_t I_t t))
    #         = SUC0 (n0plus (sk_size (App_t I_t t)) (sk_size (App_t I_t t))).
    p.have(
        "sz_top: sk_size (App_t (App_t I_t t) (App_t I_t t)) "
        "        = SUC0 (n0plus (sk_size (App_t I_t t)) (sk_size (App_t I_t t)))"
    ).by(SK_SIZE_APP, "App_t I_t t", "App_t I_t t")

    # sk_size (App_t I_t t) < SUC0 (n0plus (sk_size (App_t I_t t)) (sk_size (App_t I_t t)))
    # [_L at a=sk_size (App_t I_t t), b=sk_size (App_t I_t t)].
    p.have(
        "h_lt_top_pre: nat0_lt (sk_size (App_t I_t t)) "
        "              (SUC0 (n0plus (sk_size (App_t I_t t)) (sk_size (App_t I_t t))))"
    ).by(NAT0_LT_SUC0_N0PLUS_L, "sk_size (App_t I_t t)", "sk_size (App_t I_t t)")
    p.have(
        "h_lt_top: nat0_lt (sk_size (App_t I_t t)) "
        "                   (sk_size (App_t (App_t I_t t) (App_t I_t t)))"
    ).by_rewrite_of("h_lt_top_pre", [SYM(p.fact("sz_top"))])

    # Chain: sk_size t < sk_size (App_t I_t t) < sk_size (App_t (App_t I_t t) ...).
    p.thus(
        "nat0_lt (sk_size t) (sk_size (App_t (App_t I_t t) (App_t I_t t)))"
    ).by(
        NAT0_LT_TRANS,
        "sk_size t",
        "sk_size (App_t I_t t)",
        "sk_size (App_t (App_t I_t t) (App_t I_t t))",
        "h_lt_It",
        "h_lt_top",
    )


# ---------------------------------------------------------------------------
# Size-monotone irreflexivity helpers.
#
# Used to discharge ``not_self`` hypotheses of the form
# ``~(t = App_t ... t ...)`` by showing the App-wrapped term has strictly
# greater sk_size than ``t``.  The hypotheses appear in Y_FIXED_POINT's
# trace where ``t`` is universally quantified (an arbitrary SK term),
# so the usual APP_T_INJ + atom-tag-clash discharge doesn't apply.
# ---------------------------------------------------------------------------


@proof
def SK_SIZE_LT_APP_LEFT(p):
    """|- !t u. nat0_lt (sk_size t) (sk_size (App_t t u)).

    Wrapping a term as the left child of an App strictly grows sk_size.
    Direct: SK_SIZE_APP unfolds the RHS to
    ``SUC0 (n0plus (sk_size t) (sk_size u))``, then
    NAT0_LT_SUC0_N0PLUS_L at (a := sk_size t, b := sk_size u).
    """
    p.goal("!t u. nat0_lt (sk_size t) (sk_size (App_t t u))")
    p.fix("t u")

    # Unfold sk_size on the App_t.
    p.have(
        "sz_app: sk_size (App_t t u) "
        "        = SUC0 (n0plus (sk_size t) (sk_size u))"
    ).by(SK_SIZE_APP, "t", "u")

    # NAT0_LT_SUC0_N0PLUS_L gives the lt in unfolded form.
    p.have(
        "h_pre: nat0_lt (sk_size t) "
        "       (SUC0 (n0plus (sk_size t) (sk_size u)))"
    ).by(NAT0_LT_SUC0_N0PLUS_L, "sk_size t", "sk_size u")

    # DSL friction: by_rewrite_of orients each rule LHS -> RHS, so to fold
    # ``SUC0 (n0plus ...)`` back into ``sk_size (App_t t u)`` we have to
    # feed ``SYM(sz_app)`` rather than ``sz_app``.  A ``by_rewrite_of``
    # variant that auto-orients (mirroring _simp_require's sym tolerance)
    # would remove this small ceremony at every size-fold call site.
    p.thus(
        "nat0_lt (sk_size t) (sk_size (App_t t u))"
    ).by_rewrite_of("h_pre", [SYM(p.fact("sz_app"))])


@proof
def SK_SIZE_LT_APP_RIGHT(p):
    """|- !t u. nat0_lt (sk_size t) (sk_size (App_t u t)).

    Wrapping a term as the *right* child of an App strictly grows
    sk_size.  Mirror of SK_SIZE_LT_APP_LEFT via NAT0_LT_SUC0_N0PLUS_R.
    """
    p.goal("!t u. nat0_lt (sk_size t) (sk_size (App_t u t))")
    p.fix("t u")

    p.have(
        "sz_app: sk_size (App_t u t) "
        "        = SUC0 (n0plus (sk_size u) (sk_size t))"
    ).by(SK_SIZE_APP, "u", "t")

    p.have(
        "h_pre: nat0_lt (sk_size t) "
        "       (SUC0 (n0plus (sk_size u) (sk_size t)))"
    ).by(NAT0_LT_SUC0_N0PLUS_R, "sk_size u", "sk_size t")

    # Same fold-back via SYM(sz_app) as in SK_SIZE_LT_APP_LEFT.
    p.thus(
        "nat0_lt (sk_size t) (sk_size (App_t u t))"
    ).by_rewrite_of("h_pre", [SYM(p.fact("sz_app"))])


@proof
def SK_SIZE_LT_DEEP_LEFT(p):
    """|- !t u v. nat0_lt (sk_size t) (sk_size (App_t (App_t u t) v)).

    Depth-2 size growth: wrapping ``t`` as the right child of an inner
    App and then as the left child of an outer App strictly grows
    sk_size by two SUC0/n0plus hops.

    Two-hop chain via NAT0_LT_TRANS:
      sk_size t
        < sk_size (App_t u t)                  [SK_SIZE_LT_APP_RIGHT]
        < sk_size (App_t (App_t u t) v)        [SK_SIZE_LT_APP_LEFT]

    Discharges Step 7 of Y_FIXED_POINT: the SK_STEP_K_UNDER_LEFT guard
    ``~(f = App_t (App_t K_t f) (App_t (App_t K_t ARG) f))`` follows by
    AP_TERM(sk_size) + NAT0_LT_NOT_REFL on this chain.
    """
    p.goal(
        "!t u v. nat0_lt (sk_size t) "
        "                (sk_size (App_t (App_t u t) v))"
    )
    p.fix("t u v")

    # Hop 1: sk_size t < sk_size (App_t u t).
    # DSL friction: SK_SIZE_LT_APP_RIGHT is stated as ``!t u. ... App_t u t``,
    # so the SPEC order is (t-arg-of-lemma := t, u-arg-of-lemma := u);
    # the position of the *wrapped* variable in the conclusion is the
    # first bound name regardless of which child it lives at.  A
    # SK_SIZE_LT_APP variant that took (wrapper, wrapped) in surface
    # order would read more naturally at call sites.
    p.have(
        "h_inner: nat0_lt (sk_size t) (sk_size (App_t u t))"
    ).by(SK_SIZE_LT_APP_RIGHT, "t", "u")

    # Hop 2: sk_size (App_t u t) < sk_size (App_t (App_t u t) v).
    p.have(
        "h_outer: nat0_lt (sk_size (App_t u t)) "
        "                 (sk_size (App_t (App_t u t) v))"
    ).by(SK_SIZE_LT_APP_LEFT, "App_t u t", "v")

    # Compose via NAT0_LT_TRANS.  DSL friction: NAT0_LT_TRANS requires
    # all three witness terms spelled out (a, b, c) before the two
    # ordering facts -- a ``by_match`` overload that infers the middle
    # term from the two facts' shapes would save the verbose middle
    # ``sk_size (App_t u t)`` repetition here.
    p.thus(
        "nat0_lt (sk_size t) (sk_size (App_t (App_t u t) v))"
    ).by(
        NAT0_LT_TRANS,
        "sk_size t",
        "sk_size (App_t u t)",
        "sk_size (App_t (App_t u t) v)",
        "h_inner",
        "h_outer",
    )


# ---------------------------------------------------------------------------
# Self-inequality wrappers (irreflexivity corollaries).
#
# Each ~(t = App-expr containing t) follows from the matching
# SK_SIZE_LT_* lemma via AP_TERM(sk_size) + NAT0_LT_NOT_REFL.  These are
# the call-site form actually used to discharge SK_STEP_*_UNDER_LEFT
# not_self hypotheses when ``t`` is universally quantified (no atom-tag
# clash available).
# ---------------------------------------------------------------------------


from nat0_order import NAT0_LT_NOT_REFL  # noqa: E402


@proof
def SK_NEQ_APP_LEFT_WRAP(p):
    """|- !t u. ~(t = App_t t u).

    AP_TERM(sk_size) + SK_SIZE_LT_APP_LEFT + NAT0_LT_NOT_REFL.
    """
    p.goal("!t u. ~(t = App_t t u)")
    p.fix("t u")
    with p.suppose("h_eq: t = App_t t u"):
        # AP_TERM(sk_size, h_eq) lifts h_eq through the sk_size head.
        # DSL friction: AP_TERM is a raw tactic; ``by_cong(sk_size, "h_eq")``
        # ought to do the same with a friendlier label, but the current
        # by_cong dispatch (§4) needs a Var/Const head term first --
        # ``sk_size`` is a Const here, so it works, but the spelling
        # ``by_thm(AP_TERM(sk_size, p.fact("h_eq")))`` is what existing
        # call sites use (cf. OMEGA_NON_HALTING line 3771), so we follow.
        p.have(
            "h_size_eq: sk_size t = sk_size (App_t t u)"
        ).by_thm(AP_TERM(sk_size, p.fact("h_eq")))
        p.have(
            "h_lt: nat0_lt (sk_size t) (sk_size (App_t t u))"
        ).by(SK_SIZE_LT_APP_LEFT, "t", "u")
        # Fold ``sk_size (App_t t u)`` in h_lt back to ``sk_size t`` via
        # SYM(h_size_eq) -- the same SYM-fold ceremony as in the size
        # lemmas above.
        p.have(
            "h_lt_self: nat0_lt (sk_size t) (sk_size t)"
        ).by_rewrite_of("h_lt", [SYM(p.fact("h_size_eq"))])
        p.have(
            "h_nrefl: ~(nat0_lt (sk_size t) (sk_size t))"
        ).by(NAT0_LT_NOT_REFL, "sk_size t")
        p.absurd().by_conj("h_nrefl", "h_lt_self")


@proof
def SK_NEQ_APP_RIGHT_WRAP(p):
    """|- !t u. ~(t = App_t u t).

    Mirror of SK_NEQ_APP_LEFT_WRAP via SK_SIZE_LT_APP_RIGHT.
    """
    p.goal("!t u. ~(t = App_t u t)")
    p.fix("t u")
    with p.suppose("h_eq: t = App_t u t"):
        p.have(
            "h_size_eq: sk_size t = sk_size (App_t u t)"
        ).by_thm(AP_TERM(sk_size, p.fact("h_eq")))
        p.have(
            "h_lt: nat0_lt (sk_size t) (sk_size (App_t u t))"
        ).by(SK_SIZE_LT_APP_RIGHT, "t", "u")
        p.have(
            "h_lt_self: nat0_lt (sk_size t) (sk_size t)"
        ).by_rewrite_of("h_lt", [SYM(p.fact("h_size_eq"))])
        p.have(
            "h_nrefl: ~(nat0_lt (sk_size t) (sk_size t))"
        ).by(NAT0_LT_NOT_REFL, "sk_size t")
        p.absurd().by_conj("h_nrefl", "h_lt_self")


@proof
def SK_NEQ_DEEP_LEFT_WRAP(p):
    """|- !t u v. ~(t = App_t (App_t u t) v).

    The call-site form used at Step 7 of Y_FIXED_POINT.  AP_TERM(sk_size)
    + SK_SIZE_LT_DEEP_LEFT + NAT0_LT_NOT_REFL.
    """
    p.goal("!t u v. ~(t = App_t (App_t u t) v)")
    p.fix("t u v")
    with p.suppose("h_eq: t = App_t (App_t u t) v"):
        p.have(
            "h_size_eq: sk_size t = sk_size (App_t (App_t u t) v)"
        ).by_thm(AP_TERM(sk_size, p.fact("h_eq")))
        p.have(
            "h_lt: nat0_lt (sk_size t) (sk_size (App_t (App_t u t) v))"
        ).by(SK_SIZE_LT_DEEP_LEFT, "t", "u", "v")
        p.have(
            "h_lt_self: nat0_lt (sk_size t) (sk_size t)"
        ).by_rewrite_of("h_lt", [SYM(p.fact("h_size_eq"))])
        p.have(
            "h_nrefl: ~(nat0_lt (sk_size t) (sk_size t))"
        ).by(NAT0_LT_NOT_REFL, "sk_size t")
        p.absurd().by_conj("h_nrefl", "h_lt_self")


# ---------------------------------------------------------------------------
# Python helper: discharge the SK_STEP_S_UNDER_LEFT not_self hypothesis.
#
# Every call to SK_STEP_S_UNDER_LEFT at SPEC (x, y, z, w) leaves the
# user owing
#   ~(App_t (App_t x z) (App_t y z) = App_t (App_t (App_t S_t x) y) z).
# The discharge is structurally identical at every site (and depends
# only on z, never on x or y):
#   * APP_T_INJ peels the equation to two conjuncts.
#   * The right conjunct ``App_t y z = z`` is rejected by
#     SK_NEQ_APP_RIGHT_WRAP at (t := z, u := y) -- the wrapped term
#     can't equal its own subterm regardless of what y is.
# Used 3x in Y_FIXED_POINT (Steps 1, 3, 5) and any other lifted-S call.
# ---------------------------------------------------------------------------


def _discharge_s_under_left_not_self(p, x, y, z, *, label):
    """Register ``label`` proving ~(App_t (App_t x z) (App_t y z) =
    App_t (App_t (App_t S_t x) y) z).

    ``x``, ``y``, ``z`` are term strings (parsed in scope).  The proof
    needs no structural assumption on x or y -- the contradiction lives
    in the right conjunct (``App_t y z = z``), which is always size-
    impossible by SK_NEQ_APP_RIGHT_WRAP.

    DSL friction noted: this is a *Python* helper, not a proof
    combinator.  The DSL has no mechanism to package "a frame-local
    sub-proof that registers one fact" as a first-class lemma
    parameterised by terms; pattern handlers (§9 register_pattern_handler)
    plug into ``assume`` rather than ``have``.  An ``@have_macro``
    decorator that lets a Python function emit a sequence of have/with
    blocks targeted at a specific not_self shape would let this live as
    a tactic rather than a free function.
    """
    from tactics import CONJUNCT2 as _C2
    # DSL friction: term-string composition is by raw f-string concat,
    # so non-atomic substitutes (e.g. ``x = "App_t K_t a"``) must be
    # parenthesised at every interpolation -- otherwise the parser sees
    # juxtaposed atoms (``App_t App_t K_t a``) which left-associates
    # wrongly.  A ``mk_app("App_t", *parts)`` term-builder would do this
    # at the term layer; for now we wrap inline.
    px, py, pz = f"({x})", f"({y})", f"({z})"
    contract = f"App_t (App_t {px} {pz}) (App_t {py} {pz})"
    redex = f"App_t (App_t (App_t S_t {px}) {py}) {pz}"
    with p.have(f"{label}: ~({contract} = {redex})").proof():
        with p.suppose(f"h_eq: {contract} = {redex}"):
            # Peel top App_t: contract = App_t (App_t x z) (App_t y z),
            # redex = App_t (App_t (App_t S_t x) y) z.
            p.have(
                f"e1: App_t {px} {pz} = App_t (App_t S_t {px}) {py} /\\ "
                f"    App_t {py} {pz} = {pz}"
            ).by(
                APP_T_INJ,
                f"App_t {px} {pz}", f"App_t {py} {pz}",
                f"App_t (App_t S_t {px}) {py}", pz,
                "h_eq",
            )
            # Right conjunct: ``App_t y z = z`` -- contradicts
            # SK_NEQ_APP_RIGHT_WRAP applied at (t := z, u := y).
            p.have(f"e_yz: App_t {py} {pz} = {pz}").by_thm(
                _C2(p.fact("e1"))
            )
            # DSL friction: ``by_conj`` matches P/~P by syntactic shape
            # only -- it does NOT auto-SYM the equation, so we have to
            # flip ``e_yz`` manually before pairing with the
            # ``~(z = App_t y z)`` form returned by SK_NEQ_APP_RIGHT_WRAP.
            # _simp_require's SYM tolerance (§4) helps inside
            # have/thus finishing but not inside ``by_conj``.
            p.have(f"e_zy: {pz} = App_t {py} {pz}").by_thm(SYM(p.fact("e_yz")))
            p.have(f"z_neq: ~({pz} = App_t {py} {pz})").by(
                SK_NEQ_APP_RIGHT_WRAP, pz, py
            )
            p.absurd().by_conj("z_neq", "e_zy")


@proof
def OMEGA_T_STEP1(p):
    """|- sk_step Omega_t =
           App_t (App_t I_t (App_t (App_t S_t I_t) I_t))
                 (App_t I_t (App_t (App_t S_t I_t) I_t)).

    Note (Stage 1 rework already shipped): the historical
    ``OMEGA_T_SELF_LOOP`` aimed to state ``sk_step Omega_t =
    Omega_t``.  That equation is provably FALSE in any standard SK
    reduction semantics (Omega has multiple head steps per cycle, and
    under our leftmost-outermost congruence ``sk_step`` the cycle
    even strictly grows -- see OMEGA_NON_HALTING).  Replaced with the
    concrete one-step theorem instead.

    Direct computation via SK_STEP_S:
      Omega_t = App_t (App_t (App_t S_t I_t) I_t) SII   [OMEGA_T_DEF]
              = an S-redex with x=I_t, y=I_t, z=SII
      sk_step Omega_t = App_t (App_t I_t SII) (App_t I_t SII)
                                                        [by SK_STEP_S]
    where SII = App_t (App_t S_t I_t) I_t.
    """
    # DSL friction: ``by_rewrite_of`` with ``SYM(OMEGA_T_DEF)`` folds
    # the unfolded App_t-SII-SII shape on the LHS back to ``Omega_t``.
    # No friction in the small; the surrounding analysis (computing
    # the actual step) was the hard part, not the proof.
    SII = "App_t (App_t S_t I_t) I_t"
    p.goal(
        "sk_step Omega_t = "
        f"App_t (App_t I_t ({SII})) (App_t I_t ({SII}))"
    )
    # SK_STEP_S at x=I_t, y=I_t, z=SII:
    #   sk_step (App_t (App_t (App_t S_t I_t) I_t) SII)
    #     = App_t (App_t I_t SII) (App_t I_t SII).
    p.have(
        f"step_S: sk_step (App_t (App_t (App_t S_t I_t) I_t) ({SII})) "
        f"         = App_t (App_t I_t ({SII})) (App_t I_t ({SII}))"
    ).by(SK_STEP_S, "I_t", "I_t", SII)
    # Fold App_t SII SII on the LHS back to Omega_t via SYM(OMEGA_T_DEF).
    p.thus(
        "sk_step Omega_t = "
        f"App_t (App_t I_t ({SII})) (App_t I_t ({SII}))"
    ).by_rewrite_of("step_S", [SYM(OMEGA_T_DEF)])


# ---------------------------------------------------------------------------
# halts shift lemmas.  Two general-purpose facts about the
# ``sk_iter``/``halts`` interaction:
#
#   SK_ITER_PUSH   :  |- !n t. sk_iter (SUC0 n) t = sk_iter n (sk_step t)
#                   -- commute one sk_step from the outside to the
#                      inside of an iter (or vice versa via SYM).
#   HALTS_SK_STEP  :  |- !t. halts t = halts (sk_step t)
#                   -- halting is preserved going both directions across
#                      a single sk_step.
#
# Used by the eventual OMEGA_NON_HALTING reasoning to shift the
# fixed-point witness between iterates.
# ---------------------------------------------------------------------------


@proof
def SK_ITER_PUSH(p):
    """|- !n t. sk_iter (SUC0 n) t = sk_iter n (sk_step t).

    Commute sk_step in and out of sk_iter.  Induction on ``n``:
      base: sk_iter 1 t = sk_step t = sk_iter 0 (sk_step t).
      step: sk_iter (SUC0 (SUC0 n)) t
            = sk_step (sk_iter (SUC0 n) t)                 [SK_ITER_SUC]
            = sk_step (sk_iter n (sk_step t))              [IH]
            = sk_iter (SUC0 n) (sk_step t).                [SK_ITER_SUC, SYM].
    """
    from tactics import TRANS
    p.goal("!n t. sk_iter (SUC0 n) t = sk_iter n (sk_step t)")
    with p.induction("n"):
        with p.base():
            p.fix("t")
            # sk_iter 1 t = sk_step (sk_iter 0 t) = sk_step t.
            p.have(
                "h_iter1: sk_iter (SUC0 0) t = sk_step (sk_iter 0 t)"
            ).by(SK_ITER_SUC, "0", "t")
            p.have("h_zero: sk_iter 0 t = t").by(SK_ITER_ZERO, "t")
            p.have(
                "h_iter1_simp: sk_iter (SUC0 0) t = sk_step t"
            ).by_rewrite_of("h_iter1", ["h_zero"])
            # sk_iter 0 (sk_step t) = sk_step t.
            p.have(
                "h_zero_st: sk_iter 0 (sk_step t) = sk_step t"
            ).by(SK_ITER_ZERO, "sk_step t")
            # Combine.
            p.thus(
                "sk_iter (SUC0 0) t = sk_iter 0 (sk_step t)"
            ).by_thm(TRANS(p.fact("h_iter1_simp"), SYM(p.fact("h_zero_st"))))
        with p.step("IH"):
            p.fix("t")
            # sk_iter (SUC0 (SUC0 n)) t = sk_step (sk_iter (SUC0 n) t).
            p.have(
                "h_unfold: sk_iter (SUC0 (SUC0 n)) t "
                "          = sk_step (sk_iter (SUC0 n) t)"
            ).by(SK_ITER_SUC, "SUC0 n", "t")
            # IH at t: sk_iter (SUC0 n) t = sk_iter n (sk_step t).
            p.have(
                "h_ih: sk_iter (SUC0 n) t = sk_iter n (sk_step t)"
            ).by("IH", "t")
            # Replace inner sk_iter (SUC0 n) t with sk_iter n (sk_step t).
            p.have(
                "h_mid: sk_iter (SUC0 (SUC0 n)) t "
                "       = sk_step (sk_iter n (sk_step t))"
            ).by_rewrite_of("h_unfold", ["h_ih"])
            # sk_step (sk_iter n (sk_step t)) = sk_iter (SUC0 n) (sk_step t).
            p.have(
                "h_fold: sk_iter (SUC0 n) (sk_step t) "
                "        = sk_step (sk_iter n (sk_step t))"
            ).by(SK_ITER_SUC, "n", "sk_step t")
            p.thus(
                "sk_iter (SUC0 (SUC0 n)) t = sk_iter (SUC0 n) (sk_step t)"
            ).by_thm(TRANS(p.fact("h_mid"), SYM(p.fact("h_fold"))))


# ---------------------------------------------------------------------------
# is_normal propagation under sk_iter, in both directions:
#
#   IS_NORMAL_SK_ITER_FIXED :  |- !n t. is_normal t ==> sk_iter n t = t
#                              -- a normal-form fixed point of sk_step is
#                                 also a fixed point of every sk_iter.
#   IS_NORMAL_SK_STEP       :  |- !t. is_normal t ==> is_normal (sk_step t)
#                              -- normality is preserved by sk_step
#                                 (trivially: sk_step t = t).
#   HALTS_SK_STEP_FWD       :  |- !t. halts t ==> halts (sk_step t)
#                              -- shift halts witness forward by one step.
#
# These are weak enough not to close OMEGA_NON_HALTING on their own
# (the backward direction halts (sk_step t) ==> halts t would also
# be needed, and the heart of the proof is still the 3-step cycle
# computation -- see OMEGA_NON_HALTING's docstring), but they form
# the structural skeleton around the missing trajectory lemma.
# ---------------------------------------------------------------------------


@proof
def IS_NORMAL_SK_STEP(p):
    """|- !t. is_normal t ==> is_normal (sk_step t).

    Trivial: if sk_step t = t, then sk_step (sk_step t) = sk_step t
    (apply sk_step to both sides), so sk_step t is also a fixed point.
    """
    from tactics import AP_TERM, TRANS
    p.goal("!t. is_normal t ==> is_normal (sk_step t)")
    p.fix("t")
    p.assume("h_norm: is_normal t")
    p.have("h_fixed: sk_step t = t").by(
        IS_NORMAL_IMP_FIXED, "t", "h_norm"
    )
    # AP_TERM sk_step h_fixed : sk_step (sk_step t) = sk_step t.
    p.have("h_step_fixed: sk_step (sk_step t) = sk_step t").by_thm(
        AP_TERM(sk_step, p.fact("h_fixed"))
    )
    # is_normal (sk_step t) unfolds to sk_step (sk_step t) = sk_step t.
    p.thus("is_normal (sk_step t)").by_unfold(
        "h_step_fixed", IS_NORMAL_DEF
    )


@proof
def IS_NORMAL_SK_ITER_FIXED(p):
    """|- !n t. is_normal t ==> sk_iter n t = t.

    Induction on ``n``:
      base: sk_iter 0 t = t                                   [SK_ITER_ZERO].
      step: sk_iter (SUC0 n) t = sk_step (sk_iter n t)
                                = sk_step t                   [IH]
                                = t                           [is_normal].
    """
    from tactics import TRANS
    p.goal("!n t. is_normal t ==> sk_iter n t = t")
    with p.induction("n"):
        with p.base():
            p.fix("t")
            p.assume("h_norm: is_normal t")
            p.thus("sk_iter 0 t = t").by(SK_ITER_ZERO, "t")
        with p.step("IH"):
            p.fix("t")
            p.assume("h_norm: is_normal t")
            p.have(
                "h_unfold: sk_iter (SUC0 n) t = sk_step (sk_iter n t)"
            ).by(SK_ITER_SUC, "n", "t")
            p.have("h_ih: sk_iter n t = t").by("IH", "t", "h_norm")
            # Rewrite ``sk_iter n t`` to ``t`` in h_unfold's RHS via h_ih.
            p.have(
                "h_step_t: sk_iter (SUC0 n) t = sk_step t"
            ).by_rewrite_of("h_unfold", ["h_ih"])
            p.have("h_fixed: sk_step t = t").by(
                IS_NORMAL_IMP_FIXED, "t", "h_norm"
            )
            p.thus("sk_iter (SUC0 n) t = t").by_thm(
                TRANS(p.fact("h_step_t"), p.fact("h_fixed"))
            )


@proof
def HALTS_SK_STEP_FWD(p):
    """|- !t. halts t ==> halts (sk_step t).

    Two cases on the halts witness ``n``:
      n = 0:        is_normal t ==> is_normal (sk_step t)     [IS_NORMAL_SK_STEP].
      n > 0 = SUC0 m: sk_iter (SUC0 m) t = sk_iter m (sk_step t)
                                                              [SK_ITER_PUSH],
                      so is_normal (sk_iter m (sk_step t)).

    To avoid a NAT0_CASES helper (not in the codebase), we
    pre-derive ``is_normal (sk_iter n t) ==> halts (sk_step t)``
    by induction on ``n``, where the base AND step both yield
    explicit halts-witnesses.
    """
    from tactics import AP_TERM
    # Helper inducted on n: |- !n t. is_normal (sk_iter n t) ==> halts (sk_step t).
    @proof
    def _NORMAL_IMP_HALTS_STEP(p2):
        p2.goal("!n t. is_normal (sk_iter n t) ==> halts (sk_step t)")
        with p2.induction("n"):
            with p2.base():
                p2.fix("t")
                p2.assume("h_norm0: is_normal (sk_iter 0 t)")
                # sk_iter 0 t = t, so h_norm0 = is_normal t.
                p2.have("h_iter0: sk_iter 0 t = t").by(SK_ITER_ZERO, "t")
                p2.have("h_norm_t: is_normal t").by_rewrite_of(
                    "h_norm0", ["h_iter0"]
                )
                # IS_NORMAL_SK_STEP: is_normal (sk_step t).
                p2.have("h_norm_st: is_normal (sk_step t)").by(
                    IS_NORMAL_SK_STEP, "t", "h_norm_t"
                )
                # halts (sk_step t) = ?m. is_normal (sk_iter m (sk_step t)); witness m=0.
                p2.have(
                    "h_at: halts (sk_step t) = (?m. is_normal (sk_iter m (sk_step t)))"
                ).by(HALTS_AT, "sk_step t")
                # sk_iter 0 (sk_step t) = sk_step t.
                p2.have(
                    "h_iter0_st: sk_iter 0 (sk_step t) = sk_step t"
                ).by(SK_ITER_ZERO, "sk_step t")
                # is_normal (sk_iter 0 (sk_step t)).
                p2.have(
                    "h_norm_iter0: is_normal (sk_iter 0 (sk_step t))"
                ).by_eq_mp(
                    AP_TERM(is_normal, p2.fact("h_iter0_st")),
                    "h_norm_st",
                )
                p2.have(
                    "h_ex: ?m. is_normal (sk_iter m (sk_step t))"
                ).by_witness("0", "h_norm_iter0")
                p2.thus("halts (sk_step t)").by_eq_mp("h_at", "h_ex")
            with p2.step("IH"):
                p2.fix("t")
                p2.assume("h_norm: is_normal (sk_iter (SUC0 n) t)")
                # SK_ITER_PUSH: sk_iter (SUC0 n) t = sk_iter n (sk_step t).
                p2.have(
                    "h_push: sk_iter (SUC0 n) t = sk_iter n (sk_step t)"
                ).by(SK_ITER_PUSH, "n", "t")
                # is_normal (sk_iter n (sk_step t)).
                p2.have(
                    "h_norm_pushed: is_normal (sk_iter n (sk_step t))"
                ).by_eq_mp(
                    AP_TERM(is_normal, p2.fact("h_push")),
                    "h_norm",
                )
                p2.have(
                    "h_at: halts (sk_step t) = (?m. is_normal (sk_iter m (sk_step t)))"
                ).by(HALTS_AT, "sk_step t")
                p2.have(
                    "h_ex: ?m. is_normal (sk_iter m (sk_step t))"
                ).by_witness("n", "h_norm_pushed")
                p2.thus("halts (sk_step t)").by_eq_mp("h_at", "h_ex")

    p.goal("!t. halts t ==> halts (sk_step t)")
    p.fix("t")
    p.assume("h_ht: halts t")
    p.have("h_at: halts t = (?n. is_normal (sk_iter n t))").by(HALTS_AT, "t")
    p.have("h_ex: ?n. is_normal (sk_iter n t)").by_eq_mp("h_at", "h_ht")
    p.choose("n", from_="h_ex")
    # n_eq : is_normal (sk_iter n t)
    p.thus("halts (sk_step t)").by(_NORMAL_IMP_HALTS_STEP, "n", "t", "n_eq")


# ---------------------------------------------------------------------------
# Trajectory step lemmas for the Omega-shape.
#
#   SK_STEP_I_APP            :  |- !X. sk_step (App_t I_t X)
#                                    = App_t (App_t K_t X) (App_t K_t X)
#       I_t = App_t (App_t S_t K_t) K_t, so ``App_t I_t X`` is an
#       S-redex (in disguise) with x=K_t, y=K_t, z=X.
#
#   TRAJ_STEP_OMEGA_SHAPE    :  |- !X. sk_step (App_t (App_t I_t X) (App_t I_t X))
#                                    = App_t (App_t (App_t K_t X) (App_t K_t X))
#                                            (App_t I_t X)
#       Top is App_t a b with a = b = App_t I_t X, neither K- nor
#       S-redex at top (I_t doesn't unify with K_t or App_t S_t _),
#       so D3 fires.  ``sk_step a`` reduces via SK_STEP_I_APP, so
#       descend-L wins.
# ---------------------------------------------------------------------------


@proof
def SK_STEP_I_APP(p):
    """|- !X. sk_step (App_t I_t X) = App_t (App_t K_t X) (App_t K_t X).

    Unfold I_t via I_T_DEF to expose an S-redex with x=K_t, y=K_t, z=X;
    apply SK_STEP_S; fold ``App_t (App_t S_t K_t) K_t`` back to I_t.
    """
    p.goal("!X. sk_step (App_t I_t X) = App_t (App_t K_t X) (App_t K_t X)")
    p.fix("X")
    p.have(
        "step_S: sk_step (App_t (App_t (App_t S_t K_t) K_t) X) "
        "        = App_t (App_t K_t X) (App_t K_t X)"
    ).by(SK_STEP_S, "K_t", "K_t", "X")
    p.thus(
        "sk_step (App_t I_t X) = App_t (App_t K_t X) (App_t K_t X)"
    ).by_rewrite_of("step_S", [SYM(I_T_DEF)])


@proof
def TRAJ_STEP_OMEGA_SHAPE(p):
    """|- !X. sk_step (App_t (App_t I_t X) (App_t I_t X))
              = App_t (App_t (App_t K_t X) (App_t K_t X)) (App_t I_t X).

    First step of the Omega-shape trajectory cycle.  Top of the input is
    App_t a b with a = b = App_t I_t X.  Refute the K- and S- top-disjuncts
    via I_T_DEF + APP_T_INJ + {K,S}_T_NEQ_APP_T (I_t doesn't structurally
    unify with K_t or App_t S_t _).  D3 fires; sk_step a = App_t (App_t
    K_t X) (App_t K_t X) by SK_STEP_I_APP, hence ``descend-L`` -- giving
    the claimed value.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2, TRANS
    from tactics import AP_TERM, AP_THM
    p.goal(
        "!X. sk_step (App_t (App_t I_t X) (App_t I_t X)) "
        "    = App_t (App_t (App_t K_t X) (App_t K_t X)) (App_t I_t X)"
    )
    p.fix("X")
    t = "App_t (App_t I_t X) (App_t I_t X)"
    sk_t = f"sk_step ({t})"
    val = "App_t (App_t (App_t K_t X) (App_t K_t X)) (App_t I_t X)"

    # ---- sub-lemma: sk_step (App_t I_t X) = (K X)(K X) ---------------
    p.have(
        "sk_IX: sk_step (App_t I_t X) = App_t (App_t K_t X) (App_t K_t X)"
    ).by(SK_STEP_I_APP, "X")

    # ---- not_kred:  ~(?a b. t = App_t (App_t K_t a) b) ---------------
    with p.have(
        f"not_kred: ~(?a b. {t} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex_kred: ?a b. {t} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex_kred")
            p.choose("b", from_="a_eq")
            # b_eq : t = App_t (App_t K_t a) b
            p.have(
                "h_o: App_t I_t X = App_t K_t a /\\ App_t I_t X = b"
            ).by(
                APP_T_INJ, "App_t I_t X", "App_t I_t X",
                "App_t K_t a", "b", "b_eq",
            )
            p.have("h_IX: App_t I_t X = App_t K_t a").by_thm(_C1(p.fact("h_o")))
            p.have("h_IK: I_t = K_t /\\ X = a").by(
                APP_T_INJ, "I_t", "X", "K_t", "a", "h_IX"
            )
            p.have("h_eq_IK: I_t = K_t").by_thm(_C1(p.fact("h_IK")))
            # I_T_DEF: I_t = App_t (App_t S_t K_t) K_t.
            p.have(
                "h_AK: App_t (App_t S_t K_t) K_t = K_t"
            ).by_thm(TRANS(SYM(I_T_DEF), p.fact("h_eq_IK")))
            p.have(
                "h_neq: ~(K_t = App_t (App_t S_t K_t) K_t)"
            ).by(K_T_NEQ_APP_T, "App_t S_t K_t", "K_t")
            p.have(
                "h_sym: K_t = App_t (App_t S_t K_t) K_t"
            ).by_thm(SYM(p.fact("h_AK")))
            p.absurd().by_conj("h_neq", "h_sym")

    # ---- not_sred:  ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) ----
    with p.have(
        f"not_sred: ~(?a b c. {t} = App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            f"ex_sred: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex_sred")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            # c_eq : t = App_t (App_t (App_t S_t a) b) c
            p.have(
                "h_o: App_t I_t X = App_t (App_t S_t a) b "
                "     /\\ App_t I_t X = c"
            ).by(
                APP_T_INJ, "App_t I_t X", "App_t I_t X",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_IX: App_t I_t X = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                "h_IS: I_t = App_t S_t a /\\ X = b"
            ).by(APP_T_INJ, "I_t", "X", "App_t S_t a", "b", "h_IX")
            p.have("h_eq_IS: I_t = App_t S_t a").by_thm(_C1(p.fact("h_IS")))
            p.have(
                "h_ASKK: App_t (App_t S_t K_t) K_t = App_t S_t a"
            ).by_thm(TRANS(SYM(I_T_DEF), p.fact("h_eq_IS")))
            p.have(
                "h_inj: App_t S_t K_t = S_t /\\ K_t = a"
            ).by(APP_T_INJ, "App_t S_t K_t", "K_t", "S_t", "a", "h_ASKK")
            p.have("h_ASK: App_t S_t K_t = S_t").by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_neq: ~(S_t = App_t S_t K_t)"
            ).by(S_T_NEQ_APP_T, "S_t", "K_t")
            p.have(
                "h_sym: S_t = App_t S_t K_t"
            ).by_thm(SYM(p.fact("h_ASK")))
            p.absurd().by_conj("h_neq", "h_sym")

    # ---- not_fixed_IX:  ~(sk_step (App_t I_t X) = App_t I_t X) -------
    # Used to (a) prove descend-L (the firing inner sub-branch), and
    # (b) refute descend-R and both-fixed sub-branches in the D3 case.
    with p.have(
        "not_fixed_IX: ~(sk_step (App_t I_t X) = App_t I_t X)"
    ).proof():
        with p.suppose("hf: sk_step (App_t I_t X) = App_t I_t X"):
            # sk_IX : sk_step (App_t I_t X) = (K X)(K X)
            # hf    : sk_step (App_t I_t X) = App_t I_t X
            # combine: (K X)(K X) = App_t I_t X.
            p.have(
                "h: App_t (App_t K_t X) (App_t K_t X) = App_t I_t X"
            ).by_thm(TRANS(SYM(p.fact("sk_IX")), p.fact("hf")))
            # APP_T_INJ -> App_t K_t X = I_t.
            p.have(
                "h_o: App_t K_t X = I_t /\\ App_t K_t X = X"
            ).by(
                APP_T_INJ, "App_t K_t X", "App_t K_t X", "I_t", "X", "h"
            )
            p.have("h_KX_I: App_t K_t X = I_t").by_thm(_C1(p.fact("h_o")))
            # I_T_DEF -> App_t K_t X = App_t (App_t S_t K_t) K_t.
            p.have(
                "h_KX_ASKK: App_t K_t X = App_t (App_t S_t K_t) K_t"
            ).by_thm(TRANS(p.fact("h_KX_I"), I_T_DEF))
            # APP_T_INJ -> K_t = App_t S_t K_t, refuted by K_T_NEQ_APP_T.
            p.have(
                "h_inj: K_t = App_t S_t K_t /\\ X = K_t"
            ).by(APP_T_INJ, "K_t", "X", "App_t S_t K_t", "K_t", "h_KX_ASKK")
            p.have("h_K_ASK: K_t = App_t S_t K_t").by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_neq: ~(K_t = App_t S_t K_t)"
            ).by(K_T_NEQ_APP_T, "S_t", "K_t")
            p.absurd().by_conj("h_neq", "h_K_ASK")

    # ---- Build the D3 disjunct (firing) at r := val ------------------
    # D3 inner sub-disjunct (descend-L):
    #   ~(sk_step a = a) /\ val = App_t (sk_step a) b
    # at a = b = App_t I_t X.
    #
    # The second conjunct ``val = App_t (sk_step (App_t I_t X)) (App_t I_t X)``
    # follows from ``sk_IX`` by AP_THM(AP_TERM(App_t, sk_IX), App_t I_t X)
    # then SYM.
    val_eq = AP_THM(
        AP_TERM(p._parse("App_t"), SYM(p.fact("sk_IX"))),
        p._parse("App_t I_t X"),
    )
    p.have(
        f"val_eq: ({val}) = App_t (sk_step (App_t I_t X)) (App_t I_t X)"
    ).by_thm(val_eq)

    p.have(
        f"descL: ~(sk_step (App_t I_t X) = App_t I_t X) /\\ "
        f"({val}) = App_t (sk_step (App_t I_t X)) (App_t I_t X)"
    ).by_thm(_CONJ(p.fact("not_fixed_IX"), p.fact("val_eq")))

    # DISJ1 descL into the 3-disjunct inner-disjunction (after fixing a, b
    # to App_t I_t X via the existential witness below).
    p.have(
        f"inner_disj_at_IX: "
        f"(~(sk_step (App_t I_t X) = App_t I_t X) /\\ "
        f" ({val}) = App_t (sk_step (App_t I_t X)) (App_t I_t X)) \\/ "
        f"(sk_step (App_t I_t X) = App_t I_t X /\\ "
        f" ~(sk_step (App_t I_t X) = App_t I_t X) /\\ "
        f" ({val}) = App_t (App_t I_t X) (sk_step (App_t I_t X))) \\/ "
        f"(sk_step (App_t I_t X) = App_t I_t X /\\ "
        f" sk_step (App_t I_t X) = App_t I_t X /\\ "
        f" ({val}) = ({t}))"
    ).by_disj("descL")

    # Build the existential: ?a b. t = App_t a b /\ inner_disjunction[a,b].
    p.have(
        f"ex_a_b: ?a b. ({t}) = App_t a b /\\ "
        f"        ((~(sk_step a = a) /\\ ({val}) = App_t (sk_step a) b) \\/ "
        f"         (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"          ({val}) = App_t a (sk_step b)) \\/ "
        f"         (sk_step a = a /\\ sk_step b = b /\\ ({val}) = ({t})))"
    ).by_exists(
        ["App_t I_t X", "App_t I_t X"],
        REFL(p._parse(t)),
        "inner_disj_at_IX",
    )

    # Full D3 disjunct: ~K /\ ~S /\ ex_a_b.
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    p.have(
        f"inner_D3: ~({K_shape}) /\\ ~({S_shape}) /\\ "
        f"(?a b. ({t}) = App_t a b /\\ "
        f"       ((~(sk_step a = a) /\\ ({val}) = App_t (sk_step a) b) \\/ "
        f"        (sk_step a = a /\\ ~(sk_step b = b) /\\ "
        f"         ({val}) = App_t a (sk_step b)) \\/ "
        f"        (sk_step a = a /\\ sk_step b = b /\\ ({val}) = ({t}))))"
    ).by_thm(
        _CONJ(p.fact("not_kred"), _CONJ(p.fact("not_sred"), p.fact("ex_a_b")))
    )

    # ---- Feed to _sk_step_select_at and case-analyze body ------------
    body_th = _sk_step_select_at(p, t, val, "inner_D3")
    p.have(f"body: {_sk_step_body(t, sk_t)}").by_thm(body_th)

    # is_app: App-shape of t (refutes D4).
    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["App_t I_t X", "App_t I_t X"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_step_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # Refute via not_kred.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            # Refute via not_sred.
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                f"h_sred_ex: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], p.fact("h_app"))
            p.absurd().by_conj("not_sred", "h_sred_ex")
        with p.case(f"h3: {D3}"):
            # Firing case.  Inner case-split on the 3-sub-disjunction.
            p.split("h3", "(_, _, h3_inner)")
            # h3_inner : ?a b. t = App_t a b /\ (descL \/ descR \/ fixed)
            p.choose("a", from_="h3_inner")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_inner)")
            # APP_T_INJ on h_app : App_t I_t X = a /\ App_t I_t X = b.
            p.have(
                "h_inj: App_t I_t X = a /\\ App_t I_t X = b"
            ).by(
                APP_T_INJ, "App_t I_t X", "App_t I_t X", "a", "b", "h_app"
            )
            p.have("h_a_eq: App_t I_t X = a").by_thm(_C1(p.fact("h_inj")))
            p.have("h_b_eq: App_t I_t X = b").by_thm(_C2(p.fact("h_inj")))
            # sk_step a = sk_step (App_t I_t X) = (K X)(K X).
            h_sk_a_th = TRANS(
                SYM(AP_TERM(p._parse("sk_step"), p.fact("h_a_eq"))),
                p.fact("sk_IX"),
            )
            p.have(
                "h_sk_a: sk_step a = App_t (App_t K_t X) (App_t K_t X)"
            ).by_thm(h_sk_a_th)

            # Helper: if sk_step a = a, derive sk_step (App_t I_t X)
            # = App_t I_t X, contradicting not_fixed_IX.
            def _refute_fixed_a(fixed_a_lbl):
                # sk_step (App_t I_t X) = sk_step a [AP_TERM at h_a_eq] = a [fixed_a] = App_t I_t X [SYM h_a_eq].
                th = TRANS(
                    TRANS(
                        AP_TERM(p._parse("sk_step"), p.fact("h_a_eq")),
                        p.fact(fixed_a_lbl),
                    ),
                    SYM(p.fact("h_a_eq")),
                )
                p.have(
                    "h_fixed_IX: sk_step (App_t I_t X) = App_t I_t X"
                ).by_thm(th)
                p.absurd().by_conj("not_fixed_IX", "h_fixed_IX")

            with p.cases_on("h_inner"):
                with p.case(
                    f"hcL: ~(sk_step a = a) /\\ ({sk_t}) = App_t (sk_step a) b"
                ):
                    p.split("hcL", "(_, h_sk_eq)")
                    # h_sk_eq : sk_t = App_t (sk_step a) b.
                    # Want: sk_t = val.
                    # Compute: App_t (sk_step a) b
                    #        = App_t ((K X)(K X)) b               [h_sk_a]
                    #        = App_t ((K X)(K X)) (App_t I_t X)   [SYM h_b_eq]
                    #        = val.
                    rhs_eq = TRANS(
                        AP_THM(
                            AP_TERM(p._parse("App_t"), p.fact("h_sk_a")),
                            p._parse("b"),
                        ),
                        AP_TERM(
                            p._parse(f"App_t (App_t (App_t K_t X) (App_t K_t X))"),
                            SYM(p.fact("h_b_eq")),
                        ),
                    )
                    p.have(
                        f"h_rhs: App_t (sk_step a) b = ({val})"
                    ).by_thm(rhs_eq)
                    p.thus(f"{sk_t} = {val}").by_thm(
                        TRANS(p.fact("h_sk_eq"), p.fact("h_rhs"))
                    )
                with p.case(
                    f"hcR: sk_step a = a /\\ ~(sk_step b = b) /\\ "
                    f"({sk_t}) = App_t a (sk_step b)"
                ):
                    p.split("hcR", "(h_fixed_a, _, _)")
                    _refute_fixed_a("h_fixed_a")
                with p.case(
                    f"hcF: sk_step a = a /\\ sk_step b = b /\\ ({sk_t}) = ({t})"
                ):
                    p.split("hcF", "(h_fixed_a, _, _)")
                    _refute_fixed_a("h_fixed_a")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


@proof
def OMEGA_SHAPE_NOT_NORMAL(p):
    """|- !X. ~ is_normal (App_t (App_t I_t X) (App_t I_t X)).

    Generalises OMEGA_T_NOT_NORMAL.  By TRAJ_STEP_OMEGA_SHAPE,
    sk_step on Omega-shape produces ((K X)(K X))(I X) which differs
    structurally: equality would force App_t K_t X = I_t, contradicted
    by I_T_DEF + APP_T_INJ + K_T_NEQ_APP_T.
    """
    from tactics import CONJUNCT1 as _C1, TRANS
    p.goal("!X. ~ is_normal (App_t (App_t I_t X) (App_t I_t X))")
    p.fix("X")
    with p.suppose(
        "h_norm: is_normal (App_t (App_t I_t X) (App_t I_t X))"
    ):
        p.have(
            "h_eq: sk_step (App_t (App_t I_t X) (App_t I_t X)) "
            "      = App_t (App_t I_t X) (App_t I_t X)"
        ).by(
            IS_NORMAL_IMP_FIXED,
            "App_t (App_t I_t X) (App_t I_t X)",
            "h_norm",
        )
        p.have(
            "h_traj: sk_step (App_t (App_t I_t X) (App_t I_t X)) "
            "        = App_t (App_t (App_t K_t X) (App_t K_t X)) (App_t I_t X)"
        ).by(TRAJ_STEP_OMEGA_SHAPE, "X")
        # (K X)(K X)(I X) = (I X)(I X).
        p.have(
            "h1: App_t (App_t (App_t K_t X) (App_t K_t X)) (App_t I_t X) "
            "    = App_t (App_t I_t X) (App_t I_t X)"
        ).by_thm(TRANS(SYM(p.fact("h_traj")), p.fact("h_eq")))
        # APP_T_INJ on outer: (K X)(K X) = I X (and I X = I X).
        p.have(
            "h_o: App_t (App_t K_t X) (App_t K_t X) = App_t I_t X "
            "     /\\ App_t I_t X = App_t I_t X"
        ).by(
            APP_T_INJ,
            "App_t (App_t K_t X) (App_t K_t X)", "App_t I_t X",
            "App_t I_t X", "App_t I_t X",
            "h1",
        )
        p.have(
            "h_K: App_t (App_t K_t X) (App_t K_t X) = App_t I_t X"
        ).by_thm(_C1(p.fact("h_o")))
        # APP_T_INJ: App_t K_t X = I_t.
        p.have(
            "h_inj: App_t K_t X = I_t /\\ App_t K_t X = X"
        ).by(APP_T_INJ, "App_t K_t X", "App_t K_t X", "I_t", "X", "h_K")
        p.have("h_KX_I: App_t K_t X = I_t").by_thm(_C1(p.fact("h_inj")))
        # I_T_DEF: I_t = App_t (App_t S_t K_t) K_t.
        p.have(
            "h_unf: App_t K_t X = App_t (App_t S_t K_t) K_t"
        ).by_thm(TRANS(p.fact("h_KX_I"), I_T_DEF))
        # APP_T_INJ: K_t = App_t S_t K_t.
        p.have(
            "h_inj2: K_t = App_t S_t K_t /\\ X = K_t"
        ).by(APP_T_INJ, "K_t", "X", "App_t S_t K_t", "K_t", "h_unf")
        p.have("h_K_ASK: K_t = App_t S_t K_t").by_thm(_C1(p.fact("h_inj2")))
        p.have(
            "h_neq: ~(K_t = App_t S_t K_t)"
        ).by(K_T_NEQ_APP_T, "S_t", "K_t")
        p.absurd().by_conj("h_neq", "h_K_ASK")


@proof
def OMEGA_T_NOT_NORMAL(p):
    """|- ~ is_normal Omega_t.

    Base case for OMEGA_NON_HALTING: rule out ``halts`` at iteration
    n = 0.  Proof:
      is_normal Omega_t  =>  sk_step Omega_t = Omega_t            [IS_NORMAL_IMP_FIXED]
      OMEGA_T_STEP1:     sk_step Omega_t = App_t (App_t I_t SII) (App_t I_t SII)
      Combine:           App_t (App_t I_t SII) (App_t I_t SII) = Omega_t
      OMEGA_T_DEF:       Omega_t = App_t SII SII
      Combine:           App_t (App_t I_t SII) (App_t I_t SII) = App_t SII SII
      APP_T_INJ x3:      App_t I_t SII = SII => I_t = App_t S_t I_t
                                              => App_t S_t K_t = S_t   [via I_T_DEF]
      S_T_NEQ_APP_T:     ~(S_t = App_t S_t K_t)                    -- contradiction.
    """
    from tactics import CONJUNCT1 as _C1, TRANS
    p.goal("~ is_normal Omega_t")
    SII = "App_t (App_t S_t I_t) I_t"
    with p.suppose("h_norm: is_normal Omega_t"):
        p.have("h_eq: sk_step Omega_t = Omega_t").by(
            IS_NORMAL_IMP_FIXED, "Omega_t", "h_norm"
        )
        # SYM(OMEGA_T_STEP1) gives RHS = sk_step Omega_t; TRANS with h_eq.
        p.have(
            f"h1: App_t (App_t I_t ({SII})) (App_t I_t ({SII})) = Omega_t"
        ).by_thm(TRANS(SYM(OMEGA_T_STEP1), p.fact("h_eq")))
        # Unfold Omega_t on the RHS via OMEGA_T_DEF.
        p.have(
            f"h2: App_t (App_t I_t ({SII})) (App_t I_t ({SII})) "
            f"     = App_t ({SII}) ({SII})"
        ).by_rewrite_of("h1", [OMEGA_T_DEF])
        # Outer APP_T_INJ: App_t I_t SII = SII (LHS) and same (RHS, unused).
        p.have(
            f"h3: App_t I_t ({SII}) = ({SII}) /\\ App_t I_t ({SII}) = ({SII})"
        ).by(
            APP_T_INJ,
            f"App_t I_t ({SII})",
            f"App_t I_t ({SII})",
            SII,
            SII,
            "h2",
        )
        p.have(f"h4: App_t I_t ({SII}) = ({SII})").by_thm(_C1(p.fact("h3")))
        # SII = App_t (App_t S_t I_t) I_t literally, so h4 reads:
        #   App_t I_t (App_t (App_t S_t I_t) I_t) = App_t (App_t S_t I_t) I_t.
        # APP_T_INJ at the outer App_t on both sides:
        #   I_t = App_t S_t I_t  /\  SII = I_t.
        p.have(
            f"h5: I_t = App_t S_t I_t /\\ ({SII}) = I_t"
        ).by(APP_T_INJ, "I_t", SII, "App_t S_t I_t", "I_t", "h4")
        p.have("h_It_eq: I_t = App_t S_t I_t").by_thm(_C1(p.fact("h5")))
        # I_T_DEF: I_t = App_t (App_t S_t K_t) K_t.  Compose:
        #   App_t (App_t S_t K_t) K_t = App_t S_t I_t   [TRANS(SYM(I_T_DEF), h_It_eq)].
        p.have(
            "h_unfolded: App_t (App_t S_t K_t) K_t = App_t S_t I_t"
        ).by_thm(TRANS(SYM(I_T_DEF), p.fact("h_It_eq")))
        # APP_T_INJ: App_t S_t K_t = S_t /\ K_t = I_t.
        p.have(
            "h_inj: App_t S_t K_t = S_t /\\ K_t = I_t"
        ).by(APP_T_INJ, "App_t S_t K_t", "K_t", "S_t", "I_t", "h_unfolded")
        p.have("h_ASK_eq_S: App_t S_t K_t = S_t").by_thm(_C1(p.fact("h_inj")))
        # Contradict via S_T_NEQ_APP_T at (S_t, K_t).
        p.have("h_neq: ~(S_t = App_t S_t K_t)").by(S_T_NEQ_APP_T, "S_t", "K_t")
        p.have("h_eq_sym: S_t = App_t S_t K_t").by_thm(SYM(p.fact("h_ASK_eq_S")))
        p.absurd().by_conj("h_neq", "h_eq_sym")


# ---------------------------------------------------------------------------
# Size-induction route to OMEGA_NON_HALTING.
#
# Three feeder lemmas (each stubbed below with a docstring sketch of its
# own proof); OMEGA_NON_HALTING composes them.
#
#   SK_ITER_ADD                  : iterate-of-iterate decomposition along
#                                  n0plus.  Pure induction on the outer
#                                  count.
#   SK_ITER_PAST_NORMAL          : once normal, stays normal under any
#                                  additional iter prefix.  Built from
#                                  SK_ITER_ADD + IS_NORMAL_SK_ITER_FIXED.
#   OMEGA_SHAPE_TRAJ_RETURNS     : from any Omega-shape, some k>0 sk_steps
#                                  later we land back at Omega-shape with
#                                  strictly larger sk_size.  Inducts on
#                                  the App_t I_t-nesting depth of X.
#   OMEGA_T_REACHES_LARGE_SIZE   : !N L. arbitrarily large Omega-shape
#                                  iterate at index n0plus k L (so >= L).
#                                  Induction on N using OMEGA_T_STEP1 as
#                                  base and OMEGA_SHAPE_TRAJ_RETURNS as
#                                  step.
# ---------------------------------------------------------------------------


@proof
def SK_ITER_ADD(p):
    """|- !n m t. sk_iter (n0plus n m) t = sk_iter n (sk_iter m t).

    Induction on ``n``:
      base:  sk_iter (n0plus 0 m) t = sk_iter m t = sk_iter 0 (sk_iter m t)
             [N0PLUS_BASE_L (or commutativity to N0PLUS_BASE), SK_ITER_ZERO].
             N0PLUS_BASE in this module is ``n0plus x 0 = x``; we need
             ``n0plus 0 m = m`` -- prove via small induction on m or
             via an N0PLUS_COMM helper.
      step:  sk_iter (n0plus (SUC0 n) m) t
              = sk_iter (SUC0 (n0plus n m)) t          [N0PLUS_SUC_L]
              = sk_step (sk_iter (n0plus n m) t)        [SK_ITER_SUC]
              = sk_step (sk_iter n (sk_iter m t))       [IH]
              = sk_iter (SUC0 n) (sk_iter m t)          [SK_ITER_SUC].

    Minor DSL friction: this module uses N0PLUS_BASE / N0PLUS_STEP at the
    right argument; the proof above needs versions at the LEFT argument.
    Either re-derive N0PLUS_BASE_L / N0PLUS_SUC_L inline or commute via
    N0PLUS_COMM (already in hf_sets? check before importing).
    """
    from tactics import TRANS as _TRANS, SYM as _SYM

    p.goal("!n m t. sk_iter (n0plus n m) t = sk_iter n (sk_iter m t)")
    p.fix("n")
    # DSL friction: we want induction on the SECOND quantifier (m); leave
    # m unfixed so ``with p.induction("m"):`` auto-peels ``!m t. body``.
    with p.induction("m"):
        with p.base():
            p.fix("t")
            # Goal: sk_iter (n0plus n 0) t = sk_iter n (sk_iter 0 t).
            # Both sides reduce to ``sk_iter n t`` under N0PLUS_BASE
            # (n0plus n 0 -> n) and SK_ITER_ZERO (sk_iter 0 t -> t).
            p.thus(
                "sk_iter (n0plus n 0) t = sk_iter n (sk_iter 0 t)"
            ).by_rewrite([N0PLUS_BASE, SK_ITER_ZERO])

        with p.step("IH"):
            p.fix("t")
            # IH (universally bound in t): specialise at this frame's t.
            p.have(
                "h_ih: sk_iter (n0plus n m) t = sk_iter n (sk_iter m t)"
            ).by("IH", "t")

            # ---- Commutation lemma at X := sk_iter m t. ------------------
            # ``sk_step (sk_iter n X) = sk_iter n (sk_step X)`` -- both
            # sides equal sk_iter (SUC0 n) X via SK_ITER_SUC and
            # SK_ITER_PUSH respectively.  Chain SYM + TRANS.
            p.have(
                "h_push: sk_iter (SUC0 n) (sk_iter m t) "
                "       = sk_iter n (sk_step (sk_iter m t))"
            ).by(SK_ITER_PUSH, "n", "sk_iter m t")
            p.have(
                "h_suc: sk_iter (SUC0 n) (sk_iter m t) "
                "      = sk_step (sk_iter n (sk_iter m t))"
            ).by(SK_ITER_SUC, "n", "sk_iter m t")
            # DSL friction: no "by_trans against a shared LHS" tactic
            # (by_trans composes a=b, b=c into a=c; here both facts have
            # the same LHS so we need SYM on one side first).  Drop to
            # kernel TRANS + SYM through ``by_thm``.
            p.have(
                "h_comm: sk_step (sk_iter n (sk_iter m t)) "
                "       = sk_iter n (sk_step (sk_iter m t))"
            ).by_thm(_TRANS(_SYM(p.fact("h_suc")), p.fact("h_push")))

            # ---- Compose LHS -> RHS via by_rewrite ----------------------
            # Goal: sk_iter (n0plus n (SUC0 m)) t
            #       = sk_iter n (sk_iter (SUC0 m) t).
            # Rewrites (all left-to-right):
            #   N0PLUS_STEP : n0plus _ (SUC0 _) -> SUC0 (n0plus _ _)
            #   SK_ITER_SUC : sk_iter (SUC0 _) _ -> sk_step (sk_iter _ _)
            #   h_ih        : sk_iter (n0plus n m) t -> sk_iter n (sk_iter m t)
            #   h_comm      : sk_step (sk_iter n (sk_iter m t))
            #                   -> sk_iter n (sk_step (sk_iter m t))
            # Both sides normalise to sk_iter n (sk_step (sk_iter m t)).
            #
            # DSL friction: h_ih and h_comm are FREE in t (not re-
            # universalised at frame entry); by_rewrite relies on
            # exact-shape occurrences, which the cascade above produces.
            p.thus(
                "sk_iter (n0plus n (SUC0 m)) t "
                "= sk_iter n (sk_iter (SUC0 m) t)"
            ).by_rewrite([
                N0PLUS_STEP,
                SK_ITER_SUC,
                "h_ih",
                "h_comm",
            ])


@proof
def SK_ITER_PAST_NORMAL(p):
    """|- !t n k. is_normal (sk_iter n t)
                  ==> sk_iter (n0plus k n) t = sk_iter n t.

    Once we land in normal form at step n, the trajectory stays put.

    Proof: SK_ITER_ADD at (k, n, t) gives
      sk_iter (n0plus k n) t = sk_iter k (sk_iter n t).
    IS_NORMAL_SK_ITER_FIXED at (k, sk_iter n t) gives
      sk_iter k (sk_iter n t) = sk_iter n t (under is_normal).
    Chain via TRANS.
    """
    from tactics import TRANS as _TRANS
    p.goal(
        "!t n k. is_normal (sk_iter n t) "
        "        ==> sk_iter (n0plus k n) t = sk_iter n t"
    )
    p.fix("t n k")
    p.assume("h_norm: is_normal (sk_iter n t)")
    # SK_ITER_ADD at (k, n, t): sk_iter (n0plus k n) t = sk_iter k (sk_iter n t).
    p.have(
        "h_add: sk_iter (n0plus k n) t = sk_iter k (sk_iter n t)"
    ).by(SK_ITER_ADD, "k", "n", "t")
    # IS_NORMAL_SK_ITER_FIXED at (k, sk_iter n t):
    #   is_normal (sk_iter n t) ==> sk_iter k (sk_iter n t) = sk_iter n t.
    p.have(
        "h_fix: sk_iter k (sk_iter n t) = sk_iter n t"
    ).by(IS_NORMAL_SK_ITER_FIXED, "k", "sk_iter n t", "h_norm")
    # Chain.
    p.thus(
        "sk_iter (n0plus k n) t = sk_iter n t"
    ).by_thm(_TRANS(p.fact("h_add"), p.fact("h_fix")))


# ---------------------------------------------------------------------------
# I-depth recursive constructor and the peel induction.
#
# The Omega trajectory has Omega-shape returns at iters 1, 4, 9, ... where
# the kth return is at Omega-shape (I^k SII).  To prove "returns to some
# Omega-shape with strictly larger size" inductively, we need to talk
# about ``I^k SII`` as a function of k.  Define ``I_pow`` by primitive
# recursion on the depth:
#
#   I_pow 0       X = X
#   I_pow (SUC0 k) X = App_t I_t (I_pow k X)
#
# Then the peel induction lemma OMEGA_PEEL captures the variable-length
# trace from ``App_t (I_pow k SII) (App_t I_t W)`` to Omega-shape (I W),
# inducting on k.
# ---------------------------------------------------------------------------


_n0_X_var = Var("X", nat0_ty)
_n0_k_ip = Var("k", nat0_ty)
_n0_a_ip = Var("a", parse_type("nat0 -> nat0"))

# c : nat0 -> nat0 = \X. X
_c_I_pow = mk_abs(_n0_X_var, _n0_X_var)
# h : nat0 -> (nat0 -> nat0) -> (nat0 -> nat0)
#   = \k. \a. \X. App_t I_t (a X)
_h_I_pow = mk_abs(
    _n0_k_ip,
    mk_abs(
        _n0_a_ip,
        mk_abs(_n0_X_var, mk_app(App_t, I_t, mk_app(_n0_a_ip, _n0_X_var))),
    ),
)

I_POW_BASE, I_POW_STEP = define_unary_0(
    "I_pow",
    parse_type("nat0 -> nat0 -> nat0"),
    _c_I_pow,
    _h_I_pow,
    result_ty=parse_type("nat0 -> nat0"),
)
I_pow = mk_const("I_pow", [])
# I_POW_BASE : |- I_pow 0 = (\X. X)
# I_POW_STEP : |- !k. I_pow (SUC0 k) = (\X. App_t I_t (I_pow k X))


@proof
def I_POW_ZERO(p):
    """|- !X. I_pow 0 X = X.

    AP_THM I_POW_BASE at X, BETA the RHS.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GEN
    ap = AP_THM(I_POW_BASE, _n0_X_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!X. I_pow 0 X = X")
    p.thus("!X. I_pow 0 X = X").by_thm(GEN(_n0_X_var, spec_th))


@proof
def I_POW_SUC(p):
    """|- !k X. I_pow (SUC0 k) X = App_t I_t (I_pow k X).

    SPEC I_POW_STEP at k, AP_THM at X, BETA.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, SPEC, GENL

    k_var = Var("k", nat0_ty)
    step_at_k = SPEC(k_var, I_POW_STEP)
    ap = AP_THM(step_at_k, _n0_X_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!k X. I_pow (SUC0 k) X = App_t I_t (I_pow k X)")
    p.thus(
        "!k X. I_pow (SUC0 k) X = App_t I_t (I_pow k X)"
    ).by_thm(GENL([k_var, _n0_X_var], spec_th))


@proof
def OMEGA_PEEL_HEAD2(p):
    """|- !X Y. ?n. sk_iter n (App_t (App_t I_t X) Y) = App_t X Y.

    Two-step trace, independent of X and Y:
      step 1: descend-L SK_STEP_I_APP (lifted via SK_STEP_LEFT) reduces
              (App_t I_t X) Y -> ((K X)(K X)) Y.
      step 2: SK_STEP_K_UNDER_LEFT fires the K-redex on the LHS,
              ((K X)(K X)) Y -> X Y.

    The three SK_STEP_LEFT guards depend only on I_t's structural
    difference from K_t / App_t S_t _, dischargeable via APP_T_INJ +
    I_T_DEF + atom-tag inequalities.  The SK_STEP_K_UNDER_LEFT guard
    uses SK_NEQ_DEEP_LEFT_WRAP.

    This is the inductive-step lemma for OMEGA_PEEL: each I_t layer
    peeled from the head of ``App_t (I_pow k SII) (App_t I_t W)`` costs
    exactly 2 sk_steps and the K-redex restoration drops us into the
    structurally smaller ``App_t (I_pow (k-1) SII) (App_t I_t W)``.
    """
    from tactics import CONJUNCT1 as _C1, TRANS as _TRANS

    p.goal(
        "!X Y. ?n. sk_iter n (App_t (App_t I_t X) Y) = App_t X Y"
    )
    p.fix("X Y")

    outer = "App_t (App_t I_t X) Y"

    # ---- h1: ~K-shape at outer.
    # ``App_t I_t X = App_t K_t a`` peels to ``I_t = K_t``; via I_T_DEF
    # this gives ``App_t (App_t S_t K_t) K_t = K_t``, contradicting
    # K_T_NEQ_APP_T.
    with p.have(
        f"h1: ~(?a b. {outer} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex_k: ?a b. {outer} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex_k")
            p.choose("b", from_="a_eq")
            p.have(
                "e1: App_t I_t X = App_t K_t a /\\ Y = b"
            ).by(APP_T_INJ, "App_t I_t X", "Y", "App_t K_t a", "b", "b_eq")
            p.have("e1a: App_t I_t X = App_t K_t a").by_thm(_C1(p.fact("e1")))
            p.have("e2: I_t = K_t /\\ X = a").by(
                APP_T_INJ, "I_t", "X", "K_t", "a", "e1a"
            )
            p.have("e_IK: I_t = K_t").by_thm(_C1(p.fact("e2")))
            # Unfold I_t via I_T_DEF: App_t (App_t S_t K_t) K_t = K_t.
            p.have(
                "e_unf: App_t (App_t S_t K_t) K_t = K_t"
            ).by_thm(_TRANS(SYM(I_T_DEF), p.fact("e_IK")))
            p.have(
                "e_sym: K_t = App_t (App_t S_t K_t) K_t"
            ).by_thm(SYM(p.fact("e_unf")))
            p.have(
                "k_neq: ~(K_t = App_t (App_t S_t K_t) K_t)"
            ).by(K_T_NEQ_APP_T, "App_t S_t K_t", "K_t")
            p.absurd().by_conj("k_neq", "e_sym")

    # ---- h2: ~S-shape at outer.
    # Peels to ``I_t = App_t S_t a``; via I_T_DEF this gives
    # ``App_t (App_t S_t K_t) K_t = App_t S_t a``, peel ``App_t S_t K_t = S_t``,
    # contradicting S_T_NEQ_APP_T.
    with p.have(
        f"h2: ~(?a b c. {outer} = App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            f"ex_s: ?a b c. {outer} = App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex_s")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "e1: App_t I_t X = App_t (App_t S_t a) b /\\ Y = c"
            ).by(
                APP_T_INJ, "App_t I_t X", "Y",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "e1a: App_t I_t X = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("e1")))
            p.have(
                "e2: I_t = App_t S_t a /\\ X = b"
            ).by(APP_T_INJ, "I_t", "X", "App_t S_t a", "b", "e1a")
            p.have("e_IS: I_t = App_t S_t a").by_thm(_C1(p.fact("e2")))
            p.have(
                "e_unf: App_t (App_t S_t K_t) K_t = App_t S_t a"
            ).by_thm(_TRANS(SYM(I_T_DEF), p.fact("e_IS")))
            p.have(
                "e_inj: App_t S_t K_t = S_t /\\ K_t = a"
            ).by(APP_T_INJ, "App_t S_t K_t", "K_t", "S_t", "a", "e_unf")
            p.have(
                "e_ASK: App_t S_t K_t = S_t"
            ).by_thm(_C1(p.fact("e_inj")))
            p.have(
                "e_sym: S_t = App_t S_t K_t"
            ).by_thm(SYM(p.fact("e_ASK")))
            p.have(
                "s_neq: ~(S_t = App_t S_t K_t)"
            ).by(S_T_NEQ_APP_T, "S_t", "K_t")
            p.absurd().by_conj("s_neq", "e_sym")

    # ---- h3: ~self-step on (App_t I_t X).
    # SK_STEP_I_APP: sk_step (App_t I_t X) = (K X)(K X) != App_t I_t X
    # by APP_T_INJ + I_T_DEF + K_T_NEQ_APP_T.
    with p.have(
        f"h3: ~(sk_step (App_t I_t X) = App_t I_t X)"
    ).proof():
        with p.suppose(f"hf: sk_step (App_t I_t X) = App_t I_t X"):
            p.have(
                "sk_IX: sk_step (App_t I_t X) "
                "      = App_t (App_t K_t X) (App_t K_t X)"
            ).by(SK_STEP_I_APP, "X")
            p.have(
                "e: App_t (App_t K_t X) (App_t K_t X) = App_t I_t X"
            ).by_thm(_TRANS(SYM(p.fact("sk_IX")), p.fact("hf")))
            p.have(
                "e1: App_t K_t X = I_t /\\ App_t K_t X = X"
            ).by(
                APP_T_INJ, "App_t K_t X", "App_t K_t X",
                "I_t", "X", "e",
            )
            p.have("e1a: App_t K_t X = I_t").by_thm(_C1(p.fact("e1")))
            p.have(
                "e_unf: App_t K_t X = App_t (App_t S_t K_t) K_t"
            ).by_thm(_TRANS(p.fact("e1a"), I_T_DEF))
            p.have(
                "e_inj: K_t = App_t S_t K_t /\\ X = K_t"
            ).by(
                APP_T_INJ, "K_t", "X", "App_t S_t K_t", "K_t", "e_unf"
            )
            p.have("e_KS: K_t = App_t S_t K_t").by_thm(_C1(p.fact("e_inj")))
            p.have(
                "k_neq: ~(K_t = App_t S_t K_t)"
            ).by(K_T_NEQ_APP_T, "S_t", "K_t")
            p.absurd().by_conj("k_neq", "e_KS")

    # ---- ns_step2: SK_STEP_K_UNDER_LEFT's not_self for step 2.
    p.have(
        "ns_step2: ~(X = App_t (App_t K_t X) (App_t K_t X))"
    ).by(SK_NEQ_DEEP_LEFT_WRAP, "X", "K_t", "App_t K_t X")

    # ---- 2-step trace via sk_reduce ---------------------------------------
    with sk_reduce(p, outer, "App_t X Y") as r:
        # Step 1: SK_STEP_LEFT at (u=App_t I_t X, v=Y).
        # current = App_t (sk_step (App_t I_t X)) Y.
        r.step(SK_STEP_LEFT, "App_t I_t X", "Y", mp=["h1", "h2", "h3"])
        # Rewrite sk_step (App_t I_t X) to (K X)(K X) via SK_STEP_I_APP.
        # current = App_t (App_t (App_t K_t X) (App_t K_t X)) Y.
        r.rewrite(SK_STEP_I_APP)
        # Step 2: SK_STEP_K_UNDER_LEFT at (x=X, y=App_t K_t X, z=Y).
        # current = App_t X Y.
        r.step(
            SK_STEP_K_UNDER_LEFT,
            "X", "App_t K_t X", "Y",
            mp=["ns_step2"],
        )


@proof
def OMEGA_PEEL(p):
    """|- !k W. ?n. sk_iter n (App_t (I_pow k SII) (App_t I_t W))
                  = App_t (App_t I_t (App_t I_t W)) (App_t I_t (App_t I_t W)).

    SII = App_t (App_t S_t I_t) I_t.  The end is Omega-shape (I_t W),
    independent of k.

    Inductive trace lemma for Omega trajectory returns at I-depth k:
    from ``App_t (I^k SII) (I W)``, some 2k+1 sk_steps reach
    Omega-shape (I W).  Induction on k:

      Base k=0: I_pow 0 SII = SII.  Start = SII (I W) -- top S-redex
        with x=I_t, y=I_t, z=I W.  1 sk_step reaches (I (I W))(I (I W))
        = Omega-shape (I W).

      Step k -> k+1: I_pow (SUC0 k) SII = App_t I_t (I_pow k SII).
        Start_{k+1} = (App_t I_t (I_pow k SII)) (App_t I_t W).
        OMEGA_PEEL_HEAD2 at (X := I_pow k SII, Y := App_t I_t W) gives
        a 2-step trace to ``App_t (I_pow k SII) (App_t I_t W)`` = start_k.
        IH at W gives n_w sk_steps from start_k to end.  SK_ITER_ADD
        chains: ``n0plus n_w m`` sk_steps from start_{k+1} reach end.
    """
    from tactics import TRANS as _TRANS, AP_TERM as _APT, AP_THM
    SII = "App_t (App_t S_t I_t) I_t"
    end = "App_t (App_t I_t (App_t I_t W)) (App_t I_t (App_t I_t W))"

    p.goal(
        f"!k. !W. ?n. sk_iter n (App_t (I_pow k ({SII})) (App_t I_t W)) = {end}"
    )

    with p.induction("k"):
        with p.base():
            p.fix("W")
            start_0 = f"App_t (I_pow 0 ({SII})) (App_t I_t W)"
            with sk_reduce(p, start_0, end) as r:
                # I_POW_ZERO unfolds I_pow 0 SII -> SII in the running eq.
                r.rewrite(I_POW_ZERO)
                # current = App_t SII (App_t I_t W).  Top S-redex.
                r.step(SK_STEP_S, "I_t", "I_t", "App_t I_t W")
                # current = end.

        with p.step("IH"):
            # IH : !W. ?n. sk_iter n (App_t (I_pow k SII) (App_t I_t W)) = end.
            p.fix("W")

            head2_start = f"App_t (App_t I_t (I_pow k ({SII}))) (App_t I_t W)"
            start_k = f"App_t (I_pow k ({SII})) (App_t I_t W)"
            start_k1 = f"App_t (I_pow (SUC0 k) ({SII})) (App_t I_t W)"

            # Unfold the head's I_pow layer: I_pow (SUC0 k) SII
            # = App_t I_t (I_pow k SII).  Lift through App_t at (I W).
            p.have(
                f"pow_eq: I_pow (SUC0 k) ({SII}) "
                f"        = App_t I_t (I_pow k ({SII}))"
            ).by(I_POW_SUC, "k", SII)
            # AP_TERM(App_t, pow_eq) then AP_THM at (App_t I_t W).
            App_t_const = p._parse("App_t")
            pow_eq_apt = _APT(App_t_const, p.fact("pow_eq"))
            arg = p._parse("App_t I_t W")
            pow_eq_app_th = AP_THM(pow_eq_apt, arg)
            p.have(
                f"pow_eq_app: {start_k1} = {head2_start}"
            ).by_thm(pow_eq_app_th)

            # OMEGA_PEEL_HEAD2 at (X := I_pow k SII, Y := App_t I_t W):
            # 2-step trace head2_start -> start_k.
            p.have(
                f"h_head2: ?m. sk_iter m ({head2_start}) = {start_k}"
            ).by(
                OMEGA_PEEL_HEAD2, f"I_pow k ({SII})", "App_t I_t W"
            )
            p.choose("m", from_="h_head2")
            # m_eq : sk_iter m head2_start = start_k.

            # IH at W: n_w sk_steps from start_k to end.
            p.have(
                f"h_ih: ?n_w. sk_iter n_w ({start_k}) = {end}"
            ).by("IH", "W")
            p.choose("n_w", from_="h_ih")
            # n_w_eq : sk_iter n_w start_k = end.

            # SK_ITER_ADD: sk_iter (n0plus n_w m) head2_start
            #            = sk_iter n_w (sk_iter m head2_start).
            p.have(
                f"h_add: sk_iter (n0plus n_w m) ({head2_start}) "
                f"      = sk_iter n_w (sk_iter m ({head2_start}))"
            ).by(SK_ITER_ADD, "n_w", "m", head2_start)

            # AP_TERM(sk_iter n_w) on m_eq:
            # sk_iter n_w (sk_iter m head2_start) = sk_iter n_w start_k.
            sk_iter_nw = p._parse("sk_iter n_w")
            iter_eq_th = _APT(sk_iter_nw, p.fact("m_eq"))
            p.have(
                f"h_mid: sk_iter n_w (sk_iter m ({head2_start})) "
                f"      = sk_iter n_w ({start_k})"
            ).by_thm(iter_eq_th)

            # Chain: h_add . h_mid . n_w_eq.
            p.have(
                f"h_unf_eq: sk_iter (n0plus n_w m) ({head2_start}) = {end}"
            ).by_thm(_TRANS(
                p.fact("h_add"),
                _TRANS(p.fact("h_mid"), p.fact("n_w_eq")),
            ))

            # Convert head2_start to start_k1 via pow_eq_app:
            # sk_iter (n0plus n_w m) start_k1 = sk_iter (n0plus n_w m) head2_start.
            sk_iter_total = p._parse("sk_iter (n0plus n_w m)")
            folded_eq = _APT(sk_iter_total, p.fact("pow_eq_app"))
            p.have(
                f"h_fold: sk_iter (n0plus n_w m) ({start_k1}) "
                f"      = sk_iter (n0plus n_w m) ({head2_start})"
            ).by_thm(folded_eq)

            # Final chain.
            p.have(
                f"h_final: sk_iter (n0plus n_w m) ({start_k1}) = {end}"
            ).by_thm(_TRANS(p.fact("h_fold"), p.fact("h_unf_eq")))

            # EXISTS at n0plus n_w m.
            p.thus(
                f"?n. sk_iter n ({start_k1}) = {end}"
            ).by_witness("n0plus n_w m", "h_final")


@proof
def OMEGA_TO_X_IX(p):
    """|- !X. sk_iter (SUC0 (SUC0 0)) (App_t (App_t I_t X) (App_t I_t X))
              = App_t X (App_t I_t X).

    Universal 2-step prefix of the Omega-shape trajectory:
      T0 = Omega_shape X = (I X)(I X)
      T1 = ((K X)(K X))(I X)                    [TRAJ_STEP_OMEGA_SHAPE]
      T2 = X (I X)                              [SK_STEP_K_UNDER_LEFT at
                                                 (x=X, y=K X, z=I X);
                                                 not_self via
                                                 SK_NEQ_DEEP_LEFT_WRAP]

    Uniform in X -- independent of X's structure.  Combines with
    OMEGA_PEEL (at W := X) inside OMEGA_TRAJ_I_DEPTH_STEP to give the
    full Omega-shape (I^k SII) -> Omega-shape (I^(k+1) SII) trace.

    Currently sorried; proof is ~30 lines of sk_reduce + one
    SK_NEQ_DEEP_LEFT_WRAP discharge for the K-lift's not_self.
    """
    p.goal(
        "!X. sk_iter (SUC0 (SUC0 0)) "
        "     (App_t (App_t I_t X) (App_t I_t X)) "
        "    = App_t X (App_t I_t X)"
    )
    p.fix("X")
    # T1 = sk_step T0 = ((K X)(K X))(I X)        [TRAJ_STEP_OMEGA_SHAPE]
    # T2 = sk_step T1 = X (I X)                  [SK_STEP_K_UNDER_LEFT at
    #                                              (x=X, y=K X, z=I X)]
    # not_self for the K-lift: ~(X = App_t (App_t K_t X) (App_t K_t X)).
    # SK_NEQ_DEEP_LEFT_WRAP at (t, u, v) := (X, K_t, App_t K_t X).
    p.have(
        "not_self: ~(X = App_t (App_t K_t X) (App_t K_t X))"
    ).by(SK_NEQ_DEEP_LEFT_WRAP, "X", "K_t", "App_t K_t X")
    with sk_reduce(
        p,
        "App_t (App_t I_t X) (App_t I_t X)",
        "App_t X (App_t I_t X)",
    ) as r:
        r.step(TRAJ_STEP_OMEGA_SHAPE, "X")
        r.step(
            SK_STEP_K_UNDER_LEFT,
            "X", "App_t K_t X", "App_t I_t X",
            mp=["not_self"],
        )


@proof
def OMEGA_TRAJ_I_DEPTH_STEP(p):
    """|- !k. ?n. sk_iter n (App_t (App_t I_t (I_pow k SII))
                                    (App_t I_t (I_pow k SII)))
                = App_t (App_t I_t (I_pow (SUC0 k) SII))
                        (App_t I_t (I_pow (SUC0 k) SII))
              /\\ nat0_lt (sk_size (App_t (App_t I_t (I_pow k SII))
                                           (App_t I_t (I_pow k SII))))
                          (sk_size (App_t (App_t I_t (I_pow (SUC0 k) SII))
                                           (App_t I_t (I_pow (SUC0 k) SII)))).

    Replaces the (false) universal OMEGA_SHAPE_TRAJ_RETURNS.  Step
    lemma at I-depth k: from Omega-shape (I^k SII) some n sk_steps
    reach Omega-shape (I^(k+1) SII), with strict size growth.

    SII = App_t (App_t S_t I_t) I_t.  Note both Omega-shape RHSs are
    spelled out fully -- the LHS has ``I_pow k SII`` (not just X), the
    RHS has ``I_pow (SUC0 k) SII``.  This concrete form is what
    OMEGA_T_REACHES_LARGE_SIZE iterates.

    Proof composes OMEGA_TO_X_IX + OMEGA_PEEL:
      * OMEGA_TO_X_IX at X := I_pow k SII gives 2 sk_steps to
        ``(I_pow k SII) (App_t I_t (I_pow k SII))``.
      * OMEGA_PEEL at (k, W := I_pow k SII) gives further n' sk_steps
        to ``(I (I (I_pow k SII)))(I (I (I_pow k SII)))``.
        Rewrite ``App_t I_t (I_pow k SII)`` to ``I_pow (SUC0 k) SII``
        via SYM(I_POW_SUC); the end becomes Omega-shape (I_pow (SUC0 k) SII).
      * SK_ITER_ADD chains: n0plus n' 2 sk_steps total.

    Size_lt: builds from SK_SIZE_GROWTH_OMEGA_SHAPE at t := I_pow k SII
    and the strict layer growth ``sk_size (I_pow k SII)
    < sk_size (App_t I_t (I_pow k SII)) = sk_size (I_pow (SUC0 k) SII)``,
    lifted to Omega-shapes via NAT0_LT_N0PLUS_MONO_L /
    NAT0_LT_N0PLUS_MONO_R + NAT0_LT_SUC0_MONO + SK_SIZE_APP.

    Estimated: ~80 lines once OMEGA_TO_X_IX and the n0plus monos land.
    Note: this is NOT a single head-redex trace -- it composes two
    pre-proved traces (OMEGA_TO_X_IX + OMEGA_PEEL) via SK_ITER_ADD --
    so ``sk_reduce`` is not the right tool here.  Close directly with
    ``p.thus(...).by_witness("n0plus n' (SUC0 (SUC0 0))", h_conj)``
    where ``h_conj`` is the CONJ of the iter equation and size_lt
    built from kernel-level TRANS and the size lemmas.  Currently
    sorried.
    """
    from tactics import (
        TRANS as _TRANS,
        SYM as _SYM,
        AP_TERM as _APT,
        MK_COMB as _MK,
        CONJ as _CONJ,
    )
    from nat0_order import NAT0_LT_SUC0_MONO, NAT0_LT_TRANS

    SII = "App_t (App_t S_t I_t) I_t"
    X = f"I_pow k ({SII})"
    SX = f"I_pow (SUC0 k) ({SII})"
    IX = f"App_t I_t ({X})"
    IIX = f"App_t I_t ({IX})"
    T0 = f"App_t ({IX}) ({IX})"
    T_end_raw = f"App_t ({IIX}) ({IIX})"
    T_end_goal = f"App_t (App_t I_t ({SX})) (App_t I_t ({SX}))"
    # DSL friction: f-string composition with `n0plus X Y` requires each
    # arg to already be parenthesised, otherwise the parser left-associates
    # `n0plus sk_size ...` and the partial application breaks types.
    sz_Y = f"(sk_size ({IX}))"
    sz_IY = f"(sk_size ({IIX}))"

    p.goal(
        f"!k. ?n. sk_iter n ({T0}) = {T_end_goal} "
        f"      /\\ nat0_lt (sk_size ({T0})) (sk_size ({T_end_goal}))"
    )
    p.fix("k")

    # -- Trace: T0 -> T_end_raw via OMEGA_TO_X_IX (2 steps) + OMEGA_PEEL (n_p).
    p.have(
        f"step1: sk_iter (SUC0 (SUC0 0)) ({T0}) "
        f"       = App_t ({X}) ({IX})"
    ).by(OMEGA_TO_X_IX, X)

    p.have(
        f"h_peel: ?n_p. sk_iter n_p (App_t ({X}) ({IX})) = {T_end_raw}"
    ).by(OMEGA_PEEL, "k", X)
    p.choose("n_p", from_="h_peel")

    # Chain via SK_ITER_ADD at (n_p, 2, T0):
    #   sk_iter (n0plus n_p 2) T0 = sk_iter n_p (sk_iter 2 T0).
    p.have(
        f"h_add: sk_iter (n0plus n_p (SUC0 (SUC0 0))) ({T0}) "
        f"       = sk_iter n_p (sk_iter (SUC0 (SUC0 0)) ({T0}))"
    ).by(SK_ITER_ADD, "n_p", "SUC0 (SUC0 0)", T0)
    # AP_TERM(sk_iter n_p) lifts step1 inside the SK_ITER_ADD chain.
    h_inner_th = _APT(p._parse("sk_iter n_p"), p.fact("step1"))
    p.have(
        f"h_inner: sk_iter n_p (sk_iter (SUC0 (SUC0 0)) ({T0})) "
        f"        = sk_iter n_p (App_t ({X}) ({IX}))"
    ).by_thm(h_inner_th)
    p.have(
        f"h_raw: sk_iter (n0plus n_p (SUC0 (SUC0 0))) ({T0}) = {T_end_raw}"
    ).by_thm(_TRANS(
        p.fact("h_add"),
        _TRANS(p.fact("h_inner"), p.fact("n_p_eq")),
    ))

    # -- Fold T_end_raw -> T_end_goal via I_POW_SUC.
    # pow_eq: I_pow (SUC0 k) SII = App_t I_t (I_pow k SII), i.e. SX = IX.
    p.have(
        f"pow_eq: {SX} = {IX}"
    ).by(I_POW_SUC, "k", SII)
    # h_inner_eq: App_t I_t IX = App_t I_t SX, i.e. IIX = App_t I_t SX.
    h_inner_eq_th = _APT(p._parse("App_t I_t"), _SYM(p.fact("pow_eq")))
    p.have(
        f"h_inner_eq: {IIX} = App_t I_t ({SX})"
    ).by_thm(h_inner_eq_th)
    # h_end_eq: T_end_raw = T_end_goal via MK_COMB on the two IIX slots.
    h_end_eq_th = _MK(
        _APT(p._parse("App_t"), p.fact("h_inner_eq")),
        p.fact("h_inner_eq"),
    )
    p.have(f"h_end_eq: {T_end_raw} = {T_end_goal}").by_thm(h_end_eq_th)
    p.have(
        f"h_trace: sk_iter (n0plus n_p (SUC0 (SUC0 0))) ({T0}) = {T_end_goal}"
    ).by_thm(_TRANS(p.fact("h_raw"), p.fact("h_end_eq")))

    # -- Size growth: sk_size T0 < sk_size T_end_goal.
    # Let Y = IX.  T0 = App_t Y Y; T_end_raw = App_t (I Y) (I Y); both summands
    # of T_end_raw strictly exceed (sk_size Y) via NAT0_LT_SUC0_N0PLUS_R, lifted
    # to n0plus by MONO_L + MONO_R + TRANS, then SUC0_MONO.
    p.have(
        f"sz_T0: sk_size ({T0}) "
        f"       = SUC0 (n0plus {sz_Y} {sz_Y})"
    ).by(SK_SIZE_APP, IX, IX)
    p.have(
        f"sz_T_end_raw: sk_size ({T_end_raw}) "
        f"             = SUC0 (n0plus {sz_IY} {sz_IY})"
    ).by(SK_SIZE_APP, IIX, IIX)
    p.have(
        f"sz_IY_eq: {sz_IY} "
        f"          = SUC0 (n0plus (sk_size I_t) {sz_Y})"
    ).by(SK_SIZE_APP, "I_t", IX)
    # h_lt_Y_IY: sk_size Y < sk_size (I Y).
    p.have(
        f"h_lt_pre: nat0_lt {sz_Y} "
        f"          (SUC0 (n0plus (sk_size I_t) {sz_Y}))"
    ).by(NAT0_LT_SUC0_N0PLUS_R, "sk_size I_t", sz_Y)
    p.have(
        f"h_lt_Y_IY: nat0_lt {sz_Y} {sz_IY}"
    ).by_rewrite_of("h_lt_pre", [_SYM(p.fact("sz_IY_eq"))])

    # Lift Y < IY to the two-summand n0plus via MONO_L (left slot) then
    # MONO_R (right slot), chained by TRANS.
    p.have(
        f"h_lt_L: nat0_lt (n0plus {sz_Y} {sz_Y}) "
        f"                (n0plus {sz_IY} {sz_Y})"
    ).by(
        NAT0_LT_N0PLUS_MONO_L, sz_Y, sz_IY, sz_Y, "h_lt_Y_IY",
    )
    p.have(
        f"h_lt_R: nat0_lt (n0plus {sz_IY} {sz_Y}) "
        f"                (n0plus {sz_IY} {sz_IY})"
    ).by(
        NAT0_LT_N0PLUS_MONO_R, sz_IY, sz_Y, sz_IY, "h_lt_Y_IY",
    )
    p.have(
        f"h_lt_sum: nat0_lt (n0plus {sz_Y} {sz_Y}) "
        f"                  (n0plus {sz_IY} {sz_IY})"
    ).by(
        NAT0_LT_TRANS,
        f"n0plus {sz_Y} {sz_Y}",
        f"n0plus {sz_IY} {sz_Y}",
        f"n0plus {sz_IY} {sz_IY}",
        "h_lt_L", "h_lt_R",
    )
    p.have(
        f"h_lt_suc: nat0_lt (SUC0 (n0plus {sz_Y} {sz_Y})) "
        f"                  (SUC0 (n0plus {sz_IY} {sz_IY}))"
    ).by(
        NAT0_LT_SUC0_MONO,
        f"n0plus {sz_Y} {sz_Y}",
        f"n0plus {sz_IY} {sz_IY}",
        "h_lt_sum",
    )
    p.have(
        f"h_size_lt_raw: nat0_lt (sk_size ({T0})) (sk_size ({T_end_raw}))"
    ).by_rewrite_of(
        "h_lt_suc",
        [_SYM(p.fact("sz_T0")), _SYM(p.fact("sz_T_end_raw"))],
    )
    h_size_eq_th = _APT(p._parse("sk_size"), p.fact("h_end_eq"))
    p.have(
        f"h_size_eq: sk_size ({T_end_raw}) = sk_size ({T_end_goal})"
    ).by_thm(h_size_eq_th)
    p.have(
        f"h_size_lt: nat0_lt (sk_size ({T0})) (sk_size ({T_end_goal}))"
    ).by_rewrite_of("h_size_lt_raw", [p.fact("h_size_eq")])

    # Conjoin and EXISTS-introduce.
    p.have(
        f"h_conj: sk_iter (n0plus n_p (SUC0 (SUC0 0))) ({T0}) = {T_end_goal} "
        f"        /\\ nat0_lt (sk_size ({T0})) (sk_size ({T_end_goal}))"
    ).by_thm(_CONJ(p.fact("h_trace"), p.fact("h_size_lt")))
    p.thus(
        f"?n. sk_iter n ({T0}) = {T_end_goal} "
        f"    /\\ nat0_lt (sk_size ({T0})) (sk_size ({T_end_goal}))"
    ).by_witness("n0plus n_p (SUC0 (SUC0 0))", "h_conj")


@proof
def OMEGA_DEPTH_SEQ(p):
    """|- !d. ?n. (sk_iter n Omega_t
                    = App_t (App_t I_t (I_pow d (App_t (App_t S_t I_t) I_t)))
                            (App_t I_t (I_pow d (App_t (App_t S_t I_t) I_t))))
              /\\ nat0_lt d (sk_size (Omega-shape (I_pow d SII)))
              /\\ nat0_lt d (SUC0 n).

    Depth-indexed sequence lemma: at every I-depth d there is an Omega-
    trajectory iterate landing at Omega-shape (I_pow d SII), with
    ``sk_size`` strictly exceeding d and iter count at least d.

    Currently sorried; ~60 lines by induction on d:

      Base d=0: n := SUC0 0.  iter eq from OMEGA_T_STEP1 + I_POW_ZERO fold;
        size > 0 by NAT0_LT_0_SUC0 (after SK_SIZE_APP); 0 <= n via
        NAT0_LT_0_SUC0 at m := 0.
      Step d -> SUC0 d:
        * From IH: n_d, iter eq at depth d, size_d > d, n_d >= d.
        * OMEGA_TRAJ_I_DEPTH_STEP at d gives m, iter eq m steps from
          Omega-shape (I_pow d SII) to Omega-shape (I_pow (SUC0 d) SII),
          with size_d < size_{d+1}.
        * SK_ITER_ADD chains: n_{d+1} := n0plus m n_d satisfies the iter
          equation at depth (SUC0 d).
        * size > SUC0 d: NAT0_LT_SUC0_INSERT(d < size_d, size_d < size_{d+1}).
        * iter count >= SUC0 d: m != 0 (else sk_iter m fixes the term,
          contradicting strict size growth), so n0plus m n_d >= SUC0 n_d
          >= SUC0 d.  Derive via NAT0_NEQ_ZERO_PRED on m and NAT0_LT_SUC0_MONO
          on n_d >= d.
    """
    from tactics import (
        AP_TERM as _APT,
        AP_THM as _AP_THM,
        TRANS as _TRANS,
        SYM as _SYM,
        MK_COMB as _MK,
        CONJ as _CONJ,
    )
    from nat0_order import (
        NAT0_LT_0_SUC0,
        NAT0_LT_SUC0_INSERT,
        NAT0_LT_SUC0_MONO,
        NAT0_NEQ_ZERO_PRED,
        NAT0_LT_NOT_REFL,
    )

    SII = "App_t (App_t S_t I_t) I_t"

    def Td(ds):
        return (
            f"App_t (App_t I_t (I_pow ({ds}) ({SII}))) "
            f"(App_t I_t (I_pow ({ds}) ({SII})))"
        )

    Td_d = Td("d")
    Td_sd = Td("SUC0 d")
    Td_0 = Td("0")
    SUC0_C = p._parse("SUC0")
    App_t_C = p._parse("App_t")
    App_t_I_t = p._parse("App_t I_t")

    # DSL friction: ``=`` is lower precedence than ``/\\``, so
    # ``A = B /\\ C`` parses as ``A = (B /\\ C)`` -- wrap the equation in
    # parens to keep it as a single conjunct.
    p.goal(
        f"!d. ?n. (sk_iter n Omega_t = {Td_d}) "
        f"     /\\ nat0_lt d (sk_size ({Td_d})) "
        f"     /\\ nat0_lt d (SUC0 n)"
    )
    with p.induction("d"):
        with p.base():
            # n := SUC0 0.  Trace: sk_iter (SUC0 0) Omega_t
            # = sk_step (sk_iter 0 Omega_t) = sk_step Omega_t
            # = App_t (App_t I_t SII) (App_t I_t SII)         [OMEGA_T_STEP1]
            # = App_t (App_t I_t (I_pow 0 SII)) (..)          [SYM I_POW_ZERO]
            p.have(
                "b_iter1: sk_iter (SUC0 0) Omega_t "
                "         = sk_step (sk_iter 0 Omega_t)"
            ).by(SK_ITER_SUC, "0", "Omega_t")
            p.have("b_iter0: sk_iter 0 Omega_t = Omega_t").by(
                SK_ITER_ZERO, "Omega_t"
            )
            # AP_TERM sk_step on b_iter0 to align inside b_iter1.
            b_inner = _APT(p._parse("sk_step"), p.fact("b_iter0"))
            p.have(
                f"b_iter1_step: sk_iter (SUC0 0) Omega_t = sk_step Omega_t"
            ).by_thm(_TRANS(p.fact("b_iter1"), b_inner))
            # b_step: sk_step Omega_t = App_t (App_t I_t SII) (App_t I_t SII).
            p.have(
                f"b_step: sk_step Omega_t = "
                f"App_t (App_t I_t ({SII})) (App_t I_t ({SII}))"
            ).by_thm(OMEGA_T_STEP1)
            # I_POW_ZERO at SII: I_pow 0 SII = SII.
            p.have(
                f"b_pow0: I_pow 0 ({SII}) = ({SII})"
            ).by(I_POW_ZERO, SII)
            # Fold SII -> I_pow 0 SII (SYM, lifted by AP_TERM App_t I_t).
            e_inner = _APT(App_t_I_t, _SYM(p.fact("b_pow0")))
            # e_inner : App_t I_t SII = App_t I_t (I_pow 0 SII).
            # MK_COMB on (App_t lifted, e_inner) gives Td(SII) = Td(I_pow 0 SII).
            e_top = _MK(_APT(App_t_C, e_inner), e_inner)
            p.have(
                f"b_fold: App_t (App_t I_t ({SII})) (App_t I_t ({SII})) "
                f"        = {Td_0}"
            ).by_thm(e_top)
            # Chain: sk_iter (SUC0 0) Omega_t = Td(0).
            p.have(
                f"b_iter_eq: sk_iter (SUC0 0) Omega_t = {Td_0}"
            ).by_thm(_TRANS(
                p.fact("b_iter1_step"),
                _TRANS(p.fact("b_step"), p.fact("b_fold")),
            ))

            # size > 0: sk_size Td_0 = SUC0 (...) by SK_SIZE_APP; NAT0_LT_0_SUC0.
            p.have(
                f"b_sz: sk_size ({Td_0}) "
                f"      = SUC0 (n0plus (sk_size (App_t I_t (I_pow 0 ({SII})))) "
                f"                      (sk_size (App_t I_t (I_pow 0 ({SII})))))"
            ).by(
                SK_SIZE_APP,
                f"App_t I_t (I_pow 0 ({SII}))",
                f"App_t I_t (I_pow 0 ({SII}))",
            )
            p.have(
                f"b_lt_pre: nat0_lt 0 "
                f"          (SUC0 (n0plus (sk_size (App_t I_t (I_pow 0 ({SII})))) "
                f"                         (sk_size (App_t I_t (I_pow 0 ({SII}))))))"
            ).by(
                NAT0_LT_0_SUC0,
                f"n0plus (sk_size (App_t I_t (I_pow 0 ({SII})))) "
                f"        (sk_size (App_t I_t (I_pow 0 ({SII}))))",
            )
            p.have(
                f"b_size_gt: nat0_lt 0 (sk_size ({Td_0}))"
            ).by_rewrite_of("b_lt_pre", [_SYM(p.fact("b_sz"))])

            # 0 < SUC0 (SUC0 0): NAT0_LT_0_SUC0 at m := SUC0 0.
            p.have(
                "b_iter_ge: nat0_lt 0 (SUC0 (SUC0 0))"
            ).by(NAT0_LT_0_SUC0, "SUC0 0")

            # Build conjunction and EXISTS-introduce at n := SUC0 0.
            p.have(
                f"b_conj: (sk_iter (SUC0 0) Omega_t = {Td_0}) "
                f"        /\\ nat0_lt 0 (sk_size ({Td_0})) "
                f"        /\\ nat0_lt 0 (SUC0 (SUC0 0))"
            ).by_thm(_CONJ(
                p.fact("b_iter_eq"),
                _CONJ(p.fact("b_size_gt"), p.fact("b_iter_ge")),
            ))
            p.thus(
                f"?n. (sk_iter n Omega_t = {Td_0}) "
                f"    /\\ nat0_lt 0 (sk_size ({Td_0})) "
                f"    /\\ nat0_lt 0 (SUC0 n)"
            ).by_witness("SUC0 0", "b_conj")

        with p.step("IH"):
            # IH : ?n. (sk_iter n Omega_t = Td_d) /\ nat0_lt d (sk_size Td_d)
            #         /\ nat0_lt d (SUC0 n).
            p.choose("n_d", from_="IH")
            p.split("n_d_eq", "(h_iter_d, h_size_d, h_d_le_nd)")

            # OMEGA_TRAJ_I_DEPTH_STEP at d.
            p.have(
                f"h_traj: ?m. (sk_iter m ({Td_d}) = {Td_sd}) "
                f"         /\\ nat0_lt (sk_size ({Td_d})) (sk_size ({Td_sd}))"
            ).by(OMEGA_TRAJ_I_DEPTH_STEP, "d")
            p.choose("m", from_="h_traj")
            p.split("m_eq", "(h_iter_step, h_size_lt)")

            # ---- m != 0 (else sk_iter m fixes the term, contradicting size_lt).
            with p.have("h_m_neq_0: ~(m = 0)").proof():
                with p.suppose("h_m0: m = 0"):
                    # sk_iter m Td_d = sk_iter 0 Td_d  (substitute m via AP_TERM/AP_THM).
                    e_fn = _APT(p._parse("sk_iter"), p.fact("h_m0"))
                    e_at = _AP_THM(e_fn, p._parse(Td_d))
                    # e_at : sk_iter m Td_d = sk_iter 0 Td_d.
                    p.have(
                        f"h_iter0_step: sk_iter 0 ({Td_d}) = {Td_sd}"
                    ).by_thm(_TRANS(_SYM(e_at), p.fact("h_iter_step")))
                    p.have(
                        f"h_zero: sk_iter 0 ({Td_d}) = ({Td_d})"
                    ).by(SK_ITER_ZERO, Td_d)
                    p.have(
                        f"h_eq_T: ({Td_d}) = ({Td_sd})"
                    ).by_thm(_TRANS(
                        _SYM(p.fact("h_zero")),
                        p.fact("h_iter0_step"),
                    ))
                    h_size_eq = _APT(p._parse("sk_size"), p.fact("h_eq_T"))
                    # h_size_eq : sk_size Td_d = sk_size Td_sd.
                    # Rewrite h_size_lt (replace sk_size Td_sd by sk_size Td_d).
                    p.have(
                        f"h_lt_self: nat0_lt (sk_size ({Td_d})) "
                        f"                    (sk_size ({Td_d}))"
                    ).by_rewrite_of("h_size_lt", [_SYM(h_size_eq)])
                    p.have(
                        f"h_not_refl: ~(nat0_lt (sk_size ({Td_d})) "
                        f"                       (sk_size ({Td_d})))"
                    ).by(NAT0_LT_NOT_REFL, f"sk_size ({Td_d})")
                    p.absurd().by_conj("h_not_refl", "h_lt_self")

            # m = SUC0 mp.
            p.have(
                "h_m_pred: ?mp:nat0. m = SUC0 mp"
            ).by(NAT0_NEQ_ZERO_PRED, "m", "h_m_neq_0")
            p.choose("mp", from_="h_m_pred")

            # h_m_split : n0plus m n_d = SUC0 (n0plus mp n_d).
            # Derive via AP_TERM(n0plus, mp_eq) + AP_THM(n_d) chained with N0PLUS_SUC_L.
            e_fn = _APT(p._parse("n0plus"), p.fact("mp_eq"))
            e_at = _AP_THM(e_fn, p._parse("n_d"))
            # e_at : n0plus m n_d = n0plus (SUC0 mp) n_d.
            p.have(
                "h_sucL: n0plus (SUC0 mp) n_d = SUC0 (n0plus mp n_d)"
            ).by(N0PLUS_SUC_L, "mp", "n_d")
            p.have(
                "h_m_split: n0plus m n_d = SUC0 (n0plus mp n_d)"
            ).by_thm(_TRANS(e_at, p.fact("h_sucL")))

            # ---- new iter eq: sk_iter (n0plus m n_d) Omega_t = Td_sd.
            p.have(
                f"h_add: sk_iter (n0plus m n_d) Omega_t "
                f"       = sk_iter m (sk_iter n_d Omega_t)"
            ).by(SK_ITER_ADD, "m", "n_d", "Omega_t")
            # AP_TERM(sk_iter m) on h_iter_d.
            e_mid = _APT(p._parse("sk_iter m"), p.fact("h_iter_d"))
            # e_mid : sk_iter m (sk_iter n_d Omega_t) = sk_iter m Td_d.
            p.have(
                f"h_iter_new: sk_iter (n0plus m n_d) Omega_t = {Td_sd}"
            ).by_thm(_TRANS(
                p.fact("h_add"),
                _TRANS(e_mid, p.fact("h_iter_step")),
            ))

            # ---- size > SUC0 d: NAT0_LT_SUC0_INSERT(d < size_d, size_d < size_sd).
            p.have(
                f"h_size_new: nat0_lt (SUC0 d) (sk_size ({Td_sd}))"
            ).by(
                NAT0_LT_SUC0_INSERT,
                "d",
                f"sk_size ({Td_d})",
                f"sk_size ({Td_sd})",
                "h_size_d",
                "h_size_lt",
            )

            # ---- iter >= SUC0 d: nat0_lt (SUC0 d) (SUC0 (n0plus m n_d)).
            # n_d < SUC0 (n0plus mp n_d) via NAT0_LT_SUC0_N0PLUS_R.
            p.have(
                "h_nd_lt: nat0_lt n_d (SUC0 (n0plus mp n_d))"
            ).by(NAT0_LT_SUC0_N0PLUS_R, "mp", "n_d")
            # NAT0_LT_SUC0_MONO: SUC0 n_d < SUC0 (SUC0 (n0plus mp n_d)).
            p.have(
                "h_snd_lt: nat0_lt (SUC0 n_d) (SUC0 (SUC0 (n0plus mp n_d)))"
            ).by(
                NAT0_LT_SUC0_MONO,
                "n_d", "SUC0 (n0plus mp n_d)", "h_nd_lt",
            )
            # NAT0_LT_SUC0_INSERT(d < SUC0 n_d, SUC0 n_d < SUC0 (SUC0 (n0plus mp n_d))):
            #   SUC0 d < SUC0 (SUC0 (n0plus mp n_d)).
            p.have(
                "h_sd_lt: nat0_lt (SUC0 d) (SUC0 (SUC0 (n0plus mp n_d)))"
            ).by(
                NAT0_LT_SUC0_INSERT,
                "d", "SUC0 n_d", "SUC0 (SUC0 (n0plus mp n_d))",
                "h_d_le_nd", "h_snd_lt",
            )
            # Fold SUC0 (n0plus mp n_d) back to (n0plus m n_d) via SYM(h_m_split).
            # AP_TERM SUC0: SUC0 (n0plus m n_d) = SUC0 (SUC0 (n0plus mp n_d)).
            e_suc = _APT(SUC0_C, p.fact("h_m_split"))
            p.have(
                "h_iter_ge: nat0_lt (SUC0 d) (SUC0 (n0plus m n_d))"
            ).by_rewrite_of("h_sd_lt", [_SYM(e_suc)])

            # Conjoin and EXISTS-introduce at n := n0plus m n_d.
            p.have(
                f"h_conj: (sk_iter (n0plus m n_d) Omega_t = {Td_sd}) "
                f"        /\\ nat0_lt (SUC0 d) (sk_size ({Td_sd})) "
                f"        /\\ nat0_lt (SUC0 d) (SUC0 (n0plus m n_d))"
            ).by_thm(_CONJ(
                p.fact("h_iter_new"),
                _CONJ(p.fact("h_size_new"), p.fact("h_iter_ge")),
            ))
            p.thus(
                f"?n. (sk_iter n Omega_t = {Td_sd}) "
                f"    /\\ nat0_lt (SUC0 d) (sk_size ({Td_sd})) "
                f"    /\\ nat0_lt (SUC0 d) (SUC0 n)"
            ).by_witness("n0plus m n_d", "h_conj")


@proof
def OMEGA_T_REACHES_LARGE_SIZE(p):
    """|- !N L. ?k X. sk_iter (n0plus k L) Omega_t
                       = App_t (App_t I_t X) (App_t I_t X)
                    /\\ nat0_lt N (sk_size (App_t (App_t I_t X)
                                                   (App_t I_t X))).

    For any size threshold N and any iter-offset L, there is an
    Omega-shape iterate at index ``n0plus k L`` (so >= L) with size > N.

    Plugged into OMEGA_NON_HALTING at (N, L) := (sk_size (sk_iter n0
    Omega_t), n0), where n0 is the halts witness.  The witness X is
    in the trajectory image, so always of the form ``I_pow d SII`` for
    some d.

    Induction strategy (post-restatement to use OMEGA_TRAJ_I_DEPTH_STEP):

      Bootstrap (from OMEGA_T_STEP1):
        sk_iter (SUC0 0) Omega_t = App_t (App_t I_t SII) (App_t I_t SII)
                                 = Omega-shape (I_pow 0 SII).
        Pad to offset L via 0 returns at depth 0 -- requires either
        absorbing L into the witness or chaining L applications of
        OMEGA_TRAJ_I_DEPTH_STEP from the base.

      Induction on the I-depth d such that
        sk_iter (n0plus k(d) L) Omega_t = Omega-shape (I_pow d SII)
        /\\ nat0_lt N(d) (sk_size (Omega-shape (I_pow d SII)))
      where k(d) and N(d) grow with d.

      step d -> d+1:
        OMEGA_TRAJ_I_DEPTH_STEP at d gives k_step, with
          sk_iter k_step (Omega-shape (I_pow d SII))
            = Omega-shape (I_pow (SUC0 d) SII)
          /\\ nat0_lt (sk_size (Omega-shape (I_pow d SII)))
                      (sk_size (Omega-shape (I_pow (SUC0 d) SII))).
        SK_ITER_ADD chains the iter counts:
          sk_iter (n0plus k_step k(d)) L Omega_t
            = sk_iter k_step (Omega-shape (I_pow d SII))
            = Omega-shape (I_pow (SUC0 d) SII).
        Size accumulates via NAT0_LT_TRANS.

      To reach an arbitrary threshold N: iterate the step until
      sk_size (Omega-shape (I_pow d SII)) > N.  This is a separate
      strong induction on N choosing d.

    Witness X = I_pow d SII for d chosen large enough.

    Currently sorried; needs ~150-200 lines on top of the now-landed
    OMEGA_TRAJ_I_DEPTH_STEP + n0plus monos.  The headline blocker is the
    ``n0plus k L`` shape of the iter index: deriving the witness ``k``
    from "iter count exceeds L" is structurally nat0 subtraction, which
    the codebase does not provide.  A minimal closure plan:

      (a) N0PLUS_ASSOC -- ``!a b c. n0plus (n0plus a b) c
                                  = n0plus a (n0plus b c)`` (~25 lines,
          induct on c).  Needed to thread ``k`` through SK_ITER_ADD-
          composed depth-step iterations: ``n0plus m (n0plus j L)
          = n0plus (n0plus m j) L`` is what lets the maintained witness
          ``k = j_d`` evolve as ``k' := n0plus m_d j_d`` per depth step.
      (b) N0PLUS_DECOMP -- ``!L n. ~(nat0_lt n L) ==> ?k. n = n0plus k L``
          (~40 lines, induct on L with NAT0_NEQ_ZERO_PRED +
          NAT0_LT_SUC0_MONO contrapositive at the SUC0 L step).  Recovers
          ``k`` once the iter count clears L.
      (c) A weak monotone bound ``!d. ?n. sk_iter n Omega_t
                = Omega-shape (I_pow d SII) /\\ nat0_lt d (SUC0 n)``
          (~20 lines, induct on d) -- gives ``n >= d`` for the decomp
          hypothesis.  m_d >= 1 per step follows from
          OMEGA_TRAJ_I_DEPTH_STEP's size_lt (if m_d were 0, iter is
          fixed, so size cannot strictly grow).
      (d) Main: pick ``d := n0plus N L`` so both ``size > d > N`` and
          ``n >= d >= L``.  Apply N0PLUS_DECOMP for k; conjoin and
          witness.
    """
    from tactics import (
        SYM as _SYM,
        TRANS as _TRANS,
        AP_TERM as _APT,
    )
    from nat0_order import (
        NAT0_LT_SUC0_CASES,
        NAT0_LT_TRANS,
        NAT0_LT_SUC0_INSERT,
        NAT0_LT_SUC0_INV,
        NAT0_LT_NOT_REFL,
    )

    SII = "App_t (App_t S_t I_t) I_t"
    d = "n0plus N L"
    Xd = f"I_pow ({d}) ({SII})"
    Td = f"App_t (App_t I_t ({Xd})) (App_t I_t ({Xd}))"

    p.goal(
        "!N L. ?k X. sk_iter (n0plus k L) Omega_t "
        "             = App_t (App_t I_t X) (App_t I_t X) "
        "          /\\ nat0_lt N "
        "                      (sk_size (App_t (App_t I_t X) (App_t I_t X)))"
    )
    p.fix("N L")

    # d := n0plus N L.  By NAT0_LT_SUC0_N0PLUS_{L,R}: N <= d and L <= d, in
    # ``nat0_lt _ (SUC0 d)`` form.
    p.have(
        f"h_N_le_d: nat0_lt N (SUC0 ({d}))"
    ).by(NAT0_LT_SUC0_N0PLUS_L, "N", "L")
    p.have(
        f"h_L_le_d: nat0_lt L (SUC0 ({d}))"
    ).by(NAT0_LT_SUC0_N0PLUS_R, "N", "L")

    # OMEGA_DEPTH_SEQ at d: pick iter index n with iter eq + size > d + n >= d.
    # (Wrap iter equation in parens -- ``=`` is lower-prec than ``/\\``.)
    p.have(
        f"h_seq: ?n. (sk_iter n Omega_t = {Td}) "
        f"        /\\ nat0_lt ({d}) (sk_size ({Td})) "
        f"        /\\ nat0_lt ({d}) (SUC0 n)"
    ).by(OMEGA_DEPTH_SEQ, d)
    p.choose("n", from_="h_seq")
    p.split("n_eq", "(h_iter, h_size_gt_d, h_d_le_n)")

    # Lift d < size to N < size: case-split N <= d via NAT0_LT_SUC0_CASES.
    p.have(
        f"h_N_cases: N = ({d}) \\/ nat0_lt N ({d})"
    ).by(NAT0_LT_SUC0_CASES, "N", d, "h_N_le_d")
    with p.have(
        f"h_size_gt_N: nat0_lt N (sk_size ({Td}))"
    ).proof():
        with p.cases_on("h_N_cases"):
            with p.case(f"h_eq: N = ({d})"):
                # Substitute d := N in h_size_gt_d via SYM(h_eq): d = N.
                p.thus(
                    f"nat0_lt N (sk_size ({Td}))"
                ).by_rewrite_of("h_size_gt_d", [_SYM(p.fact("h_eq"))])
            with p.case(f"h_lt: nat0_lt N ({d})"):
                p.thus(
                    f"nat0_lt N (sk_size ({Td}))"
                ).by(
                    NAT0_LT_TRANS, "N", d, f"sk_size ({Td})",
                    "h_lt", "h_size_gt_d",
                )

    # ~(nat0_lt n L): from L <= d <= n, suppose n < L and chase to SUC0 n < SUC0 n.
    with p.have("h_not_n_lt_L: ~(nat0_lt n L)").proof():
        with p.suppose("h_n_lt_L: nat0_lt n L"):
            # n < L /\ L < SUC0 d  =>  SUC0 n < SUC0 d  =>  n < d.
            p.have(
                f"h_sucN_lt_sucD: nat0_lt (SUC0 n) (SUC0 ({d}))"
            ).by(
                NAT0_LT_SUC0_INSERT, "n", "L", f"SUC0 ({d})",
                "h_n_lt_L", "h_L_le_d",
            )
            p.have(
                f"h_n_lt_d: nat0_lt n ({d})"
            ).by(NAT0_LT_SUC0_INV, "n", d, "h_sucN_lt_sucD")
            # n < d /\ d < SUC0 n  =>  SUC0 n < SUC0 n.
            p.have(
                "h_refl_lt: nat0_lt (SUC0 n) (SUC0 n)"
            ).by(
                NAT0_LT_SUC0_INSERT, "n", d, "SUC0 n",
                "h_n_lt_d", "h_d_le_n",
            )
            p.have(
                "h_nref: ~(nat0_lt (SUC0 n) (SUC0 n))"
            ).by(NAT0_LT_NOT_REFL, "SUC0 n")
            p.absurd().by_conj("h_nref", "h_refl_lt")

    # N0PLUS_DECOMP at (L, n): extract k with n = n0plus k L.
    p.have(
        "h_decomp: ?k. n = n0plus k L"
    ).by(N0PLUS_DECOMP, "L", "n", "h_not_n_lt_L")
    p.choose("k", from_="h_decomp")

    # Rewrite the iter equation: h_iter ``sk_iter n Omega_t = Td`` under
    # k_eq ``n = n0plus k L``.
    # DSL friction: ``by_rewrite_of("h_iter", ["k_eq"])`` loops, because
    # ``k`` is a SELECT witness whose body still mentions ``n`` -- REWRITE_CONV
    # diverges on the substitution.  Fall back to AP_TERM + AP_THM + TRANS.
    from tactics import AP_THM as _AP_THM
    h_iter_lift = _AP_THM(
        _APT(p._parse("sk_iter"), p.fact("k_eq")),
        p._parse("Omega_t"),
    )
    # h_iter_lift : sk_iter n Omega_t = sk_iter (n0plus k L) Omega_t.
    p.have(
        f"h_iter_kL: sk_iter (n0plus k L) Omega_t = {Td}"
    ).by_thm(_TRANS(_SYM(h_iter_lift), p.fact("h_iter")))

    # EXISTS-introduce (k, X := I_pow d SII).  by_exists auto-discharges each
    # conjunct of the substituted body by alpha-matching the rules.
    p.thus(
        "?k X. sk_iter (n0plus k L) Omega_t = App_t (App_t I_t X) (App_t I_t X) "
        "    /\\ nat0_lt N (sk_size (App_t (App_t I_t X) (App_t I_t X)))"
    ).by_exists(["k", Xd], "h_iter_kL", "h_size_gt_N")


@proof
def OMEGA_NON_HALTING(p):
    """|- ~ halts Omega_t.

    Size-induction proof.  Trajectory analysis (under leftmost-outermost
    ``sk_step``):

      T0 = Omega_t                              = App_t SII SII
      T1 = sk_step T0                           = App_t (I_t SII) (I_t SII)
      T2 = sk_step T1                           = App_t ((K_t SII)(K_t SII)) (I_t SII)
                                                  [descend-L: SK_STEP_I_APP]
      T3 = sk_step T2                           = App_t SII (I_t SII)
                                                  [descend-L: K-redex fires]
      T4 = sk_step T3                           = App_t (I_t (I_t SII)) (I_t (I_t SII))
                                                  [TOP S-redex with
                                                   x=I_t, y=I_t, z=I_t SII]
      ...
    where SII = App_t (App_t S_t I_t) I_t.  Omega-shape recurs at
    iters 1, 4, 9, 16, ... with sk_size strictly growing each return.

    Proof structure:

      Suppose ``halts Omega_t``.  HALTS_AT then ``p.choose`` extracts
      ``n0`` with ``is_normal (sk_iter n0 Omega_t)``.

      Let N := sk_size (sk_iter n0 Omega_t).

      OMEGA_T_REACHES_LARGE_SIZE at (N, n0) gives k, X with
        sk_iter (n0plus k n0) Omega_t = Omega-shape X                  (a)
        nat0_lt N (sk_size (Omega-shape X)).                            (b)

      SK_ITER_PAST_NORMAL at (Omega_t, n0, k) gives
        sk_iter (n0plus k n0) Omega_t = sk_iter n0 Omega_t.            (c)

      Chain (a) + SYM(c):
        sk_iter n0 Omega_t = Omega-shape X.                             (d)

      AP_TERM sk_size to (d):
        sk_size (sk_iter n0 Omega_t) = sk_size (Omega-shape X)
        i.e.  N = sk_size (Omega-shape X).                              (e)

      Rewrite (b) by SYM(e):
        nat0_lt N N.

      NAT0_LT_NOT_REFL at N: contradiction.

    Net feeder dependencies (all stubbed above):
      ``SK_ITER_ADD``, ``SK_ITER_PAST_NORMAL``,
      ``OMEGA_SHAPE_TRAJ_RETURNS``, ``OMEGA_T_REACHES_LARGE_SIZE``.
    Plus already-shipped: HALTS_AT, OMEGA_T_STEP1, SK_ITER_SUC,
    SK_SIZE_GROWTH_OMEGA_SHAPE, IS_NORMAL_SK_ITER_FIXED,
    NAT0_LT_TRANS, NAT0_LT_NOT_REFL.

    Estimated total once feeders are filled: ~~400-600 lines (the bulk
    is OMEGA_SHAPE_TRAJ_RETURNS's peel induction).
    """
    from tactics import AP_TERM as _AP_TERM, TRANS as _TRANS, SYM as _SYM
    from nat0_order import NAT0_LT_NOT_REFL

    p.goal("~ halts Omega_t")

    with p.suppose("h_halts: halts Omega_t"):
        # ---- (1) Extract normal-iterate witness n0. ---------------------
        p.have(
            "h_at: halts Omega_t = (?n. is_normal (sk_iter n Omega_t))"
        ).by(HALTS_AT, "Omega_t")
        p.have("h_ex: ?n. is_normal (sk_iter n Omega_t)").by_eq_mp(
            "h_at", "h_halts"
        )
        p.choose("n0", from_="h_ex")
        # n0_eq : is_normal (sk_iter n0 Omega_t)

        # ---- (2) Large-size Omega-shape iterate at index n0plus k n0. ---
        # Threshold N := sk_size (sk_iter n0 Omega_t); offset L := n0.
        p.have(
            "h_big: ?k X. "
            "       sk_iter (n0plus k n0) Omega_t "
            "       = App_t (App_t I_t X) (App_t I_t X) "
            "    /\\ nat0_lt (sk_size (sk_iter n0 Omega_t)) "
            "                (sk_size (App_t (App_t I_t X) (App_t I_t X)))"
        ).by(
            OMEGA_T_REACHES_LARGE_SIZE,
            "sk_size (sk_iter n0 Omega_t)",
            "n0",
        )
        p.choose("k", from_="h_big")
        p.choose("X", from_="k_eq")
        # X_eq : sk_iter (n0plus k n0) Omega_t = Omega-shape X
        #        /\ nat0_lt (sk_size (sk_iter n0 Omega_t))
        #                   (sk_size (Omega-shape X))

        # ---- (3) Past-normal collapse: iter at n0plus k n0 = iter at n0. -
        p.have(
            "h_past: sk_iter (n0plus k n0) Omega_t = sk_iter n0 Omega_t"
        ).by(SK_ITER_PAST_NORMAL, "Omega_t", "n0", "k", "n0_eq")

        # ---- (4) Chain X_eq's first conjunct with SYM(h_past). ---------
        # sk_iter n0 Omega_t = Omega-shape X.
        # (DSL friction: ``X_eq`` is the full conjunction; split it.)
        p.split("X_eq", "(h_iter_eq, h_size_lt)")
        # h_iter_eq : sk_iter (n0plus k n0) Omega_t = Omega-shape X
        # h_size_lt : nat0_lt (sk_size (sk_iter n0 Omega_t))
        #                     (sk_size (Omega-shape X))
        p.have(
            "h_iter_at_n0: sk_iter n0 Omega_t "
            "              = App_t (App_t I_t X) (App_t I_t X)"
        ).by_thm(_TRANS(_SYM(p.fact("h_past")), p.fact("h_iter_eq")))

        # ---- (5) AP_TERM sk_size to (4): N = sk_size (Omega-shape X). --
        p.have(
            "h_size_eq: sk_size (sk_iter n0 Omega_t) "
            "           = sk_size (App_t (App_t I_t X) (App_t I_t X))"
        ).by_thm(_AP_TERM(sk_size, p.fact("h_iter_at_n0")))

        # ---- (6) Rewrite h_size_lt by SYM(h_size_eq) -> nat0_lt N N. ----
        # h_size_lt : nat0_lt N (sk_size (Omega-shape X))
        # SYM h_size_eq folds RHS back to N.
        p.have(
            "h_lt_NN: nat0_lt (sk_size (sk_iter n0 Omega_t)) "
            "                   (sk_size (sk_iter n0 Omega_t))"
        ).by_rewrite_of("h_size_lt", [_SYM(p.fact("h_size_eq"))])

        # ---- (7) Contradict via NAT0_LT_NOT_REFL. ----------------------
        p.have(
            "h_not_refl: ~(nat0_lt (sk_size (sk_iter n0 Omega_t)) "
            "                       (sk_size (sk_iter n0 Omega_t)))"
        ).by(NAT0_LT_NOT_REFL, "sk_size (sk_iter n0 Omega_t)")
        p.absurd().by_conj("h_not_refl", "h_lt_NN")


# ---------------------------------------------------------------------------
# Stage 4 -- Curry's fixed-point combinator.
#
#   Y_t := App_t L_t L_t      where    L_t := App_t S_t (App_t S_t K_t)
#                                              applied to itself appropriately;
#                                              see e.g. Barendregt Def. 6.1.3.
#
# Concretely the standard SK-encoding is
#   Y := S S K (S (K (S S (S (S S K)))) K)
# or any other Y-witness; the specific shape doesn't matter, only the
# fixed-point equation.
#
# The fixed-point theorem:
#   |- !f. is_sk_term f ==>
#          ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f).
#
# i.e. ``Y f`` reduces in finitely many steps to ``f (Y f)``.  This is
# all we need from Y for the diagonal.
# ---------------------------------------------------------------------------


# Concrete Y_t witness: Tromp's 25-symbol Y combinator in pure SK.
#
#   Y_t := SSK (S (K (SS (S (SSK)))) K)
#
# Tromp's Y' is the shortest known fixed-point combinator in pure SK.
# We use it because it provably satisfies the reduction property
#   sk_iter 7 (App_t Y_t f) = App_t f X_TROMP_f
# under the kernel's leftmost-outermost sk_step (verified by
# outside/sk_trace.py).  Curry's and Turing's standard Y combinators do
# *not* satisfy any such literal-equality fixed-point under one-way
# sk_step -- the inner Y-applied-to-f always reduces, so the trajectory
# never freezes at App_t f (App_t Y_t f).
#
# Built only from S_t and K_t -- no I_t -- so the kernel's lack of
# I-recognition doesn't block the reduction trace.
#
# Layout (left-associative):
#   SS         = App_t S_t S_t
#   SSK        = App_t (App_t S_t S_t) K_t                          -- SS K
#   S(SSK)     = App_t S_t (App_t (App_t S_t S_t) K_t)              -- S (SSK)
#   SS(S(SSK)) = App_t (App_t S_t S_t)
#                       (App_t S_t (App_t (App_t S_t S_t) K_t))
#   K(SS...)   = App_t K_t (SS(S(SSK)))                             -- inner K-applied
#   S(K(...))  = App_t S_t (K(SS(S(SSK))))                          -- arg's spine
#   arg        = App_t (S(K(SS(S(SSK))))) K_t
#   Y_t        = App_t SSK arg
_SS_t       = mk_app(App_t, S_t, S_t)
_SSK_t      = mk_app(App_t, _SS_t, K_t)
_S_SSK_t    = mk_app(App_t, S_t, _SSK_t)
_SS_S_SSK_t = mk_app(App_t, _SS_t, _S_SSK_t)
_K_inner_t  = mk_app(App_t, K_t, _SS_S_SSK_t)
_S_K_inner  = mk_app(App_t, S_t, _K_inner_t)
_arg_t      = mk_app(App_t, _S_K_inner, K_t)

Y_T_DEF = define(
    "Y_t",
    nat0_ty,
    mk_app(App_t, _SSK_t, _arg_t),
)
Y_t = mk_const("Y_t", [])


@proof
def IS_SK_TERM_Y(p):
    """|- is_sk_term Y_t.

    Tromp's Y' is built entirely from S_t and K_t -- the unfold list
    only needs Y_T_DEF; no I_T_DEF since Tromp's Y' contains no I_t.
    """
    p.goal("is_sk_term Y_t")
    p.thus("is_sk_term Y_t").by_tree(unfold=[Y_T_DEF])


# Tromp's Y' reduction trace concrete witnesses.  These are the term
# pieces we'll reference from the Y_FIXED_POINT statement and proof.
_TROMP_SSK_STR = "App_t (App_t S_t S_t) K_t"
_TROMP_INNER_STR = (
    "App_t (App_t S_t S_t) "
    "      (App_t S_t (App_t (App_t S_t S_t) K_t))"
)
_TROMP_ARG_STR = (
    f"App_t (App_t S_t (App_t K_t ({_TROMP_INNER_STR}))) K_t"
)
# X_TROMP_f -- the term such that sk_iter 7 (App_t Y_t f) = App_t f X_TROMP_f.
# Computed by the Python verifier (outside/sk_trace.py, experiment 16).
_TROMP_X_STR = (
    f"App_t (App_t (App_t S_t ({_TROMP_SSK_STR})) (App_t K_t f)) "
    f"      (App_t (App_t K_t ({_TROMP_ARG_STR})) f)"
)


@proof
def Y_FIXED_POINT(p):
    """|- !f. is_sk_term f ==>
              ?n. sk_iter n (App_t Y_t f) = App_t f X_TROMP_f.

    Tromp's Y reduction theorem.  X_TROMP_f is a specific SK term
    (the reduct of Y_t f after 7 sk_steps; see ``_TROMP_X_STR``).
    The reduction-existential form replaces the literal ``f (Y_t f)``
    target that no SK Y-combinator satisfies under one-way sk_step:
    once `Y_t f` is reduced, leftmost-outermost sk_step keeps reducing
    sub-redexes and never freezes at the literal ``f (Y_t f)`` term.

    The Stage-6 diagonal uses this together with
    ``HALTING_REDUCTION_PRESERVED`` to bridge from ``halts d`` to
    ``halts (App_t f X_TROMP_f)`` -- the literal fixed-point identity
    isn't needed.

    Trace (7 sk_steps, verified end-to-end by ``outside/sk_trace.py``
    experiment 16; each transition uses helpers already in this module):

      Let SSK = (S S) K
          ARG = S (K (SS (S (SSK)))) K              [Tromp's RHS]
          INNER = (S S) (S (SSK))                   [body inside K()]
          INNER_K = K INNER

      Step 0: rewrite Y_T_DEF -- unfolds Y_t.
          current = App_t (App_t (App_t (App_t S_t S_t) K_t) ARG) f

      Step 1: SK_STEP_S_UNDER_LEFT at (S, K, ARG, f).  1 hyp.
          Hyp:  ~(App (App S ARG) (App K ARG) = App (App (App S S) K) ARG).
          Discharge: APP_T_INJ peels to S = App S S, contradicts
          S_T_NEQ_APP_T(S, S).
          current = App_t (App_t (App_t S_t ARG) (App_t K_t ARG)) f

      Step 2: SK_STEP_S at top (x=ARG, y=App K ARG, z=f).  0 hyps.
          current = App_t (App_t ARG f) (App_t (App_t K_t ARG) f)

      Step 3: SK_STEP_S_UNDER_LEFT at (INNER_K, K, f, App (App K ARG) f).
          1 hyp.  Discharge similar to step 1 but on INNER_K's structure.
          current = App_t (App_t (App_t INNER_K f) (App_t K_t f))
                          (App_t (App_t K_t ARG) f)

      Step 4: depth-2 K-descent.  INNER_K f = App (App K INNER) f is a
          K-redex at position [LHS][LL] of the current.  Inline:
            - SK_STEP_K_UNDER_LEFT at (INNER, f, App K f) gives
              sk_step LHS = App INNER (App K f).
              Hyp: ~(INNER = App (App K INNER) f).  Discharge: APP_T_INJ
              peels INNER's top (App S S) vs K, S_T_NEQ_K_T.
            - SK_STEP_LEFT at (LHS, RHS) lifts to the outer.
          current = App_t (App_t INNER (App_t K_t f))
                          (App_t (App_t K_t ARG) f)

      Step 5: SK_STEP_S_UNDER_LEFT at (S, App_t S_t SSK, App_t K_t f, RHS).
          1 hyp, same shape as step 1.
          current = App_t (App_t (App_t S_t (App_t K_t f))
                                  (App_t (App_t S_t SSK) (App_t K_t f)))
                          (App_t (App_t K_t ARG) f)

      Step 6: SK_STEP_S at top.  0 hyps.
          current = App_t (App_t (App_t K_t f) (App_t (App_t K_t ARG) f))
                          (App_t (App_t (App_t S_t SSK) (App_t K_t f))
                                 (App_t (App_t K_t ARG) f))

      Step 7: SK_STEP_K_UNDER_LEFT at (f, App (App K ARG) f, RHS).  1 hyp.
          Hyp: ~(f = App (App K f) (App (App K ARG) f)).
          Discharge: SK_NEQ_DEEP_LEFT_WRAP at (f, K_t, (K ARG) f) -- the
          size-monotone irreflexivity corollary that says an unknown
          subterm can't equal a strictly-larger App wrapping itself.
          current = App_t f X_TROMP_f.

    Witness: n = SUC0^7 0.  Discharge of the 5 not_self hypotheses
    factored: 3 ``_discharge_s_under_left_not_self`` calls (steps 1/3/5,
    where the contradiction lives in the universal right-conjunct
    ``App y z = z`` regardless of x's shape), 2 ``SK_NEQ_DEEP_LEFT_WRAP``
    instantiations (steps 4/7).
    """
    # Term-string shorthands for the trace.
    SSK = _TROMP_SSK_STR                              # (S S) K
    INNER = _TROMP_INNER_STR                          # (S S) (S (S S K))
    INNER_K = f"App_t K_t ({INNER})"                  # K INNER
    ARG = _TROMP_ARG_STR                              # S (K INNER) K
    AKf = "App_t K_t f"                               # K f
    AKAf = f"App_t (App_t K_t ({ARG})) f"             # (K ARG) f
    ASSK = f"App_t S_t ({SSK})"                       # S (S S K) = S SSK
    # ASSK_AKf = S SSK (K f); WW = (S SSK (K f)) ((K ARG) f) = X_TROMP_f.
    ASSK_AKf = f"App_t ({ASSK}) ({AKf})"
    WW = f"App_t ({ASSK_AKf}) ({AKAf})"

    p.goal(
        "!f. is_sk_term f ==> "
        f"    ?n. sk_iter n (App_t Y_t f) = App_t f ({_TROMP_X_STR})"
    )
    p.fix("f")
    p.assume("_h_st: is_sk_term f")  # unused -- the trace is pure rewriting.

    # ---- Discharge the 5 not_self hypotheses up front. ----------------
    # Steps 1/3/5 use SK_STEP_S_UNDER_LEFT, whose not_self has the shape
    # ~(App (App x z) (App y z) = App (App (App S x) y) z) -- killed by
    # the right-conjunct ``App y z = z`` (helper handles all three).
    _discharge_s_under_left_not_self(p, "S_t", "K_t", ARG, label="ns1")
    _discharge_s_under_left_not_self(p, INNER_K, "K_t", "f", label="ns3")
    _discharge_s_under_left_not_self(p, "S_t", ASSK, AKf, label="ns5")

    # Step 4: SK_STEP_K_UNDER_LEFT_LEFT's not_self_inner has the
    # ``deep-left wrap`` shape -- SK_NEQ_DEEP_LEFT_WRAP at (INNER, K_t, f).
    p.have(
        f"ns4: ~(({INNER}) = App_t (App_t K_t ({INNER})) f)"
    ).by(SK_NEQ_DEEP_LEFT_WRAP, INNER, "K_t", "f")

    # Step 7: SK_STEP_K_UNDER_LEFT's not_self has the same deep-left
    # wrap shape at (f, K_t, (K ARG) f).
    p.have(
        f"ns7: ~(f = App_t (App_t K_t f) ({AKAf}))"
    ).by(SK_NEQ_DEEP_LEFT_WRAP, "f", "K_t", AKAf)

    # ---- 7-step sk_reduce trace.  Witness n = SUC0^7 0. ---------------
    with sk_reduce(p, "App_t Y_t f", f"App_t f ({_TROMP_X_STR})") as r:
        # Step 0: align by unfolding Y_t -- no iter bump.
        # current = App_t (App_t (App_t (App_t S_t S_t) K_t) ARG) f
        r.rewrite(Y_T_DEF)

        # Step 1: outer S-redex sits one App below f.
        # current -> App_t (App_t (App_t S_t ARG) (App_t K_t ARG)) f
        r.step(SK_STEP_S_UNDER_LEFT, "S_t", "K_t", ARG, "f", mp=["ns1"])

        # Step 2: top S-redex (x=ARG, y=K ARG, z=f).
        # current -> App_t (App_t ARG f) (App_t (App_t K_t ARG) f)
        r.step(SK_STEP_S, ARG, f"App_t K_t ({ARG})", "f")

        # Step 3: after expanding ARG, current's LHS is
        # App_t (App_t (App_t S_t INNER_K) K_t) f -- a one-deep S-redex.
        # current -> App_t (App_t (App_t INNER_K f) (App_t K_t f)) AKAf
        r.step(SK_STEP_S_UNDER_LEFT, INNER_K, "K_t", "f", AKAf, mp=["ns3"])

        # Step 4: depth-2 K-descent (INNER_K f = (K INNER) f, K-redex).
        # current -> App_t (App_t INNER (App_t K_t f)) AKAf
        r.step(
            SK_STEP_K_UNDER_LEFT_LEFT, INNER, "f", AKf, AKAf,
            mp=["ns4"],
        )

        # Step 5: INNER's spine is (S S) (S SSK), so the LHS is an
        # under-left S-redex at (x=S_t, y=S SSK, z=K f, w=AKAf).
        # current -> App_t (App_t (App_t S_t AKf) (App_t ASSK AKf)) AKAf
        r.step(
            SK_STEP_S_UNDER_LEFT, "S_t", ASSK, AKf, AKAf,
            mp=["ns5"],
        )

        # Step 6: top S-redex (x=K f, y=ASSK (K f), z=AKAf).
        # current -> App_t (App_t AKf AKAf) (App_t ASSK_AKf AKAf)
        r.step(SK_STEP_S, AKf, ASSK_AKf, AKAf)

        # Step 7: top is ((K f) AKAf) WW -- one-deep K-redex.
        # current -> App_t f WW = App_t f X_TROMP_f.  sk_reduce close
        # matches against the existential goal.
        r.step(SK_STEP_K_UNDER_LEFT, "f", AKAf, WW, mp=["ns7"])


# ---------------------------------------------------------------------------
# Stage 5 -- bracket abstraction (Curry's [x] e).
#
# We need a constant ``flip_t`` that, applied to a Church-bool b and two
# values a/c, returns ``a`` if b = K_t (true) and ``c`` if b = KI_t
# (false).  Standard encoding:
#
#   flip_t b a c  :=  b a c       (if Church booleans are K_t and KI_t,
#                                  then K_t a c -->* a and KI_t a c -->* c)
#
# Hence flip_t is just I_t.  We expose it as a named constant only to
# make the diagonal construction readable.
#
# This stage is bookkeeping; could be inlined.
# ---------------------------------------------------------------------------


@proof
def CHURCH_TRUE_REDUCES(p):
    """|- !a c. is_sk_term a /\\ is_sk_term c ==>
                ?n. sk_iter n (App_t (App_t K_t a) c) = a.

    K_t a c -->* a, i.e. the "true" Church bool selects its first arg.
    One head K-step closes it; ``sk_reduce`` synthesises the witness
    ``n = SUC0 0``.
    """
    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t K_t a) c) = a"
    )
    p.fix("a c")
    p.assume("h_st: is_sk_term a /\\ is_sk_term c")  # unused
    with sk_reduce(p, "App_t (App_t K_t a) c", "a") as r:
        r.step(SK_STEP_K, "a", "c")


@proof
def CHURCH_FALSE_REDUCES(p):
    """|- !a c. is_sk_term a /\\ is_sk_term c ==>
                ?n. sk_iter n (App_t (App_t KI_t a) c) = c.

    KI_t a c = K I a c -->* I c -->* c.

    Trace via ``sk_reduce``: unfold KI_t to expose the K-redex one App
    deep, fire it with the composed ``SK_STEP_K_UNDER_LEFT`` lemma, then
    unfold I_t into the S-redex and head-step S then K.  The single
    hypothesis ``SK_STEP_K_UNDER_LEFT`` requires -- that the K-redex's
    output ``I_t`` is not equal to the redex itself -- is discharged
    inline via APP_T_INJ over the unfolded I_t.
    """
    from tactics import CONJUNCT1 as _C1, TRANS

    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t KI_t a) c) = c"
    )
    p.fix("a c")
    p.assume("h_st: is_sk_term a /\\ is_sk_term c")  # unused

    # Discharge SK_STEP_K_UNDER_LEFT's single hypothesis at x := I_t, y := a:
    #     ~(I_t = App_t (App_t K_t I_t) a).
    # Unfold I_t on the LHS, then APP_T_INJ peels to S_t = K_t.
    with p.have(
        "not_self: ~(I_t = App_t (App_t K_t I_t) a)"
    ).proof():
        with p.suppose("h_eq: I_t = App_t (App_t K_t I_t) a"):
            p.have(
                "unf_eq: App_t (App_t S_t K_t) K_t = App_t (App_t K_t I_t) a"
            ).by_thm(TRANS(SYM(I_T_DEF), p.fact("h_eq")))
            p.have("e1: App_t S_t K_t = App_t K_t I_t /\\ K_t = a").by(
                APP_T_INJ, "App_t S_t K_t", "K_t",
                "App_t K_t I_t", "a", "unf_eq",
            )
            p.have("e1a: App_t S_t K_t = App_t K_t I_t").by_thm(
                _C1(p.fact("e1"))
            )
            p.have("e2: S_t = K_t /\\ K_t = I_t").by(
                APP_T_INJ, "S_t", "K_t", "K_t", "I_t", "e1a"
            )
            p.have("s_eq_k: S_t = K_t").by_thm(_C1(p.fact("e2")))
            p.absurd().by_conj(S_T_NEQ_K_T, "s_eq_k")

    # Build the trace via sk_reduce.
    with sk_reduce(p, "App_t (App_t KI_t a) c", "c") as r:
        r.rewrite(KI_T_DEF)
        # current = App_t (App_t (App_t K_t I_t) a) c.
        r.step(SK_STEP_K_UNDER_LEFT, "I_t", "a", "c", mp=["not_self"])
        # current = App_t I_t c.
        r.rewrite(I_T_DEF)
        # current = App_t (App_t (App_t S_t K_t) K_t) c.
        r.step(SK_STEP_S, "K_t", "K_t", "c")
        # current = App_t (App_t K_t c) (App_t K_t c).
        r.step(SK_STEP_K, "c", "App_t K_t c")
        # current = c.


# ---------------------------------------------------------------------------
# Stage 6 -- the diagonal.
#
# Assume for contradiction that some SK term H decides halting in the
# sense that, for every closed term t,
#
#       App_t H t  -->*  K_t       if halts t
#       App_t H t  -->*  KI_t      if ~halts t.
#
# (Bool-output, leftmost-outermost.)  Define
#
#       f := \\x. (H x) Omega_t K_t              -- bracket-abstracted
#       d := Y_t f                               -- fixed point of f
#
# Then ``d -->* f d -->* (H d) Omega_t K_t``.  Case split:
#   * If halts d: H d -->* K_t, so d -->* K_t a c -->* Omega_t,
#     and halts d implies halts Omega_t -- contradicting
#     OMEGA_NON_HALTING.
#   * If ~halts d: H d -->* KI_t, so d -->* KI_t a c -->* K_t, which
#     is normal -- so halts d, contradicting the assumption.
#
# Either way contradiction; hence no such H exists.
# ---------------------------------------------------------------------------


# ``halts_decider`` definition and its unfold are placed downstream, after
# ``halts_b`` is in scope (search for ``HALTS_DECIDER_DEF =``).


@proof
def HALTS_SK_STEP_BWD(p):
    """|- !t. halts (sk_step t) ==> halts t.

    Inverse of HALTS_SK_STEP_FWD: if ``sk_step t`` reaches normal form
    at iter m, then ``t`` reaches normal form at iter (SUC0 m) via
    SK_ITER_PUSH.
    """
    from tactics import AP_TERM as _AP_TERM
    p.goal("!t. halts (sk_step t) ==> halts t")
    p.fix("t")
    p.assume("h: halts (sk_step t)")
    p.have(
        "h_at_st: halts (sk_step t) = (?m. is_normal (sk_iter m (sk_step t)))"
    ).by(HALTS_AT, "sk_step t")
    p.have(
        "h_ex_st: ?m. is_normal (sk_iter m (sk_step t))"
    ).by_eq_mp("h_at_st", "h")
    p.choose("m", from_="h_ex_st")
    # m_eq : is_normal (sk_iter m (sk_step t))
    # SK_ITER_PUSH(m, t): sk_iter (SUC0 m) t = sk_iter m (sk_step t)
    p.have(
        "h_push: sk_iter (SUC0 m) t = sk_iter m (sk_step t)"
    ).by(SK_ITER_PUSH, "m", "t")
    # AP_TERM is_normal h_push: is_normal (sk_iter (SUC0 m) t)
    #                          = is_normal (sk_iter m (sk_step t)).
    # by_eq_mp is sym-tolerant: flips when the fact matches the RHS.
    p.have(
        "h_norm_succ: is_normal (sk_iter (SUC0 m) t)"
    ).by_eq_mp(_AP_TERM(is_normal, p.fact("h_push")), "m_eq")
    # Bundle as ?n. is_normal (sk_iter n t) and lift to halts t.
    p.have(
        "h_at_t: halts t = (?n. is_normal (sk_iter n t))"
    ).by(HALTS_AT, "t")
    p.have(
        "h_ex_t: ?n. is_normal (sk_iter n t)"
    ).by_witness("SUC0 m", "h_norm_succ")
    p.thus("halts t").by_eq_mp("h_at_t", "h_ex_t")


@proof
def HALTS_SK_STEP_IFF(p):
    """|- !t. halts t = halts (sk_step t).

    Iff-intro on the two directions: HALTS_SK_STEP_FWD already shipped
    above; HALTS_SK_STEP_BWD just above.
    """
    p.goal("!t. halts t = halts (sk_step t)")
    p.fix("t")
    p.have("h_fwd: halts t ==> halts (sk_step t)").by(HALTS_SK_STEP_FWD, "t")
    p.have("h_bwd: halts (sk_step t) ==> halts t").by(HALTS_SK_STEP_BWD, "t")
    p.thus("halts t = halts (sk_step t)").by_iff("h_fwd", "h_bwd")


@proof
def HALTS_SK_ITER(p):
    """|- !n t. halts t = halts (sk_iter n t).

    Induction on ``n`` with HALTS_SK_STEP_IFF as the step lemma:
      base:  halts t = halts (sk_iter 0 t)        [SK_ITER_ZERO].
      step:  halts t = halts (sk_iter n t)        [IH]
              = halts (sk_step (sk_iter n t))     [HALTS_SK_STEP_IFF]
              = halts (sk_iter (SUC0 n) t)        [SYM SK_ITER_SUC].
    """
    from tactics import AP_TERM as _AP_TERM, TRANS as _TRANS, SYM as _SYM
    p.goal("!n t. halts t = halts (sk_iter n t)")
    with p.induction("n"):
        with p.base():
            p.fix("t")
            p.have("h_z: sk_iter 0 t = t").by(SK_ITER_ZERO, "t")
            # halts t = halts (sk_iter 0 t) via AP_TERM(halts, SYM h_z).
            p.thus("halts t = halts (sk_iter 0 t)").by_thm(
                _AP_TERM(halts, _SYM(p.fact("h_z")))
            )
        with p.step("IH"):
            p.fix("t")
            p.have("h_ih: halts t = halts (sk_iter n t)").by("IH", "t")
            p.have(
                "h_step_iff: halts (sk_iter n t) "
                "            = halts (sk_step (sk_iter n t))"
            ).by(HALTS_SK_STEP_IFF, "sk_iter n t")
            p.have(
                "h_suc: sk_iter (SUC0 n) t = sk_step (sk_iter n t)"
            ).by(SK_ITER_SUC, "n", "t")
            # Chain: halts t = halts (sk_iter n t)
            #              = halts (sk_step (sk_iter n t))
            #              = halts (sk_iter (SUC0 n) t).
            # DSL friction: no by_trans tactic on a forward chain when one
            # link is itself a SYM of a fact; drop to kernel TRANS.
            eq_last = _AP_TERM(halts, _SYM(p.fact("h_suc")))
            p.thus("halts t = halts (sk_iter (SUC0 n) t)").by_thm(
                _TRANS(_TRANS(p.fact("h_ih"), p.fact("h_step_iff")), eq_last)
            )


@proof
def HALTING_REDUCTION_PRESERVED(p):
    """|- !t u n. is_sk_term t /\\ sk_iter n t = u ==> (halts t <=> halts u).

    Halting is invariant under reduction: prepending finitely many
    steps doesn't change whether a normal form is reachable.  Needed
    in both branches of the diagonal contradiction to push ``halts``
    through ``-->*``.

    Proof: HALTS_SK_ITER at (n, t) gives ``halts t = halts (sk_iter n t)``;
    AP_TERM(halts, h_eq) closes ``halts (sk_iter n t) = halts u``; TRANS.
    The ``is_sk_term t`` hypothesis is unused (the trajectory lemmas don't
    care about well-formedness) but is carried in the goal for interface
    consistency with the downstream diagonal proof.
    """
    from tactics import AP_TERM as _AP_TERM, TRANS as _TRANS
    p.goal(
        "!t u n. is_sk_term t /\\ sk_iter n t = u ==> "
        "        (halts t = halts u)"
    )
    p.fix("t u n")
    p.assume("(_h_st, h_eq): is_sk_term t /\\ sk_iter n t = u")
    p.have("h_iter: halts t = halts (sk_iter n t)").by(HALTS_SK_ITER, "n", "t")
    # AP_TERM halts h_eq : halts (sk_iter n t) = halts u.
    p.thus("halts t = halts u").by_thm(
        _TRANS(p.fact("h_iter"), _AP_TERM(halts, p.fact("h_eq")))
    )


@proof
def SK_ITER_TRANS(p):
    """|- !X Y Z. (?n. sk_iter n X = Y) /\\ (?m. sk_iter m Y = Z) ==>
                  ?p. sk_iter p X = Z.

    Transitivity of the reduction-existential.  Witness ``p := n0plus b a``
    via SK_ITER_ADD(b, a, X):
      sk_iter (n0plus b a) X = sk_iter b (sk_iter a X) = sk_iter b Y = Z.
    Not a stub -- closes against SK_ITER_ADD.
    """
    from tactics import TRANS as _TRANS
    p.goal(
        "!X Y Z. (?n. sk_iter n X = Y) /\\ (?m. sk_iter m Y = Z) "
        "        ==> (?p. sk_iter p X = Z)"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_xy, h_yz): (?n. sk_iter n X = Y) /\\ (?m. sk_iter m Y = Z)"
    )
    p.choose("a", from_="h_xy")
    # a_eq : sk_iter a X = Y
    p.choose("b", from_="h_yz")
    # b_eq : sk_iter b Y = Z
    p.have(
        "h_add: sk_iter (n0plus b a) X = sk_iter b (sk_iter a X)"
    ).by(SK_ITER_ADD, "b", "a", "X")
    # Rewrite the inner ``sk_iter a X`` to Y via a_eq.
    p.have(
        "h_chain: sk_iter (n0plus b a) X = sk_iter b Y"
    ).by_rewrite_of("h_add", ["a_eq"])
    # Chain to Z via b_eq.
    p.have(
        "h_final: sk_iter (n0plus b a) X = Z"
    ).by_thm(_TRANS(p.fact("h_chain"), p.fact("b_eq")))
    p.thus("?p. sk_iter p X = Z").by_witness("n0plus b a", "h_final")


# ---------------------------------------------------------------------------
# Church-Rosser / Standardization scaffolding for SK.
#
# ``sk_par_steps`` is the reflexive-transitive closure of one-step
# parallel reduction (non-deterministic: contracts any subset of the
# redexes present at a given moment).  We use it as a black-box
# infrastructure: three primitive properties (single-step embedding,
# left-App congruence, halts invariance) factor every halts-preservation
# argument Stage 6 needs.
#
# Full discharge of the three stubs below is the standard SK meta-theory
# (parallel reduction + diamond property + Church-Rosser + standardization
# theorem).  Estimate ~500 lines if developed from scratch in this
# module; ~200 lines if transferred via SK <-> lambda encoding.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Phase 4a -- parallel reduction.
#
# ``sk_par_step X X1`` -- one-step parallel reduction.  Inductively
# defined by:
#   REFL:  sk_par_step Z Z
#   K:     sk_par_step A A' /\ sk_par_step Y Y'
#          ==> sk_par_step (App_t (App_t K_t A) Y) A'
#   S:     sk_par_step A A' /\ sk_par_step B B' /\ sk_par_step Z Z'
#          ==> sk_par_step (App_t (App_t (App_t S_t A) B) Z)
#                          (App_t (App_t A' Z') (App_t B' Z'))
#   APP:   sk_par_step A A' /\ sk_par_step B B'
#          ==> sk_par_step (App_t A B) (App_t A' B')
#
# ``sk_par_steps X Y`` -- reflexive-transitive closure of sk_par_step.
#
# Both relations are encoded *impredicatively* (the least relation
# closed under the rules).  This avoids the wf-recursion machinery
# (which would need a four-disjunct monotonicity proof on top of the
# binary-relation packaging) and yields direct proofs of each intro
# rule via the closure body's conjunct extraction.
#
# The cost: every proof of ``sk_par_step X X1`` must instantiate the
# universal ``P`` with the desired relation.  Two places need this:
# (1) the four intro lemmas below (instantiating P = sk_par_step
# itself), and (2) the diamond proof in Phase 4d (instantiating P with
# the bullet-paired relation).  Both are mechanical.
# ---------------------------------------------------------------------------


# The closure-conditions body, parametric in a relation variable P.
# Re-used both in the sk_par_step definition and in each intro lemma
# (where it appears as the antecedent of the unfolded form).
_PAR_STEP_CLOSURE = (
    "((!Z:nat0. P Z Z) /\\ "
    " (!A:nat0. !Y:nat0. !A1:nat0. !Y1:nat0. "
    "    P A A1 /\\ P Y Y1 ==> P (App_t (App_t K_t A) Y) A1) /\\ "
    " (!A:nat0. !B:nat0. !Z:nat0. !A1:nat0. !B1:nat0. !Z1:nat0. "
    "    P A A1 /\\ P B B1 /\\ P Z Z1 ==> "
    "    P (App_t (App_t (App_t S_t A) B) Z) "
    "      (App_t (App_t A1 Z1) (App_t B1 Z1))) /\\ "
    " (!A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
    "    P A A1 /\\ P B B1 ==> P (App_t A B) (App_t A1 B1)))"
)


SK_PAR_STEP_DEF = define(
    "sk_par_step",
    parse_type("nat0 -> nat0 -> bool"),
    "\\X:nat0. \\X1:nat0. "
    "!P:nat0->nat0->bool. "
    f"{_PAR_STEP_CLOSURE} ==> P X X1",
)
sk_par_step = mk_const("sk_par_step", [])


SK_PAR_STEPS_DEF = define(
    "sk_par_steps",
    parse_type("nat0 -> nat0 -> bool"),
    "\\X:nat0. \\Y:nat0. "
    "!P:nat0->nat0->bool. "
    "((!Z:nat0. P Z Z) /\\ "
    " (!A:nat0. !B:nat0. !C:nat0. "
    "    sk_par_step A B /\\ P B C ==> P A C)) "
    "==> P X Y",
)
sk_par_steps = mk_const("sk_par_steps", [])


# ---------------------------------------------------------------------------
# Intro lemmas for sk_par_step.  Each pattern:
#   1. Build the unfolded form ``!P. closures(P) ==> P <lhs> <rhs>``
#      via a nested .proof() block:
#        * fix P, assume closures(P), split into 4 conjuncts;
#        * extract the relevant closure rule (REFL / K / S / APP);
#        * unfold any sk_par_step hypotheses (via SPEC SK_PAR_STEP_DEF + beta)
#          to obtain ``P A B`` from ``sk_par_step A B``;
#        * apply the closure rule.
#   2. Fold the unfolded form back to ``sk_par_step <lhs> <rhs>``
#      via by_unfold.
# ---------------------------------------------------------------------------


@proof
def PAR_REFL(p):
    """|- !X. sk_par_step X X.  Reflexivity of parallel reduction."""
    p.goal("!X. sk_par_step X X")
    p.fix("X")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEP_CLOSURE} ==> P X X"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEP_CLOSURE}")
        p.split("h_cl", "(refl_cl, _, _, _)")
        p.thus("P X X").by("refl_cl", "X")
    p.thus("sk_par_step X X").by_unfold("unf", SK_PAR_STEP_DEF)


def _par_step_to_P(p, ref, *, P_str="P", new_label):
    """From a fact ``sk_par_step A B`` produce ``P A B`` in scope where P is
    in scope and ``h_cl`` (the closures conjunction) is registered.

    Implementation: AP_THM SK_PAR_STEP_DEF at A, beta, AP_THM at B, beta
    to unfold ``sk_par_step A B`` to ``!P. closures(P) ==> P A B``; SPEC
    at our scope P, MP with h_cl, registers the result.
    """
    from tactics import AP_THM as _AP_THM, BETA_CONV as _BETA, TRANS as _TRANS
    from basics import dest_comb
    th = p.fact(ref) if isinstance(ref, str) else ref
    # th : sk_par_step A B
    sps_A, B = dest_comb(th._concl)
    _, A = dest_comb(sps_A)
    ap1 = _AP_THM(SK_PAR_STEP_DEF, A)
    bet1 = _BETA(rand(ap1._concl))
    spec_A = _TRANS(ap1, bet1)
    ap2 = _AP_THM(spec_A, B)
    bet2 = _BETA(rand(ap2._concl))
    spec_AB = _TRANS(ap2, bet2)
    forall_th = EQ_MP(spec_AB, th)
    P_tm = p._parse(P_str)
    inst_at_P = SPEC(P_tm, forall_th)
    result = MP(inst_at_P, p.fact("h_cl"))
    p.have(f"{new_label}: {pp(result._concl)}").by_thm(result)


@proof
def PAR_K(p):
    """|- !X X1 Y Y1.
            sk_par_step X X1 /\\ sk_par_step Y Y1
            ==> sk_par_step (App_t (App_t K_t X) Y) X1.

    K-redex contraction at parallel-reduction granularity.
    """
    from tactics import AP_THM, BETA_CONV, TRANS
    p.goal(
        "!X X1 Y Y1. sk_par_step X X1 /\\ sk_par_step Y Y1 ==> "
        "            sk_par_step (App_t (App_t K_t X) Y) X1"
    )
    p.fix("X X1 Y Y1")
    p.assume("(h_X, h_Y): sk_par_step X X1 /\\ sk_par_step Y Y1")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEP_CLOSURE} ==> P (App_t (App_t K_t X) Y) X1"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEP_CLOSURE}")
        p.split("h_cl", "(_, k_cl, _, _)")
        _par_step_to_P(p, "h_X", new_label="pX")
        _par_step_to_P(p, "h_Y", new_label="pY")
        p.have("pXY: P X X1 /\\ P Y Y1").by_thm(CONJ(p.fact("pX"), p.fact("pY")))
        p.thus("P (App_t (App_t K_t X) Y) X1").by(
            "k_cl", "X", "Y", "X1", "Y1", "pXY"
        )
    p.thus(
        "sk_par_step (App_t (App_t K_t X) Y) X1"
    ).by_unfold("unf", SK_PAR_STEP_DEF)


@proof
def PAR_S(p):
    """|- !X X1 Y Y1 Z Z1.
            sk_par_step X X1 /\\ sk_par_step Y Y1 /\\ sk_par_step Z Z1
            ==> sk_par_step (App_t (App_t (App_t S_t X) Y) Z)
                            (App_t (App_t X1 Z1) (App_t Y1 Z1)).
    """
    from tactics import AP_THM, BETA_CONV, TRANS
    p.goal(
        "!X X1 Y Y1 Z Z1. "
        "sk_par_step X X1 /\\ sk_par_step Y Y1 /\\ sk_par_step Z Z1 ==> "
        "sk_par_step (App_t (App_t (App_t S_t X) Y) Z) "
        "            (App_t (App_t X1 Z1) (App_t Y1 Z1))"
    )
    p.fix("X X1 Y Y1 Z Z1")
    p.assume(
        "(h_X, h_Y, h_Z): "
        "sk_par_step X X1 /\\ sk_par_step Y Y1 /\\ sk_par_step Z Z1"
    )
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEP_CLOSURE} ==> "
        "      P (App_t (App_t (App_t S_t X) Y) Z) "
        "        (App_t (App_t X1 Z1) (App_t Y1 Z1))"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEP_CLOSURE}")
        p.split("h_cl", "(_, _, s_cl, _)")
        _par_step_to_P(p, "h_X", new_label="pX")
        _par_step_to_P(p, "h_Y", new_label="pY")
        _par_step_to_P(p, "h_Z", new_label="pZ")
        p.have("pConj: P X X1 /\\ P Y Y1 /\\ P Z Z1").by_thm(
            CONJ(p.fact("pX"), CONJ(p.fact("pY"), p.fact("pZ")))
        )
        p.thus(
            "P (App_t (App_t (App_t S_t X) Y) Z) "
            "  (App_t (App_t X1 Z1) (App_t Y1 Z1))"
        ).by("s_cl", "X", "Y", "Z", "X1", "Y1", "Z1", "pConj")
    p.thus(
        "sk_par_step (App_t (App_t (App_t S_t X) Y) Z) "
        "            (App_t (App_t X1 Z1) (App_t Y1 Z1))"
    ).by_unfold("unf", SK_PAR_STEP_DEF)


@proof
def PAR_APP(p):
    """|- !X X1 Y Y1.
            sk_par_step X X1 /\\ sk_par_step Y Y1
            ==> sk_par_step (App_t X Y) (App_t X1 Y1).

    Congruence: par-step lifts to App componentwise.
    """
    from tactics import AP_THM, BETA_CONV, TRANS
    p.goal(
        "!X X1 Y Y1. sk_par_step X X1 /\\ sk_par_step Y Y1 ==> "
        "            sk_par_step (App_t X Y) (App_t X1 Y1)"
    )
    p.fix("X X1 Y Y1")
    p.assume("(h_X, h_Y): sk_par_step X X1 /\\ sk_par_step Y Y1")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEP_CLOSURE} ==> P (App_t X Y) (App_t X1 Y1)"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEP_CLOSURE}")
        p.split("h_cl", "(_, _, _, app_cl)")
        _par_step_to_P(p, "h_X", new_label="pX")
        _par_step_to_P(p, "h_Y", new_label="pY")
        p.have("pXY: P X X1 /\\ P Y Y1").by_thm(CONJ(p.fact("pX"), p.fact("pY")))
        p.thus("P (App_t X Y) (App_t X1 Y1)").by(
            "app_cl", "X", "Y", "X1", "Y1", "pXY"
        )
    p.thus(
        "sk_par_step (App_t X Y) (App_t X1 Y1)"
    ).by_unfold("unf", SK_PAR_STEP_DEF)


# ---------------------------------------------------------------------------
# Intro lemmas for sk_par_steps (RTC).
# ---------------------------------------------------------------------------

# The closure-conditions body for sk_par_steps; reused in each intro.
_PAR_STEPS_CLOSURE = (
    "((!Z:nat0. P Z Z) /\\ "
    " (!A:nat0. !B:nat0. !C:nat0. "
    "    sk_par_step A B /\\ P B C ==> P A C))"
)


@proof
def PAR_STEPS_REFL(p):
    """|- !X. sk_par_steps X X."""
    p.goal("!X. sk_par_steps X X")
    p.fix("X")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEPS_CLOSURE} ==> P X X"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEPS_CLOSURE}")
        p.split("h_cl", "(refl_cl, _)")
        p.thus("P X X").by("refl_cl", "X")
    p.thus("sk_par_steps X X").by_unfold("unf", SK_PAR_STEPS_DEF)


def _par_steps_to_P(p, ref, *, P_str="P", new_label):
    """Analogue of ``_par_step_to_P`` for ``sk_par_steps``."""
    from tactics import AP_THM as _AP_THM, BETA_CONV as _BETA, TRANS as _TRANS
    from basics import dest_comb
    th = p.fact(ref) if isinstance(ref, str) else ref
    sps_A, B = dest_comb(th._concl)
    _, A = dest_comb(sps_A)
    ap1 = _AP_THM(SK_PAR_STEPS_DEF, A)
    bet1 = _BETA(rand(ap1._concl))
    spec_A = _TRANS(ap1, bet1)
    ap2 = _AP_THM(spec_A, B)
    bet2 = _BETA(rand(ap2._concl))
    spec_AB = _TRANS(ap2, bet2)
    forall_th = EQ_MP(spec_AB, th)
    P_tm = p._parse(P_str)
    inst_at_P = SPEC(P_tm, forall_th)
    result = MP(inst_at_P, p.fact("h_cl"))
    p.have(f"{new_label}: {pp(result._concl)}").by_thm(result)


@proof
def PAR_STEPS_STEP(p):
    """|- !X Y Z. sk_par_step X Y /\\ sk_par_steps Y Z ==> sk_par_steps X Z.

    Prepend a single parallel step to an existing RTC chain.
    """
    p.goal(
        "!X Y Z. sk_par_step X Y /\\ sk_par_steps Y Z ==> sk_par_steps X Z"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_YZ): sk_par_step X Y /\\ sk_par_steps Y Z"
    )
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_STEPS_CLOSURE} ==> P X Z"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_STEPS_CLOSURE}")
        p.split("h_cl", "(_, step_cl)")
        _par_steps_to_P(p, "h_YZ", new_label="pYZ")
        p.have("pConj: sk_par_step X Y /\\ P Y Z").by_thm(
            CONJ(p.fact("h_XY"), p.fact("pYZ"))
        )
        p.thus("P X Z").by("step_cl", "X", "Y", "Z", "pConj")
    p.thus("sk_par_steps X Z").by_unfold("unf", SK_PAR_STEPS_DEF)


@proof
def PAR_STEP_TO_STEPS(p):
    """|- !X Y. sk_par_step X Y ==> sk_par_steps X Y.

    Single-step inclusion: every par-step is a 1-step RTC chain.
    Direct consequence of PAR_STEPS_STEP + PAR_STEPS_REFL.
    """
    p.goal("!X Y. sk_par_step X Y ==> sk_par_steps X Y")
    p.fix("X Y")
    p.assume("h_XY: sk_par_step X Y")
    p.have("h_YY: sk_par_steps Y Y").by(PAR_STEPS_REFL, "Y")
    p.have("h_conj: sk_par_step X Y /\\ sk_par_steps Y Y").by_thm(
        CONJ(p.fact("h_XY"), p.fact("h_YY"))
    )
    p.thus("sk_par_steps X Y").by(PAR_STEPS_STEP, "X", "Y", "Y", "h_conj")


# ---------------------------------------------------------------------------
# par_chain -- a context manager analogue of sk_reduce for sk_par_steps.
#
# Usage:
#   with par_chain(p, start, label="h_par") as c:
#       c.link("<intermediate_1>")
#       c.link("<intermediate_2>")
#       ...
#       c.link("<final>")
#   # registers   h_par : sk_par_steps start <final>
#
# Each ``c.link(next)`` synthesizes ``sk_par_step current next`` by
# recursive structural matching:
#   start ≡ end                                  -> PAR_REFL
#   start = App_t (App_t K_t a) b, end = a'      -> PAR_K (with par-step a -> a')
#   start = App_t (App_t (App_t S_t a) b) c,
#       end = App_t (App_t a' c') (App_t b' c')  -> PAR_S
#   start = App_t A B,
#       end = App_t A' B'                        -> PAR_APP (recurse)
# Links accumulate; ``__exit__`` composes them right-to-left via
# ``PAR_STEPS_STEP`` (seeded with ``PAR_STEPS_REFL`` at the final term).
#
# Limitation: the synth only sees structural redexes.  A folded constant
# like ``I_t`` is not an S_t-head even though ``I_t = (S_t K_t) K_t``
# definitionally -- callers must either pre-unfold such constants in
# the chain terms, or insert separate equational bridging steps.
# ---------------------------------------------------------------------------


_PC_S_t = mk_const("S_t", [])
_PC_K_t = mk_const("K_t", [])
_PC_App_t = mk_const("App_t", [])


def _pc_dest_App_t(tm):
    """If ``tm = App_t a b`` (i.e. ``Comb(Comb(App_t, a), b)``), return
    ``(a, b)``; else None."""
    from basics import is_comb, dest_comb, aconv
    if not is_comb(tm):
        return None
    head, b = dest_comb(tm)
    if not is_comb(head):
        return None
    h, a = dest_comb(head)
    if not aconv(h, _PC_App_t):
        return None
    return (a, b)


def _pc_try_K_redex(tm):
    """If ``tm = App_t (App_t K_t a) b``, return ``(a, b)``; else None."""
    from basics import aconv
    outer = _pc_dest_App_t(tm)
    if outer is None:
        return None
    inner, b = outer
    inner_unp = _pc_dest_App_t(inner)
    if inner_unp is None:
        return None
    K, a = inner_unp
    if not aconv(K, _PC_K_t):
        return None
    return (a, b)


def _pc_try_S_redex(tm):
    """If ``tm = App_t (App_t (App_t S_t a) b) c``, return ``(a, b, c)``;
    else None."""
    from basics import aconv
    outer = _pc_dest_App_t(tm)
    if outer is None:
        return None
    inner2, c = outer
    inner2_unp = _pc_dest_App_t(inner2)
    if inner2_unp is None:
        return None
    inner1, b = inner2_unp
    inner1_unp = _pc_dest_App_t(inner1)
    if inner1_unp is None:
        return None
    S, a = inner1_unp
    if not aconv(S, _PC_S_t):
        return None
    return (a, b, c)


def _pc_try_S_result(tm):
    """If ``tm = App_t (App_t aP cP1) (App_t bP cP2)``, return
    ``(aP, cP1, bP, cP2)``; else None.  Caller checks cP1 aconv cP2."""
    outer = _pc_dest_App_t(tm)
    if outer is None:
        return None
    left, right = outer
    left_unp = _pc_dest_App_t(left)
    right_unp = _pc_dest_App_t(right)
    if left_unp is None or right_unp is None:
        return None
    aP, cP1 = left_unp
    bP, cP2 = right_unp
    return (aP, cP1, bP, cP2)


class _ParChainSynthFail(Exception):
    """Raised when no par-step rule matches a (start, end) pair."""


def _pc_synth_par_step(start, end):
    """Return a kernel theorem ``|- sk_par_step start end``, or raise."""
    from basics import aconv
    if aconv(start, end):
        return SPEC(start, PAR_REFL)

    # K-redex firing.
    K_unp = _pc_try_K_redex(start)
    if K_unp is not None:
        a, b = K_unp
        try:
            par_a = _pc_synth_par_step(a, end)
            par_b = SPEC(b, PAR_REFL)
            return MP(SPECL([a, end, b, b], PAR_K), CONJ(par_a, par_b))
        except _ParChainSynthFail:
            pass

    # S-redex firing.
    S_unp = _pc_try_S_redex(start)
    if S_unp is not None:
        a, b, c = S_unp
        S_res = _pc_try_S_result(end)
        if S_res is not None:
            aP, cP1, bP, cP2 = S_res
            if aconv(cP1, cP2):
                try:
                    par_a = _pc_synth_par_step(a, aP)
                    par_b = _pc_synth_par_step(b, bP)
                    par_c = _pc_synth_par_step(c, cP1)
                    inst = SPECL([a, aP, b, bP, c, cP1], PAR_S)
                    return MP(inst, CONJ(par_a, CONJ(par_b, par_c)))
                except _ParChainSynthFail:
                    pass

    # PAR_APP descent.
    start_unp = _pc_dest_App_t(start)
    end_unp = _pc_dest_App_t(end)
    if start_unp is not None and end_unp is not None:
        sA, sB = start_unp
        eA, eB = end_unp
        try:
            par_A = _pc_synth_par_step(sA, eA)
            par_B = _pc_synth_par_step(sB, eB)
            inst = SPECL([sA, eA, sB, eB], PAR_APP)
            return MP(inst, CONJ(par_A, par_B))
        except _ParChainSynthFail:
            pass

    raise _ParChainSynthFail(
        f"par_chain: no par-step from {pp(start)} to {pp(end)}"
    )


class _ParChain:
    def __init__(self, p, start, label):
        self.p = p
        self.label = label
        self.start = p._parse(start) if isinstance(start, str) else start
        self.current = self.start
        self.links = []
        self._closed = False

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc_type is None and not self._closed:
            self._close()
        return False

    def link(self, next_tm):
        """Synthesize ``sk_par_step current next_tm`` and advance."""
        next_kt = (
            self.p._parse(next_tm) if isinstance(next_tm, str) else next_tm
        )
        par_th = _pc_synth_par_step(self.current, next_kt)
        self.links.append((self.current, next_kt, par_th))
        self.current = next_kt

    def _close(self):
        # Fold right-to-left: seed sk_par_steps last last (REFL),
        # then prepend each par-step via PAR_STEPS_STEP.
        last = self.current
        acc = SPEC(last, PAR_STEPS_REFL)
        for (ti, tj, par_th) in reversed(self.links):
            inst = SPECL([ti, tj, last], PAR_STEPS_STEP)
            acc = MP(inst, CONJ(par_th, acc))
        self.p.have(f"{self.label}: {pp(acc._concl)}").by_thm(acc)
        self._closed = True


def par_chain(p, start, *, label):
    """Context manager for assembling an ``sk_par_steps`` chain.  See
    module-level comment for the synthesis algorithm and limitations."""
    return _ParChain(p, start, label)


def _par_step_app_case(p):
    """SK_PAR_STEP_TO_SK_STEP's App-but-not-K/S sub-case.  Three-way
    sub-split on which child fixes:
      - sk_step a /= a              -> descend-left  (SK_STEP_LEFT).
      - sk_step a = a, sk_step b /= b -> descend-right (SK_STEP_RIGHT).
      - both fixed                  -> App is fixed   (SK_STEP_APP_FIXED).

    In each sub-case, PAR_APP combines IH(a) / IH(b) and PAR_REFL to
    yield sk_par_step (App a b) <reduct>; rewriting via X = App a b and
    sk_step X = <reduct> closes the goal.
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ, BETA_RULE
    # 'a' auto-introduced by cases_on; manually choose b.
    p.choose("b", from_="a_eq")
    # b_eq : X = App_t a b.
    # Lift the non-redex hypotheses from X to App_t a b via AP_TERM at
    # the negation-shape predicate, then beta-normalize, then EQ_MP.
    # (REWRITE_CONV's bottom-up rewriter no-ops on a b_eq with Var LHS
    # under our walker; AP_TERM + BETA_RULE substitutes X cleanly.)
    P_K = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. x = App_t (App_t K_t u) v)"
    )
    h_nK_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_K, p.fact("b_eq"))),
        p.fact("h_nK"),
    )
    p.have(
        "h_nK_ab: ~(?u v. App_t a b = App_t (App_t K_t u) v)"
    ).by_thm(h_nK_ab_thm)
    P_S = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. ?w:nat0. "
        "          x = App_t (App_t (App_t S_t u) v) w)"
    )
    h_nS_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_S, p.fact("b_eq"))),
        p.fact("h_nS"),
    )
    p.have(
        "h_nS_ab: ~(?u v w. App_t a b = App_t (App_t (App_t S_t u) v) w)"
    ).by_thm(h_nS_ab_thm)
    # IH at a, b -- both have strictly smaller nat0_lt.
    p.have(
        "h_lt_a_AB: nat0_lt a (App_t a b)"
    ).by(NAT0_LT_APP_T_L, "a", "b")
    p.have(
        "h_lt_b_AB: nat0_lt b (App_t a b)"
    ).by(NAT0_LT_APP_T_R, "a", "b")
    p.have("h_lt_a: nat0_lt a X").by_rewrite_of(
        "h_lt_a_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_lt_b: nat0_lt b X").by_rewrite_of(
        "h_lt_b_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_ih_a: sk_par_step a (sk_step a)").by("IH", "a", "h_lt_a")
    p.have("h_ih_b: sk_par_step b (sk_step b)").by("IH", "b", "h_lt_b")
    # 3-way sub-split via two nested LEMs.
    with p.cases_on(EXCLUDED_MIDDLE, "sk_step a = a"):
        with p.case("h_af: sk_step a = a"):
            with p.cases_on(EXCLUDED_MIDDLE, "sk_step b = b"):
                with p.case("h_bf: sk_step b = b"):
                    # Both fixed -> sk_step X = X.
                    p.have(
                        "h_sk_AB: sk_step (App_t a b) = App_t a b"
                    ).by(
                        SK_STEP_APP_FIXED, "a", "b",
                        "h_nK_ab", "h_nS_ab", "h_af", "h_bf",
                    )
                    p.have("h_sk_X: sk_step X = X").by_rewrite_of(
                        "h_sk_AB", [SYM(p.fact("b_eq"))]
                    )
                    p.have("h_refl: sk_par_step X X").by(PAR_REFL, "X")
                    # Both-fixed case: SYM(h_sk_X) is X = sk_step X.  We
                    # can't use that as a rewrite rule (non-terminating
                    # via X -> sk_step X -> sk_step (sk_step X) -> ...).
                    # Use targeted AP_TERM at the RHS slot instead.
                    p.thus("sk_par_step X (sk_step X)").by_thm(
                        EQ_MP(
                            AP_TERM(
                                p._parse("sk_par_step X"),
                                SYM(p.fact("h_sk_X")),
                            ),
                            p.fact("h_refl"),
                        )
                    )
                with p.case("h_bnf: ~(sk_step b = b)"):
                    # Descend-right.
                    p.have(
                        "h_sk_AB: sk_step (App_t a b) = "
                        "         App_t a (sk_step b)"
                    ).by(
                        SK_STEP_RIGHT, "a", "b",
                        "h_nK_ab", "h_nS_ab", "h_af", "h_bnf",
                    )
                    p.have(
                        "h_sk_X: sk_step X = App_t a (sk_step b)"
                    ).by_rewrite_of("h_sk_AB", [SYM(p.fact("b_eq"))])
                    p.have("h_aa: sk_par_step a a").by(PAR_REFL, "a")
                    p.have(
                        "h_par_AB: sk_par_step (App_t a b) "
                        "                     (App_t a (sk_step b))"
                    ).by(
                        PAR_APP, "a", "a", "b", "sk_step b",
                        _CONJ(p.fact("h_aa"), p.fact("h_ih_b")),
                    )
                    p.have(
                        "h_par_X_step: sk_par_step X (App_t a (sk_step b))"
                    ).by_rewrite_of("h_par_AB", [SYM(p.fact("b_eq"))])
                    p.thus("sk_par_step X (sk_step X)").by_rewrite_of(
                        "h_par_X_step", [SYM(p.fact("h_sk_X"))]
                    )
        with p.case("h_anf: ~(sk_step a = a)"):
            # Descend-left.
            p.have(
                "h_sk_AB: sk_step (App_t a b) = App_t (sk_step a) b"
            ).by(
                SK_STEP_LEFT, "a", "b",
                "h_nK_ab", "h_nS_ab", "h_anf",
            )
            p.have(
                "h_sk_X: sk_step X = App_t (sk_step a) b"
            ).by_rewrite_of("h_sk_AB", [SYM(p.fact("b_eq"))])
            p.have("h_bb: sk_par_step b b").by(PAR_REFL, "b")
            p.have(
                "h_par_AB: sk_par_step (App_t a b) "
                "                     (App_t (sk_step a) b)"
            ).by(
                PAR_APP, "a", "sk_step a", "b", "b",
                _CONJ(p.fact("h_ih_a"), p.fact("h_bb")),
            )
            p.have(
                "h_par_X_step: sk_par_step X (App_t (sk_step a) b)"
            ).by_rewrite_of("h_par_AB", [SYM(p.fact("b_eq"))])
            p.thus("sk_par_step X (sk_step X)").by_rewrite_of(
                "h_par_X_step", [SYM(p.fact("h_sk_X"))]
            )


def _par_step_leaf_case(p):
    """SK_PAR_STEP_TO_SK_STEP's "X is not an App" sub-case.

    From h_nK, h_nS, h_nApp build the D4-inner branch, hand it to
    ``_sk_step_select_at`` to get ``body[X, sk_step X]``; cases_on
    contradicts D1/D2/D3 via the not-shape hypotheses, leaving D4
    which yields ``sk_step X = X``.  PAR_REFL closes.
    """
    from tactics import CONJ as _CONJ
    p.have(
        "inner_leaf: "
        "~(?a b. X = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. X = App_t (App_t (App_t S_t a) b) c) /\\ "
        "~(?a b. X = App_t a b) /\\ X = X"
    ).by_thm(
        _CONJ(
            p.fact("h_nK"),
            _CONJ(
                p.fact("h_nS"),
                _CONJ(p.fact("h_nApp"), REFL(p._parse("X"))),
            ),
        )
    )
    body_th = _sk_step_select_at(p, "X", "X", "inner_leaf")
    p.have(f"body: {_sk_step_body('X', 'sk_step X')}").by_thm(body_th)
    D1, D2, D3, D4 = _sk_step_disjuncts("X", "sk_step X")
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            p.choose("u", from_="h1")
            p.choose("v", from_="u_eq")
            p.split("v_eq", "(h_app, _)")
            p.have(
                "h_kred_ex: ?a b. X = App_t (App_t K_t a) b"
            ).by_exists(["u", "v"], "h_app")
            p.absurd().by_conj("h_nK", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("u", from_="h2_ex")
            p.choose("v", from_="u_eq")
            p.choose("w", from_="v_eq")
            p.split("w_eq", "(h_app, _)")
            p.have(
                "h_sred_ex: ?a b c. X = "
                "           App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["u", "v", "w"], "h_app")
            p.absurd().by_conj("h_nS", "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_ex)")
            p.choose("u", from_="h3_ex")
            p.choose("v", from_="u_eq")
            p.split("v_eq", "(h_app, _)")
            p.have(
                "h_app_ex: ?a b. X = App_t a b"
            ).by_exists(["u", "v"], "h_app")
            p.absurd().by_conj("h_nApp", "h_app_ex")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, _, h_sk)")
            # h_sk: sk_step X = X.  SYM as rewrite rule (X -> sk_step X)
            # is non-terminating; use AP_TERM at the RHS slot.
            p.have("h_refl: sk_par_step X X").by(PAR_REFL, "X")
            p.thus("sk_par_step X (sk_step X)").by_thm(
                EQ_MP(
                    AP_TERM(
                        p._parse("sk_par_step X"),
                        SYM(p.fact("h_sk")),
                    ),
                    p.fact("h_refl"),
                )
            )


@proof
def SK_PAR_STEP_TO_SK_STEP(p):
    """|- !X. sk_par_step X (sk_step X).

    Single-step parallel reduction always relates X to its LMO ``sk_step``
    reduct.  Proof by strong induction on X (over nat0_lt) with a
    4-way case-split on X's shape:

      * K-redex (X = App K a b):  PAR_K(a, a, b, b) + reflexivity on a, b.
      * S-redex:                  PAR_S with reflexivities on a, b, c.
      * generic App (~K, ~S):     3-way sub-split on which child is fixed,
                                  applying PAR_APP with the right mix of
                                  IH(a/b) and PAR_REFL.
      * leaf (~K, ~S, ~App):      sk_step X = X via the D4-disjunct of the
                                  SK_STEP_REC body, then PAR_REFL.

    The descent rules SK_STEP_K / S / LEFT / RIGHT / APP_FIXED pin down
    sk_step X's exact form in each case; PAR_K / S / APP / REFL build
    the matching parallel-step.
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ
    p.goal("!X:nat0. sk_par_step X (sk_step X)")
    with p.strong_induction("X", "IH"):
        # IH : !k. nat0_lt k X ==> sk_par_step k (sk_step k).
        # ---- LEM split: is X a K-redex? -----------------------------------
        with p.cases_on(EXCLUDED_MIDDLE, "?a b. X = App_t (App_t K_t a) b"):
            with p.case("h_K: ?a b. X = App_t (App_t K_t a) b"):
                # X = App K a b; sk_step X = a; sk_par_step X a via PAR_K.
                # cases_on auto-introduces 'a' as a witness; we manually choose b.
                p.choose("b", from_="a_eq")
                # b_eq : X = App_t (App_t K_t a) b.
                p.have(
                    "h_sk_KAB: sk_step (App_t (App_t K_t a) b) = a"
                ).by(SK_STEP_K, "a", "b")
                p.have("h_sk_X: sk_step X = a").by_rewrite_of(
                    "h_sk_KAB", [SYM(p.fact("b_eq"))]
                )
                p.have("h_aa: sk_par_step a a").by(PAR_REFL, "a")
                p.have("h_bb: sk_par_step b b").by(PAR_REFL, "b")
                p.have(
                    "h_par_KAB: sk_par_step (App_t (App_t K_t a) b) a"
                ).by(
                    PAR_K, "a", "a", "b", "b",
                    _CONJ(p.fact("h_aa"), p.fact("h_bb")),
                )
                # Rewrite step-by-step: first App K a b -> X, then a -> sk_step X.
                # (Both simultaneously would rewrite the inner 'a' inside App K a b
                # before the outer pattern matches.)
                p.have("h_par_X_a: sk_par_step X a").by_rewrite_of(
                    "h_par_KAB", [SYM(p.fact("b_eq"))]
                )
                p.thus("sk_par_step X (sk_step X)").by_rewrite_of(
                    "h_par_X_a", [SYM(p.fact("h_sk_X"))]
                )
            with p.case("h_nK: ~(?a b. X = App_t (App_t K_t a) b)"):
                # ---- LEM split: is X an S-redex? --------------------------
                with p.cases_on(
                    EXCLUDED_MIDDLE,
                    "?a b c. X = App_t (App_t (App_t S_t a) b) c",
                ):
                    with p.case(
                        "h_S: ?a b c. X = App_t (App_t (App_t S_t a) b) c"
                    ):
                        # 'a' auto-introduced; manually choose b, c.
                        p.choose("b", from_="a_eq")
                        p.choose("c", from_="b_eq")
                        # c_eq : X = App_t (App_t (App_t S_t a) b) c.
                        p.have(
                            "h_sk_SABC: "
                            "sk_step (App_t (App_t (App_t S_t a) b) c) = "
                            "App_t (App_t a c) (App_t b c)"
                        ).by(SK_STEP_S, "a", "b", "c")
                        p.have(
                            "h_sk_X: sk_step X = App_t (App_t a c) (App_t b c)"
                        ).by_rewrite_of(
                            "h_sk_SABC", [SYM(p.fact("c_eq"))]
                        )
                        p.have("h_aa: sk_par_step a a").by(PAR_REFL, "a")
                        p.have("h_bb: sk_par_step b b").by(PAR_REFL, "b")
                        p.have("h_cc: sk_par_step c c").by(PAR_REFL, "c")
                        p.have(
                            "h_par_SABC: "
                            "sk_par_step (App_t (App_t (App_t S_t a) b) c) "
                            "            (App_t (App_t a c) (App_t b c))"
                        ).by(
                            PAR_S, "a", "a", "b", "b", "c", "c",
                            _CONJ(
                                p.fact("h_aa"),
                                _CONJ(p.fact("h_bb"), p.fact("h_cc")),
                            ),
                        )
                        p.have(
                            "h_par_X_acbc: sk_par_step X "
                            "              (App_t (App_t a c) (App_t b c))"
                        ).by_rewrite_of("h_par_SABC", [SYM(p.fact("c_eq"))])
                        p.thus("sk_par_step X (sk_step X)").by_rewrite_of(
                            "h_par_X_acbc", [SYM(p.fact("h_sk_X"))]
                        )
                    with p.case(
                        "h_nS: ~(?a b c. X = "
                        "       App_t (App_t (App_t S_t a) b) c)"
                    ):
                        # ---- LEM split: is X an App at all? ---------------
                        with p.cases_on(
                            EXCLUDED_MIDDLE, "?a b. X = App_t a b"
                        ):
                            with p.case("h_App: ?a b. X = App_t a b"):
                                _par_step_app_case(p)
                            with p.case("h_nApp: ~(?a b. X = App_t a b)"):
                                _par_step_leaf_case(p)


@proof
def SK_STEP_TO_PAR_STEPS(p):
    """|- !X. sk_par_steps X (sk_step X).

    Trivial lift: SK_PAR_STEP_TO_SK_STEP gives the single-step relation;
    PAR_STEP_TO_STEPS embeds it into the RTC.
    """
    p.goal("!X:nat0. sk_par_steps X (sk_step X)")
    p.fix("X")
    p.have("h_par: sk_par_step X (sk_step X)").by(
        SK_PAR_STEP_TO_SK_STEP, "X"
    )
    p.thus("sk_par_steps X (sk_step X)").by(
        PAR_STEP_TO_STEPS, "X", "sk_step X", "h_par"
    )


@proof
def PAR_STEPS_APP_LEFT(p):
    """|- !X X1 Y. sk_par_steps X X1 ==>
                   sk_par_steps (App_t X Y) (App_t X1 Y).

    Lift the par-step App-left congruence (provable for a single
    parallel step via PAR_APP + PAR_REFL Y) through the RTC by
    instantiating ``sk_par_steps``'s impredicative encoding with the
    lifted relation P := \\A B. sk_par_steps (App_t A Y) (App_t B Y),
    then verifying P satisfies the RTC closure conditions.
    """
    from tactics import AP_THM as _AP_THM, BETA_CONV as _BETA, TRANS as _TRANS, BETA_RULE
    p.goal(
        "!X:nat0. !X1:nat0. !Y:nat0. sk_par_steps X X1 ==> "
        "         sk_par_steps (App_t X Y) (App_t X1 Y)"
    )
    p.fix("X X1 Y")
    p.assume("h: sk_par_steps X X1")

    # ---- Unfold h via SK_PAR_STEPS_DEF + beta -----------------------------
    ap1 = _AP_THM(SK_PAR_STEPS_DEF, p._parse("X"))
    bet1 = _BETA(rand(ap1._concl))
    spec_X = _TRANS(ap1, bet1)
    ap2 = _AP_THM(spec_X, p._parse("X1"))
    bet2 = _BETA(rand(ap2._concl))
    spec_XX1 = _TRANS(ap2, bet2)
    # spec_XX1: sk_par_steps X X1 = !P. closures(P) ==> P X X1.
    h_forall = EQ_MP(spec_XX1, p.fact("h"))

    # ---- Instantiate at the lifted P --------------------------------------
    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. sk_par_steps (App_t A Y) (App_t B Y)"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)
    # inst_beta:
    #   (!Z. sk_par_steps (App Z Y) (App Z Y)) /\
    #   (!A B C. sk_par_step A B /\
    #            sk_par_steps (App B Y) (App C Y) ==>
    #            sk_par_steps (App A Y) (App C Y))
    #   ==> sk_par_steps (App X Y) (App X1 Y)

    # ---- Prove the lifted closures ---------------------------------------
    with p.have(
        "lifted_refl: !Z:nat0. sk_par_steps (App_t Z Y) (App_t Z Y)"
    ).proof():
        p.fix("Z")
        p.thus("sk_par_steps (App_t Z Y) (App_t Z Y)").by(
            PAR_STEPS_REFL, "App_t Z Y"
        )

    with p.have(
        "lifted_step: "
        "!A:nat0. !B:nat0. !C:nat0. "
        "sk_par_step A B /\\ sk_par_steps (App_t B Y) (App_t C Y) "
        "==> sk_par_steps (App_t A Y) (App_t C Y)"
    ).proof():
        p.fix("A B C")
        p.assume(
            "(h_AB, h_BC): "
            "sk_par_step A B /\\ sk_par_steps (App_t B Y) (App_t C Y)"
        )
        # Lift sk_par_step A B + refl Y to App-form via PAR_APP.
        p.have("h_YY: sk_par_step Y Y").by(PAR_REFL, "Y")
        p.have(
            "h_conj: sk_par_step A B /\\ sk_par_step Y Y"
        ).by_thm(CONJ(p.fact("h_AB"), p.fact("h_YY")))
        p.have(
            "h_App_AB: sk_par_step (App_t A Y) (App_t B Y)"
        ).by(PAR_APP, "A", "B", "Y", "Y", "h_conj")
        # Compose via PAR_STEPS_STEP.
        p.have(
            "h_conj2: sk_par_step (App_t A Y) (App_t B Y) /\\ "
            "         sk_par_steps (App_t B Y) (App_t C Y)"
        ).by_thm(CONJ(p.fact("h_App_AB"), p.fact("h_BC")))
        p.thus(
            "sk_par_steps (App_t A Y) (App_t C Y)"
        ).by(
            PAR_STEPS_STEP,
            "App_t A Y", "App_t B Y", "App_t C Y",
            "h_conj2",
        )

    p.have(
        "lifted_cl: (!Z. sk_par_steps (App_t Z Y) (App_t Z Y)) /\\ "
        "           (!A B C. sk_par_step A B /\\ "
        "                    sk_par_steps (App_t B Y) (App_t C Y) ==> "
        "                    sk_par_steps (App_t A Y) (App_t C Y))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    # MP inst_beta with the lifted closures.
    p.thus(
        "sk_par_steps (App_t X Y) (App_t X1 Y)"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))


# ---------------------------------------------------------------------------
# Phase 4d (diamond) infrastructure -- inversion lemmas for ``sk_par_step``.
#
# The impredicative encoding of ``sk_par_step`` admits inversion only via
# careful P-instantiation: pick a Q such that ``closures(Q)`` is provable,
# SPEC the unfolded universal at Q, and BETA_NORM the resulting redexes.
# The two atom inversions below establish the technique; they are also
# downstream prerequisites for the App-shape inversion lemmas needed by
# the triangle / diamond proof in Phase 4d.
# ---------------------------------------------------------------------------


def _par_step_atom_inv(p, atom_str, atom_neq_app_t):
    """Discharge ``!Y. sk_par_step <atom> Y ==> Y = <atom>`` for an
    atomic SK constant (``S_t`` / ``K_t``).

    Instantiates the impredicative ``P`` with
    ``Q := \\A B. A = <atom> ==> B = <atom>``.  Closure for Q:

    * REFL  ``!Z. Z = <atom> ==> Z = <atom>``        -- tautology.
    * K     conclusion's first arg is ``App_t ...`` -- vacuous via
            ``atom_neq_app_t`` (SYM-flip of the assumed ``App = atom``).
    * S, APP  same shape-clash pattern.

    DSL friction noted inline.
    """
    p.goal(f"!Y:nat0. sk_par_step {atom_str} Y ==> Y = {atom_str}")
    p.fix("Y")
    p.assume(f"h: sk_par_step {atom_str} Y")

    # Unfold ``sk_par_step <atom> Y`` to the impredicative universal.
    # DSL friction: ``by_def`` produces a registered fact, but we need
    # to immediately SPEC at a lambda; the DSL exposes only term-applied
    # SPEC via ``by_inst`` (which goes through ``_finish``).  Drop to
    # kernel calls.
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF, p._parse(atom_str), p._parse("Y")
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))

    # SPEC at Q, then BETA_NORM the raw redexes that SPEC-at-a-lambda
    # creates throughout the closures body and in the final ``Q <atom>
    # Y`` application.
    Q_tm = p._parse(
        f"\\A:nat0. \\B:nat0. (A = {atom_str}) ==> (B = {atom_str})"
    )
    h_at_Q_raw = SPEC(Q_tm, h_univ)
    h_at_Q = EQ_MP(BETA_NORM(h_at_Q_raw._concl), h_at_Q_raw)
    p.have(f"h_at_Q: {pp(h_at_Q._concl)}").by_thm(h_at_Q)

    # Prove the four closure conjuncts for Q.  DSL friction: BETA_NORM
    # surfaces ``Y`` as one of the K-rule bvars, which would collide
    # with our outer ``fix("Y")``.  We use ``M N M1 N1`` etc. as alpha-
    # equivalent fresh names; the final ``CONJ`` matches mod aconv.

    with p.have(
        f"c_refl: !Z:nat0. Z = {atom_str} ==> Z = {atom_str}"
    ).proof():
        p.fix("Z")
        p.assume(f"h_eq: Z = {atom_str}")
        p.thus(f"Z = {atom_str}").by_thm(p.fact("h_eq"))

    with p.have(
        f"c_K: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"     (M = {atom_str} ==> M1 = {atom_str}) /\\ "
        f"     (N = {atom_str} ==> N1 = {atom_str}) ==> "
        f"     App_t (App_t K_t M) N = {atom_str} ==> M1 = {atom_str}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"(_imp_M, _imp_N): "
            f"(M = {atom_str} ==> M1 = {atom_str}) /\\ "
            f"(N = {atom_str} ==> N1 = {atom_str})"
        )
        p.assume(f"h_eq: App_t (App_t K_t M) N = {atom_str}")
        p.have(
            f"h_eq_sym: {atom_str} = App_t (App_t K_t M) N"
        ).by_thm(SYM(p.fact("h_eq")))
        p.have(
            f"h_neg: ~({atom_str} = App_t (App_t K_t M) N)"
        ).by(atom_neq_app_t, "App_t K_t M", "N")
        p.absurd().by_conj("h_neg", "h_eq_sym")

    with p.have(
        f"c_S: !M:nat0. !N:nat0. !P:nat0. "
        f"     !M1:nat0. !N1:nat0. !P1:nat0. "
        f"     (M = {atom_str} ==> M1 = {atom_str}) /\\ "
        f"     (N = {atom_str} ==> N1 = {atom_str}) /\\ "
        f"     (P = {atom_str} ==> P1 = {atom_str}) ==> "
        f"     App_t (App_t (App_t S_t M) N) P = {atom_str} ==> "
        f"     App_t (App_t M1 P1) (App_t N1 P1) = {atom_str}"
    ).proof():
        p.fix("M N P M1 N1 P1")
        p.assume(
            f"(_imp_M, _imp_N, _imp_P): "
            f"(M = {atom_str} ==> M1 = {atom_str}) /\\ "
            f"(N = {atom_str} ==> N1 = {atom_str}) /\\ "
            f"(P = {atom_str} ==> P1 = {atom_str})"
        )
        p.assume(f"h_eq: App_t (App_t (App_t S_t M) N) P = {atom_str}")
        p.have(
            f"h_eq_sym: {atom_str} = App_t (App_t (App_t S_t M) N) P"
        ).by_thm(SYM(p.fact("h_eq")))
        p.have(
            f"h_neg: ~({atom_str} = App_t (App_t (App_t S_t M) N) P)"
        ).by(atom_neq_app_t, "App_t (App_t S_t M) N", "P")
        p.absurd().by_conj("h_neg", "h_eq_sym")

    with p.have(
        f"c_APP: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"       (M = {atom_str} ==> M1 = {atom_str}) /\\ "
        f"       (N = {atom_str} ==> N1 = {atom_str}) ==> "
        f"       App_t M N = {atom_str} ==> App_t M1 N1 = {atom_str}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"(_imp_M, _imp_N): "
            f"(M = {atom_str} ==> M1 = {atom_str}) /\\ "
            f"(N = {atom_str} ==> N1 = {atom_str})"
        )
        p.assume(f"h_eq: App_t M N = {atom_str}")
        p.have(f"h_eq_sym: {atom_str} = App_t M N").by_thm(
            SYM(p.fact("h_eq"))
        )
        p.have(f"h_neg: ~({atom_str} = App_t M N)").by(
            atom_neq_app_t, "M", "N"
        )
        p.absurd().by_conj("h_neg", "h_eq_sym")

    cl_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    p.have(f"h_cl: {pp(cl_th._concl)}").by_thm(cl_th)

    p.have(
        f"h_imp: {atom_str} = {atom_str} ==> Y = {atom_str}"
    ).by("h_at_Q", "h_cl")
    p.have(f"h_refl: {atom_str} = {atom_str}").by_thm(
        REFL(p._parse(atom_str))
    )
    p.thus(f"Y = {atom_str}").by("h_imp", "h_refl")


@proof
def PAR_STEP_S_T_INV(p):
    """|- !Y. sk_par_step S_t Y ==> Y = S_t.

    Atom inversion: a parallel step from ``S_t`` can only target
    ``S_t``.  Used by Phase 4d's triangle / diamond and by the App-
    shape inversion lemmas (when the closure-rule branch produces an
    intermediate par-step from an atom head).
    """
    _par_step_atom_inv(p, "S_t", S_T_NEQ_APP_T)


@proof
def PAR_STEP_K_T_INV(p):
    """|- !Y. sk_par_step K_t Y ==> Y = K_t.

    Atom inversion -- mirror of ``PAR_STEP_S_T_INV``.
    """
    _par_step_atom_inv(p, "K_t", K_T_NEQ_APP_T)


# ---------------------------------------------------------------------------
# Phase 4d -- Takahashi's complete-development function ``sk_bullet``.
#
# Defined by well-founded recursion on ``sk_size`` (same machinery as
# ``sk_step``).  Contracts every redex visible at a node simultaneously:
#
#     sk_bullet S_t                          = S_t
#     sk_bullet K_t                          = K_t
#     sk_bullet (App_t (App_t K_t X) Y)      = sk_bullet X
#     sk_bullet (App_t (App_t (App_t S_t X) Y) Z)
#       = App_t (App_t (sk_bullet X) (sk_bullet Z))
#               (App_t (sk_bullet Y) (sk_bullet Z))
#     sk_bullet (App_t X Y) [otherwise]      = App_t (sk_bullet X) (sk_bullet Y)
#
# The body is a SELECT over four guarded disjuncts (K-redex, S-redex,
# other-App, leaf), mirroring ``_sk_step_F``'s structure.  Atom unfolds
# (S_t / K_t) fall into the leaf branch.
#
# The triangle property
#     SK_BULLET_TRIANGLE : !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A)
# is the headline lemma; ``TRIANGLE_EXISTS`` packages it as the
# existential consumed by ``PAR_STEP_DIAMOND`` / ``PAR_STEPS_STRIP`` /
# ``PAR_STEPS_CONFLUENT``.
#
# The seven named theorems below ship as ``sorry`` stubs:
#   * SK_BULLET_MONO       -- monotonicity premise for define_wf_lt
#   * SK_BULLET_S_T        -- atom unfold (leaf branch)
#   * SK_BULLET_K_T        -- atom unfold (leaf branch)
#   * SK_BULLET_K_REDEX    -- K-redex unfold (D1 branch)
#   * SK_BULLET_S_REDEX    -- S-redex unfold (D2 branch)
#   * SK_BULLET_APP_OTHER  -- non-redex App congruence (D3 branch)
#   * SK_BULLET_TRIANGLE   -- the triangle property (par_step induction)
# Once these are discharged, ``TRIANGLE_EXISTS`` (and hence
# ``PAR_STEP_DIAMOND`` etc.) follow without further sorries.
# ---------------------------------------------------------------------------


_SK_BULLET_F_DEF = define(
    "_sk_bullet_F",
    parse_type("(nat0 -> nat0) -> nat0 -> nat0"),
    "\\f:nat0->nat0. \\t:nat0. "
    "@r:nat0. "
    "(?x y. t = App_t (App_t K_t x) y /\\ r = f x) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ?x y z. t = App_t (App_t (App_t S_t x) y) z /\\ "
    "         r = App_t (App_t (f x) (f z)) (App_t (f y) (f z))) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " (?a b. t = App_t a b /\\ r = App_t (f a) (f b))) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " ~(?a b. t = App_t a b) /\\ r = t)",
)
_SK_BULLET_F = mk_const("_sk_bullet_F", [])


def _prove_sk_bullet_F_at():
    """|- !f t. _sk_bullet_F f t = body[f, t]  (two BETAs).

    Mirror of ``_prove_sk_step_F_at`` (halting.py:704).  AP_THM at f,
    BETA the resulting lambda; AP_THM at t, BETA again; GENL.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GENL
    f_var = Var("f", _sk_step_fn_ty)
    t_var = Var("t", nat0_ty)
    th_f = AP_THM(_SK_BULLET_F_DEF, f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_ft = AP_THM(th_f_eq, t_var)
    th_ft_eq = TRANS(th_ft, BETA_CONV(rand(th_ft._concl)))
    return GENL([f_var, t_var], th_ft_eq)


_SK_BULLET_F_AT = _prove_sk_bullet_F_at()


# ---------------------------------------------------------------------------
# Per-disjunct mono iffs for the bullet body.
#
#   D1 (K-redex)   : single recurse under binary ?x y existential.
#   D2 (S-redex)   : ternary recurse under triple ?x y z existential.
#   D3 (other-App) : binary recurse under ?a b -- covered by the existing
#                    ``_mono_iff_value_binary_pw_step``.
#   D4 (leaf)      : f-free, REFL.
#
# D1 and D2 don't fit the existing helper's shape (D1 has only one
# recursive call buried under two binders; D2 has three recursive calls
# under three binders).  Both follow the same CHOOSE_WITNESS / LT chain
# / MP-hyp / EXISTS-repack template -- only the binder count, the LT
# chain depths, and the payload shape differ.
#
# Shared piece factored out as ``_lt_trans_chain``; the rest is inlined
# per-disjunct because the binder-count variation would force a generic
# combinator more complex than the direct code (the EXISTS repack
# requires per-depth predicate construction).
# ---------------------------------------------------------------------------


def _lt_trans_chain(lt_steps, n_eq_th):
    """TRANS-compose a list of LT hops into ``|- nat0_lt a0 n``.

    Args:
      lt_steps : list of theorems ``[|- nat0_lt a0 a1, |- nat0_lt a1 a2,
                  ..., |- nat0_lt a_{k-1} a_k]``.  Each step's right
                  must match the next step's left.
      n_eq_th  : ``|- n = a_k`` (rewriting the final endpoint to ``n``).

    Returns ``|- nat0_lt a0 n``.

    Two call sites (D1's depth-2 chain, D2's depth-{1,2,3} chains); the
    factored piece is the TRANS-fold + final ``REWRITE_RULE [SYM(n_eq)]``.
    """
    from tactics import MP, REWRITE_RULE, SPECL, SYM
    from nat0_order import NAT0_LT_TRANS
    chain = lt_steps[0]
    for s in lt_steps[1:]:
        a_t = rand(rator(chain._concl))
        m_t = rand(chain._concl)
        b_t = rand(s._concl)
        chain = MP(
            MP(SPECL([a_t, m_t, b_t], NAT0_LT_TRANS), chain),
            s,
        )
    return REWRITE_RULE([SYM(n_eq_th)], chain)


def _bullet_F_d1_mono_iff(hyp_th, r_term):
    """|- (?x y. n = App_t (App_t K_t x) y /\\ r = f x)
        = (?x y. n = App_t (App_t K_t x) y /\\ r = g x)
    where ``n, f, g`` are read from ``hyp_th`` and ``r := r_term``.

    Direction template (mirrors ``_mono_iff_value_binary_pw_step``):
      1. CHOOSE_WITNESS x (outer ?) then y (inner ?).
      2. Extract witnesses w_x, w_y from the conjuncts.
      3. LT chain: w_x < App_t K_t w_x [NAT0_LT_APP_T_R] < n [NAT0_LT_APP_T_L]
         (two steps, composed via ``_lt_trans_chain``).
      4. MP hyp at w_x → ``f w_x = g w_x``.
      5. REWRITE_RULE payload to flip ``r = f w_x`` ↔ ``r = g w_x``.
      6. Re-pack via two EXISTS.
      7. DEDUCT_ANTISYM_RULE the two directions.
    """
    from tactics import (
        SPEC, MP, SYM, CONJ, CONJUNCT1, CONJUNCT2,
        REWRITE_RULE, EXISTS, DEDUCT_ANTISYM_RULE, ASSUME,
        CHOOSE_WITNESS, SPECL,
    )
    from axioms import dest_exists, mk_exists, mk_and
    from basics import mk_eq, mk_abs
    from hf_syntax import _extract_nfg

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    y_var = Var("y", k_ty)
    K_redex = mk_app(App_t, mk_app(App_t, K_t, x_var), y_var)

    def _body(fn):
        return mk_and(
            mk_eq(n_t, K_redex),
            mk_eq(r_term, mk_app(fn, x_var)),
        )

    body_l = _body(f_t)
    body_r = _body(g_t)
    LHS = mk_exists(x_var, mk_exists(y_var, body_l))
    RHS = mk_exists(x_var, mk_exists(y_var, body_r))

    def _direction(src, target_inner, target_fn, swap_fg):
        h_top = ASSUME(src)
        chosen_x = CHOOSE_WITNESS(dest_exists(src), h_top)
        chosen_y = CHOOSE_WITNESS(
            dest_exists(chosen_x._concl), chosen_x
        )
        n_eq_th = CONJUNCT1(chosen_y)
        payload = CONJUNCT2(chosen_y)
        # Extract witnesses from `n = App_t (App_t K_t w_x) w_y`.
        ctor_app = rand(n_eq_th._concl)
        w_y = rand(ctor_app)
        AppKwx = rand(rator(ctor_app))
        w_x = rand(AppKwx)
        # LT chain: w_x < App_t K_t w_x < App_t (App_t K_t w_x) w_y = n.
        lt_inner = SPECL([K_t, w_x], NAT0_LT_APP_T_R)
        lt_outer = SPECL([AppKwx, w_y], NAT0_LT_APP_T_L)
        lt_w_x_n = _lt_trans_chain([lt_inner, lt_outer], n_eq_th)
        # MP hyp at w_x; sym for the reverse direction.
        eq_at_wx = MP(SPEC(w_x, hyp_th), lt_w_x_n)
        if swap_fg:
            eq_at_wx = SYM(eq_at_wx)
        new_payload = REWRITE_RULE([eq_at_wx], payload)
        new_body = CONJ(n_eq_th, new_payload)
        # Re-pack: inner EXISTS over w_y, outer over w_x.
        outer_pred = mk_abs(x_var, mk_exists(y_var, target_inner))
        inner_pred_at_wx = mk_abs(
            y_var,
            mk_and(
                mk_eq(
                    n_t,
                    mk_app(App_t, mk_app(App_t, K_t, w_x), y_var),
                ),
                mk_eq(r_term, mk_app(target_fn, w_x)),
            ),
        )
        inner_th = EXISTS(inner_pred_at_wx, w_y, new_body)
        return EXISTS(outer_pred, w_x, inner_th)

    R_th = _direction(LHS, body_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _bullet_F_d2_mono_iff(hyp_th, r_term):
    """|- (?x y z. n = App_t (App_t (App_t S_t x) y) z /\\
                   r = App_t (App_t (f x) (f z)) (App_t (f y) (f z)))
        = (?x y z. ... same with g ...)
    where ``n, f, g`` come from ``hyp_th``.

    Same template as D1, scaled to three binders.  LT-chain depths:
      * z: 1 step  -- z < (App_t ... z) = n  via NAT0_LT_APP_T_R.
      * y: 2 steps -- y < App_t (App_t S_t x) y [R]
                         < (App_t (App_t (App_t S_t x) y) z) [L] = n.
      * x: 3 steps -- x < App_t S_t x [R]
                         < App_t (App_t S_t x) y [L]
                         < (App_t (App_t (App_t S_t x) y) z) [L] = n.

    All three LT-to-n facts feed independent ``MP(SPEC(w, hyp), ...)``
    calls; a single ``REWRITE_RULE`` with the three eqs simultaneously
    substitutes on the payload (which mentions ``f x, f y, f z``).
    """
    from tactics import (
        SPEC, MP, SYM, CONJ, CONJUNCT1, CONJUNCT2,
        REWRITE_RULE, EXISTS, DEDUCT_ANTISYM_RULE, ASSUME,
        CHOOSE_WITNESS, SPECL,
    )
    from axioms import dest_exists, mk_exists, mk_and
    from basics import mk_eq, mk_abs
    from hf_syntax import _extract_nfg

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    y_var = Var("y", k_ty)
    z_var = Var("z", k_ty)
    AppSx = mk_app(App_t, S_t, x_var)
    AppAppSxy = mk_app(App_t, AppSx, y_var)
    S_redex = mk_app(App_t, AppAppSxy, z_var)

    def _val(fn):
        return mk_app(
            App_t,
            mk_app(App_t, mk_app(fn, x_var), mk_app(fn, z_var)),
            mk_app(App_t, mk_app(fn, y_var), mk_app(fn, z_var)),
        )

    def _body(fn):
        return mk_and(mk_eq(n_t, S_redex), mk_eq(r_term, _val(fn)))

    body_l = _body(f_t)
    body_r = _body(g_t)
    LHS = mk_exists(
        x_var, mk_exists(y_var, mk_exists(z_var, body_l))
    )
    RHS = mk_exists(
        x_var, mk_exists(y_var, mk_exists(z_var, body_r))
    )

    def _direction(src, target_inner, target_fn, swap_fg):
        h_top = ASSUME(src)
        chosen_x = CHOOSE_WITNESS(dest_exists(src), h_top)
        chosen_y = CHOOSE_WITNESS(
            dest_exists(chosen_x._concl), chosen_x
        )
        chosen_z = CHOOSE_WITNESS(
            dest_exists(chosen_y._concl), chosen_y
        )
        n_eq_th = CONJUNCT1(chosen_z)
        payload = CONJUNCT2(chosen_z)
        # Extract witnesses from
        #   n = App_t (App_t (App_t S_t w_x) w_y) w_z.
        outer_app = rand(n_eq_th._concl)
        w_z = rand(outer_app)
        mid_app = rand(rator(outer_app))  # App_t (App_t S_t w_x) w_y
        w_y = rand(mid_app)
        AppSwx = rand(rator(mid_app))      # App_t S_t w_x
        w_x = rand(AppSwx)
        # LT chains, all to n via _lt_trans_chain (which auto-rewrites
        # the final endpoint with SYM(n_eq_th)).
        lt_z = _lt_trans_chain(
            [SPECL([mid_app, w_z], NAT0_LT_APP_T_R)],
            n_eq_th,
        )
        lt_y = _lt_trans_chain(
            [
                SPECL([AppSwx, w_y], NAT0_LT_APP_T_R),
                SPECL([mid_app, w_z], NAT0_LT_APP_T_L),
            ],
            n_eq_th,
        )
        lt_x = _lt_trans_chain(
            [
                SPECL([S_t, w_x], NAT0_LT_APP_T_R),
                SPECL([AppSwx, w_y], NAT0_LT_APP_T_L),
                SPECL([mid_app, w_z], NAT0_LT_APP_T_L),
            ],
            n_eq_th,
        )
        eq_at_wx = MP(SPEC(w_x, hyp_th), lt_x)
        eq_at_wy = MP(SPEC(w_y, hyp_th), lt_y)
        eq_at_wz = MP(SPEC(w_z, hyp_th), lt_z)
        if swap_fg:
            eq_at_wx = SYM(eq_at_wx)
            eq_at_wy = SYM(eq_at_wy)
            eq_at_wz = SYM(eq_at_wz)
        # Simultaneous rewrite on the payload: three f-calls become
        # three g-calls (or vice versa for the reverse direction).
        new_payload = REWRITE_RULE(
            [eq_at_wx, eq_at_wy, eq_at_wz], payload
        )
        new_body = CONJ(n_eq_th, new_payload)
        # Re-pack: triple EXISTS.  Each predicate captures the previous
        # witnesses; only the current binder is free.
        outermost_pred = mk_abs(
            x_var,
            mk_exists(y_var, mk_exists(z_var, target_inner)),
        )
        # Compute target_inner with x:=w_x: substitute mentally; we
        # rebuild the term explicitly to avoid INST subtleties.
        AppSwx_t = mk_app(App_t, S_t, w_x)

        def _val_at(fn, x_t, y_t, z_t):
            return mk_app(
                App_t,
                mk_app(App_t, mk_app(fn, x_t), mk_app(fn, z_t)),
                mk_app(App_t, mk_app(fn, y_t), mk_app(fn, z_t)),
            )

        mid_pred_at_wx = mk_abs(
            y_var,
            mk_exists(
                z_var,
                mk_and(
                    mk_eq(
                        n_t,
                        mk_app(
                            App_t,
                            mk_app(App_t, AppSwx_t, y_var),
                            z_var,
                        ),
                    ),
                    mk_eq(
                        r_term,
                        _val_at(target_fn, w_x, y_var, z_var),
                    ),
                ),
            ),
        )
        AppAppSwxwy_t = mk_app(App_t, AppSwx_t, w_y)
        innermost_pred_at_wxwy = mk_abs(
            z_var,
            mk_and(
                mk_eq(
                    n_t,
                    mk_app(App_t, AppAppSwxwy_t, z_var),
                ),
                mk_eq(
                    r_term,
                    _val_at(target_fn, w_x, w_y, z_var),
                ),
            ),
        )
        z_ex = EXISTS(innermost_pred_at_wxwy, w_z, new_body)
        y_ex = EXISTS(mid_pred_at_wx, w_y, z_ex)
        return EXISTS(outermost_pred, w_x, y_ex)

    R_th = _direction(LHS, body_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


@proof
def SK_BULLET_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                 ==> _sk_bullet_F f n = _sk_bullet_F g n.

    Mirrors ``SK_STEP_MONO``'s stitch pattern (or_chain_collapse +
    _lift_select_eq + SPECL through ``_SK_BULLET_F_AT``).  Per-disjunct
    iffs:
      D1 (K-redex, single recurse)    -- ``_bullet_F_d1_mono_iff``
                                         (sorry-stubbed helper).
      D2 (S-redex, ternary recurse)   -- ``_bullet_F_d2_mono_iff``
                                         (sorry-stubbed helper);
                                         prepended with ``~K`` via
                                         AP_TERM(/\\) lift.
      D3 (other-App, binary recurse)  -- ``_mono_iff_value_binary_pw_step``
                                         (existing, real); prepended
                                         with ``~K /\\ ~S`` via two
                                         AP_TERM(/\\) lifts.
      D4 (leaf, f-free)               -- REFL.

    The two stubs are isolated behind helper functions so MONO itself
    is fully discharged; once the LT_TRANS dances are written, only
    those helpers need updating.

    DSL friction: the per-disjunct iffs return kernel theorems with
    ``r_var`` free.  ``or_chain_collapse`` consumes them as a list;
    ``_lift_select_eq`` ABSes over ``r_var`` and AP_TERMs through the
    polymorphic ``@``.  All four iffs must share the same free
    ``r_var`` -- we use the kernel ``Var("r", nat0_ty)`` consistently
    rather than reparsing.
    """
    from tactics import (
        AP_TERM as _AP_TERM,
        SPECL as _SPECL,
        TRANS as _TRANS,
        SYM as _SYM,
        or_chain_collapse as _or_collapse,
    )
    from hf_syntax import _mono_iff_value_binary_pw_step, _extract_nfg
    from fusion import mk_comb as _mk_comb
    from axioms import (
        mk_and as _mk_and,
        mk_not as _mk_not,
        mk_exists as _mk_exists,
    )
    from basics import mk_eq as _mk_eq

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _sk_bullet_F f n = _sk_bullet_F g n",
        types={
            "f": _sk_step_fn_ty,
            "g": _sk_step_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")
    n_t, f_t, g_t, _k_ty = _extract_nfg(h_th)
    r_var = Var("r", nat0_ty)

    # K-shape, S-shape, App-shape -- needed for the ~-prefixes on
    # D2/D3 and the D4 disjunct body.  Bvars ``x, y, z, a, b`` match
    # the F_DEF body exactly (NOT the alpha-renamed ``a, b, c`` from
    # _sk_bullet_disjuncts -- those are for surface case-splits;
    # here we need term-level identity with the F_DEF for the SPECL
    # chain through _SK_BULLET_F_AT to align).
    x_v = Var("x", nat0_ty)
    y_v = Var("y", nat0_ty)
    z_v = Var("z", nat0_ty)
    a_v = Var("a", nat0_ty)
    b_v = Var("b", nat0_ty)
    K_redex_body = _mk_eq(
        n_t, mk_app(App_t, mk_app(App_t, K_t, x_v), y_v)
    )
    K_shape = _mk_exists(x_v, _mk_exists(y_v, K_redex_body))
    S_redex_body = _mk_eq(
        n_t,
        mk_app(App_t, mk_app(App_t, mk_app(App_t, S_t, x_v), y_v), z_v),
    )
    S_shape = _mk_exists(
        x_v, _mk_exists(y_v, _mk_exists(z_v, S_redex_body))
    )
    App_body = _mk_eq(n_t, mk_app(App_t, a_v, b_v))
    App_shape = _mk_exists(a_v, _mk_exists(b_v, App_body))
    AND_C = mk_const("/\\", [])

    # --- Per-disjunct iffs ------------------------------------------------

    # D1: bare existential with single recursion.
    eq_D1 = _bullet_F_d1_mono_iff(h_th, r_var)

    # D2: ~K /\ (S-existential with triple recursion).  AP_TERM lifts
    # the inner iff through the ~K conjunct.
    eq_D2_inner = _bullet_F_d2_mono_iff(h_th, r_var)
    eq_D2 = _AP_TERM(_mk_comb(AND_C, _mk_not(K_shape)), eq_D2_inner)

    # D3: ~K /\ ~S /\ (App-existential with binary recursion).  Uses
    # the existing generic binary helper; rest_builder produces the
    # payload ``r = App_t (fn a) (fn b)`` -- two AP_TERMs prepend
    # ~S then ~K.
    def _D3_rest_builder(fn, a_t, b_t, args):
        return _mk_eq(
            r_var,
            mk_app(App_t, mk_app(fn, a_t), mk_app(fn, b_t)),
        )

    eq_D3_inner = _mono_iff_value_binary_pw_step(
        App_t,
        NAT0_LT_APP_T_L,
        NAT0_LT_APP_T_R,
        h_th,
        args=[],
        rest_builder=_D3_rest_builder,
        recurses_l=True,
    )
    eq_D3_with_ns = _AP_TERM(
        _mk_comb(AND_C, _mk_not(S_shape)), eq_D3_inner
    )
    eq_D3 = _AP_TERM(_mk_comb(AND_C, _mk_not(K_shape)), eq_D3_with_ns)

    # D4: f-free leaf branch.  REFL of the full disjunct.
    D4 = _mk_and(
        _mk_not(K_shape),
        _mk_and(
            _mk_not(S_shape),
            _mk_and(_mk_not(App_shape), _mk_eq(r_var, n_t)),
        ),
    )
    eq_D4 = REFL(D4)

    # --- Stitch + lift + chain through F_AT -------------------------------

    body_eq_at_r = _or_collapse([eq_D1, eq_D2, eq_D3, eq_D4])
    select_eq = _lift_select_eq(r_var, body_eq_at_r)
    spec_f = _SPECL([f_t, n_t], _SK_BULLET_F_AT)
    spec_g = _SPECL([g_t, n_t], _SK_BULLET_F_AT)
    final = _TRANS(spec_f, _TRANS(select_eq, _SYM(spec_g)))

    p.thus("_sk_bullet_F f n = _sk_bullet_F g n").by_thm(final)


# Well-founded recursive definition.
#   SK_BULLET_DEF      : |- sk_bullet = (@h. !n. h n = _sk_bullet_F h n)
#   _SK_BULLET_REC_RAW : |- !n. sk_bullet n = _sk_bullet_F sk_bullet n
SK_BULLET_DEF, _SK_BULLET_REC_RAW = define_wf_lt(
    "sk_bullet",
    _sk_step_fn_ty,
    _SK_BULLET_F,
    SK_BULLET_MONO,
)
sk_bullet = mk_const("sk_bullet", [])


# SK_BULLET_REC : |- !n. sk_bullet n = body[sk_bullet, n]
SK_BULLET_REC = _unfold_rec_via_F_def(_SK_BULLET_REC_RAW, _SK_BULLET_F_DEF)


def _sk_bullet_disjuncts(t, r):
    """Return the four disjunct strings of ``_sk_bullet_F``'s body at
    input ``t`` with the SELECT-bound variable substituted by ``r``.

    DSL friction: the F_DEF body uses ``x, y, z`` and ``a, b`` as the
    existential bvars, but unfold-lemma callers commonly fix surface
    vars ``X, Y, Z``.  We rename to ``a, b, c`` here (alpha-equivalent;
    REC is up to bvar renaming) so the case-split disjuncts can be
    pretty-printed without shadowing the surface vars.
    """
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    App_shape = f"?a b. {t} = App_t a b"
    D1 = f"(?a b. {t} = App_t (App_t K_t a) b /\\ {r} = sk_bullet a)"
    D2 = (
        f"(~({K_shape}) /\\ "
        f" ?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"         {r} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                     (App_t (sk_bullet b) (sk_bullet c)))"
    )
    D3 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ "
        f" (?a b. {t} = App_t a b /\\ "
        f"        {r} = App_t (sk_bullet a) (sk_bullet b)))"
    )
    D4 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ "
        f" ~({App_shape}) /\\ {r} = {t})"
    )
    return [D1, D2, D3, D4]


def _sk_bullet_body(t, r):
    return " \\/ ".join(_sk_bullet_disjuncts(t, r))


def _sk_bullet_select_at(p, t, witness_r, inner_branch_th):
    """Mirror of ``_sk_step_select_at`` for sk_bullet's 4-disjunct body.

    Combines: ``ex: ?r. body[t, r]`` (DISJ-chain + EXISTS) with
    ``_select_via_rec(SK_BULLET_REC, ...)`` to land on
    ``|- body[t, sk_bullet t]``.
    """
    body_at_r = _sk_bullet_body(t, witness_r)
    body_at_r_var = _sk_bullet_body(t, "r")
    p.have(f"_bullet_disj_rhs: {body_at_r}").by_disj(inner_branch_th)
    p.have(f"_bullet_ex: ?r. {body_at_r_var}").by_witness(
        witness_r, "_bullet_disj_rhs"
    )
    return _select_via_rec(SK_BULLET_REC, [p._parse(t)], p.fact("_bullet_ex"))


def _prove_sk_bullet_leaf(p, atom_str, atom_neq_lemma):
    """Shared body of SK_BULLET_S_T / SK_BULLET_K_T.  Proves
    ``sk_bullet <atom> = <atom>`` where ``atom`` is ``S_t`` or ``K_t``.

    D4 (leaf branch) fires at ``r := <atom>``: its payload is exactly
    ``r = t`` which is reflexive at this witness.  D1 / D2 / D3 all
    contain App_t-shaped existentials over ``t = <atom>``; each is
    refuted via ``_atom_neq_App_negations`` applied to ``atom_neq_lemma``.

    Direct mirror of ``_prove_sk_step_leaf`` (halting.py:2025) — the
    disjunct structure of bullet's body matches sk_step's at D1/D2/D3
    (App-shaped existentials, modulo payload) and at D4 (the leaf
    branch with ``r = t``).
    """
    from tactics import CONJ as _CONJ
    t = atom_str
    sk_t = f"sk_bullet {t}"
    nK_lbl, nS_lbl, nApp_lbl = _atom_neq_App_negations(p, t, atom_neq_lemma)
    # Leaf-disjunct inner: nK /\ nS /\ nApp /\ atom = atom (the r = t
    # payload, instantiated at r := atom, becomes the trivial REFL).
    p.have(
        f"inner_leaf: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f"~(?a b c. {t} = App_t (App_t (App_t S_t a) b) c) /\\ "
        f"~(?a b. {t} = App_t a b) /\\ {t} = {t}"
    ).by_thm(
        _CONJ(
            p.fact(nK_lbl),
            _CONJ(
                p.fact(nS_lbl),
                _CONJ(p.fact(nApp_lbl), REFL(p._parse(t))),
            ),
        )
    )
    body_th = _sk_bullet_select_at(p, t, t, "inner_leaf")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)
    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # D1: ?a b. atom = App_t (App_t K_t a) b /\ sk_bullet atom = sk_bullet a.
            # Strip the sk_bullet-payload, extract bare K-shape, contradict nK.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nK_lbl, "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                f"h_sred_ex: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], p.fact("h_app"))
            p.absurd().by_conj(nS_lbl, "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_app)")
            p.choose("a", from_="h3_app")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_app_ex: ?a b. {t} = App_t a b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nApp_lbl, "h_app_ex")
        with p.case(f"h4: {D4}"):
            # D4 firing: ~K /\ ~S /\ ~App /\ sk_bullet atom = atom.
            # The fourth conjunct IS the goal.
            p.split("h4", "(_, _, _, h_sk)")
            p.thus(f"{sk_t} = {t}").by_thm(p.fact("h_sk"))


@proof
def SK_BULLET_S_T(p):
    """|- sk_bullet S_t = S_t.  D4 fires; D1/D2/D3 refuted via S_T_NEQ_APP_T."""
    p.goal("sk_bullet S_t = S_t")
    _prove_sk_bullet_leaf(p, "S_t", S_T_NEQ_APP_T)


@proof
def SK_BULLET_K_T(p):
    """|- sk_bullet K_t = K_t.  Same structure as SK_BULLET_S_T via K_T_NEQ_APP_T."""
    p.goal("sk_bullet K_t = K_t")
    _prove_sk_bullet_leaf(p, "K_t", K_T_NEQ_APP_T)


@proof
def SK_BULLET_K_REDEX(p):
    """|- !X Y. sk_bullet (App_t (App_t K_t X) Y) = sk_bullet X.

    K-redex disjunct (D1) fires at the natural witness ``r := sk_bullet X``;
    D2 / D3 / D4 all carry a ~K guard, refuted by the obvious K-redex
    existence of the input.  Structure mirrors SK_STEP_K.

    In D1's firing branch, the existential bvars ``a, b`` from the body's
    D1 must be identified with the surface ``X, Y`` so that ``h_sk:
    sk_t = sk_bullet a`` can be lifted back to ``sk_t = sk_bullet X``.
    APP_T_INJ peels the K-redex twice: first to extract ``App_t K_t X =
    App_t K_t a /\\ Y = b``, then to extract ``K_t = K_t /\\ X = a``.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. "
        "sk_bullet (App_t (App_t K_t X) Y) = sk_bullet X"
    )
    p.fix("X Y")
    t = "App_t (App_t K_t X) Y"
    sk_t = f"sk_bullet ({t})"
    val = "sk_bullet X"

    # D1 inner witness at (a, b) := (X, Y), r := val.
    p.have(
        f"inner_K: ?a b. {t} = App_t (App_t K_t a) b /\\ "
        f"          {val} = sk_bullet a"
    ).by_exists(
        ["X", "Y"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    body_th = _sk_bullet_select_at(p, t, val, "inner_K")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # K-redex existence at the input; refutes ~K guards in D2-D4.
    p.have(f"is_kred: ?a b. {t} = App_t (App_t K_t a) b").by_exists(
        ["X", "Y"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # cases_on auto-binds the outer existential ``a``; we
            # manually choose ``b`` from a_eq.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_sk)")
            # APP_T_INJ twice: outer App layer, then inner App_t K_t _.
            p.have(
                "h_o: App_t K_t X = App_t K_t a /\\ Y = b"
            ).by(APP_T_INJ, "App_t K_t X", "Y", "App_t K_t a", "b", "h_app")
            p.have(
                "h_o1: App_t K_t X = App_t K_t a"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                "h_i: K_t = K_t /\\ X = a"
            ).by(APP_T_INJ, "K_t", "X", "K_t", "a", "h_o1")
            p.have("h_Xa: X = a").by_thm(_C2(p.fact("h_i")))
            # h_sk: sk_t = sk_bullet a.  SYM(h_Xa) rewrites a -> X.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk", [SYM(p.fact("h_Xa"))]
            )
        with p.case(f"h2: {D2}"):
            p.split("h2", "(h_nk, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(h_nk, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(h_nk, _, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")


@proof
def SK_BULLET_S_REDEX(p):
    """|- !X Y Z. sk_bullet (App_t (App_t (App_t S_t X) Y) Z)
                  = App_t (App_t (sk_bullet X) (sk_bullet Z))
                          (App_t (sk_bullet Y) (sk_bullet Z)).

    S-redex disjunct (D2, guarded by ~K) fires at the natural witness.
    D1 (K-branch) is refuted via ``not_kred`` (S-input's
    App_t (App_t S_t X) Y head can't unify with App_t K_t _ by
    APP_T_INJ + K_T_NEQ_APP_T at the inner App_t S_t X = K_t step).
    D3 / D4 are refuted via the obvious S-redex existence of the
    input.  Structure mirrors SK_STEP_S.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_bullet (App_t (App_t (App_t S_t X) Y) Z) = "
        "App_t (App_t (sk_bullet X) (sk_bullet Z)) "
        "      (App_t (sk_bullet Y) (sk_bullet Z))"
    )
    p.fix("X Y Z")
    t = "App_t (App_t (App_t S_t X) Y) Z"
    sk_t = f"sk_bullet ({t})"
    val = (
        "App_t (App_t (sk_bullet X) (sk_bullet Z)) "
        "      (App_t (sk_bullet Y) (sk_bullet Z))"
    )

    # not_kred: head App_t (App_t S_t X) Y can't match App_t K_t _.
    # Two APP_T_INJ peels strip the outer/middle App layers and surface
    # ``App_t S_t X = K_t``; SYM + K_T_NEQ_APP_T gives the contradiction.
    with p.have(
        f"not_kred: ~(?a b. {t} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex_kred: ?a b. {t} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex_kred")
            p.choose("b", from_="a_eq")
            p.have(
                "h_o: App_t (App_t S_t X) Y = App_t K_t a /\\ Z = b"
            ).by(APP_T_INJ, "App_t (App_t S_t X) Y", "Z",
                 "App_t K_t a", "b", "b_eq")
            p.have(
                "h_o1: App_t (App_t S_t X) Y = App_t K_t a"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t X = K_t /\\ Y = a"
            ).by(APP_T_INJ, "App_t S_t X", "Y", "K_t", "a", "h_o1")
            p.have("ASx_eq_K: App_t S_t X = K_t").by_thm(_C1(p.fact("h_m")))
            p.have("K_neq: ~(K_t = App_t S_t X)").by(
                K_T_NEQ_APP_T, "S_t", "X"
            )
            p.have("K_eq: K_t = App_t S_t X").by_thm(
                SYM(p.fact("ASx_eq_K"))
            )
            p.absurd().by_conj("K_neq", "K_eq")

    # D2 inner witness at r := val.  Witness tuple is (X, Y, Z); the
    # body's recursive ``sk_bullet a / b / c`` get substituted to
    # ``sk_bullet X / Y / Z`` in the expected pattern.
    p.have(
        f"inner_S_inner: "
        f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"        {val} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                      (App_t (sk_bullet b) (sk_bullet c))"
    ).by_exists(
        ["X", "Y", "Z"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    p.have(
        f"inner_S: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f" (?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"          {val} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                        (App_t (sk_bullet b) (sk_bullet c)))"
    ).by_thm(_CONJ(p.fact("not_kred"), p.fact("inner_S_inner")))
    body_th = _sk_bullet_select_at(p, t, val, "inner_S")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # is_sred: refutes ~S guards in D3, D4.
    p.have(
        f"is_sred: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    ).by_exists(["X", "Y", "Z"], REFL(p._parse(t)))

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # K-branch fires on an S-input: extract the (a, b) witnesses
            # via cases_on's auto-choose + manual choose-b, then re-pack
            # as ?a b. t = App_t (App_t K_t a) b to contradict not_kred.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            # The firing branch: unpack the existential triple, then
            # use APP_T_INJ three times to identify X=a, Y=b, Z=c, and
            # rewrite ``h_sk: val = App_t (App_t (sk_bullet a) (sk_bullet c))
            #                          (App_t (sk_bullet b) (sk_bullet c))``
            # back into the surface (X, Y, Z) form.
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, h_sk)")
            p.have(
                "h_o: App_t (App_t S_t X) Y = App_t (App_t S_t a) b /\\ "
                "     Z = c"
            ).by(APP_T_INJ, "App_t (App_t S_t X) Y", "Z",
                 "App_t (App_t S_t a) b", "c", "h_app")
            p.have(
                "h_o1: App_t (App_t S_t X) Y = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_o")))
            p.have("h_Zc: Z = c").by_thm(_C2(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t X = App_t S_t a /\\ Y = b"
            ).by(APP_T_INJ, "App_t S_t X", "Y",
                 "App_t S_t a", "b", "h_o1")
            p.have(
                "h_m1: App_t S_t X = App_t S_t a"
            ).by_thm(_C1(p.fact("h_m")))
            p.have("h_Yb: Y = b").by_thm(_C2(p.fact("h_m")))
            p.have(
                "h_i: S_t = S_t /\\ X = a"
            ).by(APP_T_INJ, "S_t", "X", "S_t", "a", "h_m1")
            p.have("h_Xa: X = a").by_thm(_C2(p.fact("h_i")))
            # DSL friction: by_rewrite_of rewrites the *source* fact's
            # surface form using the supplied SYM equations.  h_sk is
            # ``sk_bullet t = App_t ... a ... b ... c ...``; the three
            # SYMs turn it back to ``... X ... Y ... Z ...``.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_Xa")), SYM(p.fact("h_Yb")),
                 SYM(p.fact("h_Zc"))],
            )
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, h_ns, _)")
            p.absurd().by_conj("h_ns", "is_sred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, h_ns, _, _)")
            p.absurd().by_conj("h_ns", "is_sred")


@proof
def SK_BULLET_APP_OTHER(p):
    """|- !X Y.
            ~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\
            ~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c)
          ==> sk_bullet (App_t X Y) = App_t (sk_bullet X) (sk_bullet Y).

    Non-redex App congruence: D3 fires at the natural witness
    (a, b) := (X, Y); D1 and D2 directly carry the K-/S-redex existence
    needed to contradict the assumed negations; D4 carries the ~App
    guard, refuted by ``is_app``.

    Structure mirrors SK_STEP_LEFT but is simpler -- bullet's D3 has a
    single ``r = App_t (sk_bullet a) (sk_bullet b)`` payload (no nested
    descend-left/descend-right/fixed split), so once X = a3 and Y = b3
    are pinned via APP_T_INJ a single by_rewrite_of suffices.

    DSL friction: the negation antecedents use lowercase ``a b c`` as
    existential bvars (matching SK_STEP_LEFT's convention) rather than
    the original stub's uppercase ``A B C`` -- alpha-equivalent, but the
    lowercase form aligns with ``_sk_bullet_disjuncts``' bvar choice so
    ``by_conj("not_kred", "h_kred")`` matches without surprise.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. "
        "~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c) "
        "==> sk_bullet (App_t X Y) = App_t (sk_bullet X) (sk_bullet Y)"
    )
    p.fix("X Y")
    p.assume(
        "(not_kred, not_sred): "
        "~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c)"
    )

    t = "App_t X Y"
    sk_t = f"sk_bullet ({t})"
    val = "App_t (sk_bullet X) (sk_bullet Y)"
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"

    # D3 inner witness at (a, b) := (X, Y), r := val.
    p.have(
        f"inner_ex: ?a b. {t} = App_t a b /\\ "
        f"          {val} = App_t (sk_bullet a) (sk_bullet b)"
    ).by_exists(
        ["X", "Y"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    p.have(
        f"inner_d3: ~({K_shape}) /\\ ~({S_shape}) /\\ "
        f"          (?a b. {t} = App_t a b /\\ "
        f"                 {val} = App_t (sk_bullet a) (sk_bullet b))"
    ).by_thm(
        _CONJ(
            p.fact("not_kred"),
            _CONJ(p.fact("not_sred"), p.fact("inner_ex")),
        )
    )

    body_th = _sk_bullet_select_at(p, t, val, "inner_d3")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # App-shape witness for D4 contradiction.
    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["X", "Y"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # D1 itself is the K-redex existence (with payload r=sk_bullet a
            # tacked on); peel the ``/\\ r = sk_bullet a`` to recover the
            # bare K-shape and contradict not_kred.
            p.choose("a_d1", from_="h1")
            p.choose("b_d1", from_="a_d1_eq")
            p.split("b_d1_eq", "(h_app, _)")
            p.have(f"h_kred: {K_shape}").by_exists(
                ["a_d1", "b_d1"], "h_app"
            )
            p.absurd().by_conj("not_kred", "h_kred")
        with p.case(f"h2: {D2}"):
            # D2 has ~K guard upfront; strip it, the remaining triple
            # existential is the S-redex existence (modulo payload).
            p.split("h2", "(_, h2_ex)")
            p.choose("a_d2", from_="h2_ex")
            p.choose("b_d2", from_="a_d2_eq")
            p.choose("c_d2", from_="b_d2_eq")
            p.split("c_d2_eq", "(h_app, _)")
            p.have(f"h_sred: {S_shape}").by_exists(
                ["a_d2", "b_d2", "c_d2"], "h_app"
            )
            p.absurd().by_conj("not_sred", "h_sred")
        with p.case(f"h3: {D3}"):
            # The firing branch.  Strip the two leading negations
            # (already known), then unpack the App-existential and
            # pin X=a3, Y=b3 via APP_T_INJ.
            p.split("h3", "(_, _, h3_ex)")
            p.choose("a3", from_="h3_ex")
            p.choose("b3", from_="a3_eq")
            p.split("b3_eq", "(h_app, h_sk)")
            p.have("h_inj: X = a3 /\\ Y = b3").by(
                APP_T_INJ, "X", "Y", "a3", "b3", "h_app"
            )
            p.have("h_Xa: X = a3").by_thm(_C1(p.fact("h_inj")))
            p.have("h_Yb: Y = b3").by_thm(_C2(p.fact("h_inj")))
            # h_sk: sk_t = App_t (sk_bullet a3) (sk_bullet b3).
            # The two SYMs rewrite a3 -> X, b3 -> Y in the source.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_Xa")), SYM(p.fact("h_Yb"))],
            )
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


# ---------------------------------------------------------------------------
# Dependency stubs for SK_BULLET_TRIANGLE.
#
# PAR_STEP_K_APP_INV and PAR_STEP_S_APP_APP_INV are discharged below
# via the shared ``_par_step_app_atom_inv`` template.  BULLET_REFL,
# _TRIANGLE_APP_CLOSURE remain stubs.  TRIANGLE itself (below) is real,
# assembling the four pieces via impredicative P-instantiation with the
# strengthened invariant
#   ``P := \A B. sk_par_step A B /\ sk_par_step B (sk_bullet A)``.
# ---------------------------------------------------------------------------


def _par_step_app_atom_inv(p, atom_str, atom_inv_thm, atom_neq_app_t):
    """Discharge
        ``!X Y. sk_par_step (App_t <atom> X) Y ==>
                  ?XP. Y = App_t <atom> XP /\\ sk_par_step X XP``
    where ``<atom>`` is ``S_t`` or ``K_t``.

    Strategy: instantiate the impredicative encoding's ``P`` with
        Q := \\A B. sk_par_step A B /\\
                     (!W. A = App_t <atom> W ==>
                          ?Wp. B = App_t <atom> Wp /\\ sk_par_step W Wp)
    The first conjunct propagates par_step inside the closure
    rules (each rule's hypothesis carries it through); the second
    conjunct is the actual inversion shape.

    Closure analysis after BETA_NORM:
      REFL : both conjuncts via PAR_REFL.
      K    : par_step propagated by PAR_K from the IHs; inversion is
             vacuous -- ``App_t (App_t K_t _) _ = App_t <atom> _`` clashes
             at ``App_t K_t _ = <atom>`` (App vs leaf, ``atom_neq_app_t``).
      S    : par_step propagated by PAR_S; inversion clashes at
             ``App_t (App_t S_t _) _ = <atom>`` (same shape).
      APP  : the firing case.  ``App_t M N = App_t <atom> W`` gives
             ``M = <atom>``, ``N = W`` via APP_T_INJ; then the IH's
             par_step conjunct ``par_step M M1`` becomes ``par_step
             <atom> M1``, which ``atom_inv_thm`` collapses to ``M1 =
             <atom>``.  Witness ``Wp := N1``; ``App_t M1 N1 = App_t
             <atom> N1`` via AP_TERM + AP_THM.

    DSL friction (general):
    * SPEC at a 2-arg lambda Q creates beta redexes throughout the
      closures body and in the final ``Q (App_t <atom> X) Y``
      application; ``BETA_NORM`` is the only way to clean them in one
      shot.  ``by_def_at`` doesn't cover lambda-shaped P arguments.
    * The closure bvars in ``_PAR_STEP_CLOSURE`` (A Y A1 Y1 ...) clash
      with the outer ``Y``; we name the closure bvars freshly (M N P
      M1 N1 P1) and rely on alpha-conversion at the final CONJ.
    * ``by_conj`` is NOT sym-tolerant (unlike ``_simp_require``); each
      shape-clash branch SYMs the APP_T_INJ result before ``absurd``.

    DSL friction (firing-case specific):
    * Rewriting ``par_step M M1`` to ``par_step <atom> M1`` via
      ``M = <atom>`` works through ``by_rewrite_of`` -- the equation
      fires under both Comb layers.
    * Lifting ``M1 = <atom>`` to ``App_t M1 N1 = App_t <atom> N1``
      uses raw AP_TERM + AP_THM (one congruence step per kernel arg).
      ``by_cong(App_t, eq, refl)`` would also work; the explicit form
      is cheaper because we already have ``M1 = <atom>`` as a
      registered fact.
    """
    from tactics import (
        BETA_NORM,
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
        AP_TERM as _AP_TERM,
        AP_THM as _AP_THM,
    )

    p.goal(
        f"!X:nat0. !Y:nat0. "
        f"sk_par_step (App_t {atom_str} X) Y ==> "
        f"?XP:nat0. Y = App_t {atom_str} XP /\\ sk_par_step X XP"
    )
    p.fix("X Y")
    p.assume(f"h: sk_par_step (App_t {atom_str} X) Y")

    # Unfold sk_par_step at (App_t <atom> X, Y).
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF,
        p._parse(f"App_t {atom_str} X"),
        p._parse("Y"),
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))

    # SPEC at Q.  Two-arg lambda; BETA_NORM cleans the redexes.
    Q_tm = p._parse(
        f"\\A:nat0. \\B:nat0. "
        f"sk_par_step A B /\\ "
        f"(!W:nat0. A = App_t {atom_str} W ==> "
        f"  ?Wp:nat0. B = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    )
    h_at_Q_raw = SPEC(Q_tm, h_univ)
    h_at_Q = EQ_MP(BETA_NORM(h_at_Q_raw._concl), h_at_Q_raw)
    p.have(f"h_at_Q: {pp(h_at_Q._concl)}").by_thm(h_at_Q)

    # --- REFL closure --------------------------------------------------
    with p.have(
        f"c_refl: !Z:nat0. sk_par_step Z Z /\\ "
        f"(!W:nat0. Z = App_t {atom_str} W ==> "
        f" ?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("Z")
        p.have("h_par: sk_par_step Z Z").by(PAR_REFL, "Z")
        with p.have(
            f"h_inv: !W:nat0. Z = App_t {atom_str} W ==> "
            f"?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(f"h_eq: Z = App_t {atom_str} W")
            p.have("h_par_WW: sk_par_step W W").by(PAR_REFL, "W")
            p.thus(
                f"?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp"
            ).by_exists(["W"], "h_eq", "h_par_WW")
        p.thus(
            f"sk_par_step Z Z /\\ "
            f"(!W:nat0. Z = App_t {atom_str} W ==> "
            f" ?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par"), p.fact("h_inv")))

    # --- K-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_K: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t (App_t K_t M) N) M1 /\\ "
        f"(!W:nat0. App_t (App_t K_t M) N = App_t {atom_str} W ==> "
        f" ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_KMN_M1: sk_par_step (App_t (App_t K_t M) N) M1"
        ).by(PAR_K, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            f"h_inv_K: !W:nat0. "
            f"App_t (App_t K_t M) N = App_t {atom_str} W ==> "
            f"?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(
                f"h_eq: App_t (App_t K_t M) N = App_t {atom_str} W"
            )
            p.have(
                f"h_inj: App_t K_t M = {atom_str} /\\ N = W"
            ).by(APP_T_INJ, "App_t K_t M", "N", atom_str, "W", "h_eq")
            p.have(
                f"h_inj_L: App_t K_t M = {atom_str}"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                f"h_inj_L_sym: {atom_str} = App_t K_t M"
            ).by_thm(SYM(p.fact("h_inj_L")))
            p.have(
                f"h_neq: ~({atom_str} = App_t K_t M)"
            ).by(atom_neq_app_t, "K_t", "M")
            p.absurd().by_conj("h_neq", "h_inj_L_sym")
        p.thus(
            f"sk_par_step (App_t (App_t K_t M) N) M1 /\\ "
            f"(!W:nat0. App_t (App_t K_t M) N = App_t {atom_str} W ==> "
            f" ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_KMN_M1"), p.fact("h_inv_K")))

    # --- S-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_S: !M:nat0. !N:nat0. !P:nat0. !M1:nat0. !N1:nat0. !P1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step P P1 /\\ "
        f"  (!W:nat0. P = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. P1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t (App_t (App_t S_t M) N) P) "
        f"            (App_t (App_t M1 P1) (App_t N1 P1)) /\\ "
        f"(!W:nat0. "
        f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
        f" ?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
        f"            App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("M N P M1 N1 P1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N), (h_par_P, h_inv_P)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step P P1 /\\ "
            f"  (!W:nat0. P = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. P1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_3: sk_par_step M M1 /\\ sk_par_step N N1 /\\ "
            "          sk_par_step P P1"
        ).by_thm(_CONJ(
            p.fact("h_par_M"),
            _CONJ(p.fact("h_par_N"), p.fact("h_par_P")),
        ))
        p.have(
            "h_par_Sred: sk_par_step (App_t (App_t (App_t S_t M) N) P) "
            "            (App_t (App_t M1 P1) (App_t N1 P1))"
        ).by(PAR_S, "M", "M1", "N", "N1", "P", "P1", "h_conj_3")
        with p.have(
            f"h_inv_S: !W:nat0. "
            f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
            f"?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
            f"           App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(
                f"h_eq: App_t (App_t (App_t S_t M) N) P = "
                f"      App_t {atom_str} W"
            )
            p.have(
                f"h_inj: App_t (App_t S_t M) N = {atom_str} /\\ P = W"
            ).by(
                APP_T_INJ,
                "App_t (App_t S_t M) N", "P", atom_str, "W", "h_eq",
            )
            p.have(
                f"h_inj_L: App_t (App_t S_t M) N = {atom_str}"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                f"h_inj_L_sym: {atom_str} = App_t (App_t S_t M) N"
            ).by_thm(SYM(p.fact("h_inj_L")))
            p.have(
                f"h_neq: ~({atom_str} = App_t (App_t S_t M) N)"
            ).by(atom_neq_app_t, "App_t S_t M", "N")
            p.absurd().by_conj("h_neq", "h_inj_L_sym")
        p.thus(
            f"sk_par_step (App_t (App_t (App_t S_t M) N) P) "
            f"            (App_t (App_t M1 P1) (App_t N1 P1)) /\\ "
            f"(!W:nat0. "
            f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
            f" ?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
            f"            App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_Sred"), p.fact("h_inv_S")))

    # --- APP-rule closure (firing case) --------------------------------
    with p.have(
        f"c_APP: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t M N) (App_t M1 N1) /\\ "
        f"(!W:nat0. App_t M N = App_t {atom_str} W ==> "
        f" ?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
        f"            sk_par_step W Wp)"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_APP: sk_par_step (App_t M N) (App_t M1 N1)"
        ).by(PAR_APP, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            f"h_inv_APP: !W:nat0. App_t M N = App_t {atom_str} W ==> "
            f"?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
            f"           sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(f"h_eq: App_t M N = App_t {atom_str} W")
            p.have(
                f"h_inj: M = {atom_str} /\\ N = W"
            ).by(APP_T_INJ, "M", "N", atom_str, "W", "h_eq")
            p.have(f"h_M_eq: M = {atom_str}").by_thm(_C1(p.fact("h_inj")))
            p.have("h_N_eq: N = W").by_thm(_C2(p.fact("h_inj")))
            # par_step M M1 + M = <atom>  ==>  par_step <atom> M1.
            p.have(
                f"h_par_atom_M1: sk_par_step {atom_str} M1"
            ).by_rewrite_of("h_par_M", [p.fact("h_M_eq")])
            # atom inversion collapses M1 to <atom>.
            p.have(
                f"h_M1_eq: M1 = {atom_str}"
            ).by(atom_inv_thm, "M1", "h_par_atom_M1")
            # par_step N N1 + N = W  ==>  par_step W N1.
            p.have(
                "h_par_W_N1: sk_par_step W N1"
            ).by_rewrite_of("h_par_N", [p.fact("h_N_eq")])
            # App_t M1 N1 = App_t <atom> N1 via AP_TERM + AP_THM.
            ap1 = _AP_TERM(App_t, p.fact("h_M1_eq"))
            ap2 = _AP_THM(ap1, p._parse("N1"))
            p.have(
                f"h_app_eq: App_t M1 N1 = App_t {atom_str} N1"
            ).by_thm(ap2)
            p.thus(
                f"?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
                f"           sk_par_step W Wp"
            ).by_exists(["N1"], "h_app_eq", "h_par_W_N1")
        p.thus(
            f"sk_par_step (App_t M N) (App_t M1 N1) /\\ "
            f"(!W:nat0. App_t M N = App_t {atom_str} W ==> "
            f" ?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
            f"            sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_APP"), p.fact("h_inv_APP")))

    # --- Compose closures, MP, project, conclude -----------------------
    cl_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    p.have(f"h_cl: {pp(cl_th._concl)}").by_thm(cl_th)
    p.have(
        f"h_Q: sk_par_step (App_t {atom_str} X) Y /\\ "
        f"(!W:nat0. App_t {atom_str} X = App_t {atom_str} W ==> "
        f" ?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).by("h_at_Q", "h_cl")

    # Extract the inversion conjunct, SPEC at X, MP at the trivial REFL.
    p.split("h_Q", "(_, h_inv_Q)")
    p.have(
        f"h_inv_X: App_t {atom_str} X = App_t {atom_str} X ==> "
        f"?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step X Wp"
    ).by("h_inv_Q", "X")
    p.have(
        f"h_refl: App_t {atom_str} X = App_t {atom_str} X"
    ).by_thm(REFL(p._parse(f"App_t {atom_str} X")))
    p.have(
        f"h_ex: ?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step X Wp"
    ).by("h_inv_X", "h_refl")
    p.choose("XP", from_="h_ex")
    p.split("XP_eq", "(h_Y_eq, h_par_X_XP)")
    p.thus(
        f"?XP:nat0. Y = App_t {atom_str} XP /\\ sk_par_step X XP"
    ).by_exists(["XP"], "h_Y_eq", "h_par_X_XP")


@proof
def PAR_STEP_K_APP_INV(p):
    """|- !X Y. sk_par_step (App_t K_t X) Y ==>
                  ?XP. Y = App_t K_t XP /\\ sk_par_step X XP.

    App-shape par_step inversion at the K_t head: any par-reduct of
    ``App_t K_t X`` must itself be ``App_t K_t XP`` where ``X`` par-
    reduces to ``XP``.  Since ``App_t K_t X`` is not a redex (only 1
    App layer; K-redex requires 2, S-redex 3), par_step can only fire
    via REFL or APP-rule; the APP-rule head ``K_t`` then collapses
    back to ``K_t`` via PAR_STEP_K_T_INV.

    Delegated to ``_par_step_app_atom_inv`` with atom = K_t.
    """
    _par_step_app_atom_inv(
        p, "K_t", PAR_STEP_K_T_INV, K_T_NEQ_APP_T
    )


@proof
def PAR_STEP_S_T_APP_INV(p):
    """|- !X Y. sk_par_step (App_t S_t X) Y ==>
                  ?XP. Y = App_t S_t XP /\\ sk_par_step X XP.

    Sister of PAR_STEP_K_APP_INV at the S_t head -- the inner inversion
    needed by PAR_STEP_S_APP_APP_INV's APP-rule firing case (where the
    par-step head ``App_t S_t X`` must be inverted before the S-shape
    survival argument can fire).

    Delegated to ``_par_step_app_atom_inv`` with atom = S_t.
    """
    _par_step_app_atom_inv(
        p, "S_t", PAR_STEP_S_T_INV, S_T_NEQ_APP_T
    )


@proof
def PAR_STEP_S_APP_APP_INV(p):
    """|- !X Y Z. sk_par_step (App_t (App_t S_t X) Y) Z ==>
                  ?XP YP. Z = App_t (App_t S_t XP) YP /\\
                          sk_par_step X XP /\\ sk_par_step Y YP.

    Two-App-deep par_step inversion at the S_t head.  ``App_t (App_t
    S_t X) Y`` has 2 App layers; S-redex needs 3 and K-redex needs 2
    with K_t (not S_t) at depth-1, so neither fires.  Only REFL and
    APP-rule.  The APP-rule case recursively inverts the head
    ``App_t S_t X`` via PAR_STEP_S_T_APP_INV.

    Strategy: instantiate the impredicative ``P`` with
        Q := \\A B. sk_par_step A B /\\
                     (!W1 W2. A = App_t (App_t S_t W1) W2 ==>
                          ?W1p W2p. B = App_t (App_t S_t W1p) W2p
                                       /\\ sk_par_step W1 W1p
                                       /\\ sk_par_step W2 W2p)

    Closures: REFL trivial; K/S vacuous via 1-2 layer APP_T_INJ
    descent ending in S_t vs K_t / S_t vs App_t clash; APP fires using
    PAR_STEP_S_T_APP_INV on the depth-1 head par-step.

    DSL friction: the inversion existentials are now binary (W1p,
    W2p) so ``by_exists`` takes two witnesses; ``h_inv_Q`` after
    extraction is also two-arg (``!W1 W2. ...``), so SPECL via the
    DSL needs sequential ``by(... "X", "Y", ...)``.
    """
    from tactics import (
        BETA_NORM,
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
        AP_TERM as _AP_TERM,
        AP_THM as _AP_THM,
    )

    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step (App_t (App_t S_t X) Y) Z ==> "
        "?XP:nat0. ?YP:nat0. "
        "Z = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step X XP /\\ sk_par_step Y YP"
    )
    p.fix("X Y Z")
    p.assume("h: sk_par_step (App_t (App_t S_t X) Y) Z")

    # Unfold sk_par_step at the input.
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF,
        p._parse("App_t (App_t S_t X) Y"),
        p._parse("Z"),
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))

    # SPEC at the binary-inversion Q.
    Q_tm = p._parse(
        "\\A:nat0. \\B:nat0. "
        "sk_par_step A B /\\ "
        "(!W1:nat0. !W2:nat0. A = App_t (App_t S_t W1) W2 ==> "
        " ?W1p:nat0. ?W2p:nat0. "
        " B = App_t (App_t S_t W1p) W2p /\\ "
        " sk_par_step W1 W1p /\\ sk_par_step W2 W2p)"
    )
    h_at_Q_raw = SPEC(Q_tm, h_univ)
    h_at_Q = EQ_MP(BETA_NORM(h_at_Q_raw._concl), h_at_Q_raw)
    p.have(f"h_at_Q: {pp(h_at_Q._concl)}").by_thm(h_at_Q)

    # Q body, parameterized over (A, B), as a reusable string.
    def _q_body(A_str, B_str):
        return (
            f"sk_par_step {A_str} {B_str} /\\ "
            f"(!W1:nat0. !W2:nat0. {A_str} = App_t (App_t S_t W1) W2 ==> "
            f" ?W1p:nat0. ?W2p:nat0. "
            f" {B_str} = App_t (App_t S_t W1p) W2p /\\ "
            f" sk_par_step W1 W1p /\\ sk_par_step W2 W2p)"
        )

    # --- REFL closure --------------------------------------------------
    with p.have(f"c_refl: !Zc:nat0. {_q_body('Zc', 'Zc')}").proof():
        p.fix("Zc")
        p.have("h_par: sk_par_step Zc Zc").by(PAR_REFL, "Zc")
        with p.have(
            "h_inv: !W1:nat0. !W2:nat0. Zc = App_t (App_t S_t W1) W2 "
            "==> ?W1p:nat0. ?W2p:nat0. "
            "    Zc = App_t (App_t S_t W1p) W2p /\\ "
            "    sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume("h_eq: Zc = App_t (App_t S_t W1) W2")
            p.have("h_par_W1: sk_par_step W1 W1").by(PAR_REFL, "W1")
            p.have("h_par_W2: sk_par_step W2 W2").by(PAR_REFL, "W2")
            p.thus(
                "?W1p:nat0. ?W2p:nat0. "
                "Zc = App_t (App_t S_t W1p) W2p /\\ "
                "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
            ).by_exists(
                ["W1", "W2"], "h_eq", "h_par_W1", "h_par_W2"
            )
        p.thus(f"{_q_body('Zc', 'Zc')}").by_thm(
            _CONJ(p.fact("h_par"), p.fact("h_inv"))
        )

    # --- K-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_K: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) ==> "
        f"{_q_body('(App_t (App_t K_t M) N)', 'M1')}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')})"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_KMN: sk_par_step (App_t (App_t K_t M) N) M1"
        ).by(PAR_K, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            "h_inv_K: !W1:nat0. !W2:nat0. "
            "App_t (App_t K_t M) N = App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "M1 = App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume(
                "h_eq: App_t (App_t K_t M) N = App_t (App_t S_t W1) W2"
            )
            # Outer APP_T_INJ: App_t K_t M = App_t S_t W1 /\ N = W2.
            p.have(
                "h_inj1: App_t K_t M = App_t S_t W1 /\\ N = W2"
            ).by(
                APP_T_INJ,
                "App_t K_t M", "N", "App_t S_t W1", "W2", "h_eq",
            )
            p.have(
                "h_inj1_L: App_t K_t M = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj1")))
            # Inner APP_T_INJ: K_t = S_t.
            p.have(
                "h_inj2: K_t = S_t /\\ M = W1"
            ).by(APP_T_INJ, "K_t", "M", "S_t", "W1", "h_inj1_L")
            p.have("h_K_eq_S: K_t = S_t").by_thm(_C1(p.fact("h_inj2")))
            p.have("h_S_eq_K: S_t = K_t").by_thm(SYM(p.fact("h_K_eq_S")))
            p.absurd().by_conj(S_T_NEQ_K_T, "h_S_eq_K")
        p.thus(
            f"{_q_body('(App_t (App_t K_t M) N)', 'M1')}"
        ).by_thm(_CONJ(p.fact("h_par_KMN"), p.fact("h_inv_K")))

    # --- S-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_S: !M:nat0. !N:nat0. !P:nat0. !M1:nat0. !N1:nat0. !P1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) /\\ "
        f"({_q_body('P', 'P1')}) ==> "
        f"{_q_body('(App_t (App_t (App_t S_t M) N) P)', '(App_t (App_t M1 P1) (App_t N1 P1))')}"
    ).proof():
        p.fix("M N P M1 N1 P1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N), (h_par_P, h_inv_P)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) /\\ "
            f"({_q_body('P', 'P1')})"
        )
        p.have(
            "h_conj_3: sk_par_step M M1 /\\ sk_par_step N N1 /\\ "
            "          sk_par_step P P1"
        ).by_thm(_CONJ(
            p.fact("h_par_M"),
            _CONJ(p.fact("h_par_N"), p.fact("h_par_P")),
        ))
        p.have(
            "h_par_Sred: sk_par_step "
            "  (App_t (App_t (App_t S_t M) N) P) "
            "  (App_t (App_t M1 P1) (App_t N1 P1))"
        ).by(PAR_S, "M", "M1", "N", "N1", "P", "P1", "h_conj_3")
        with p.have(
            "h_inv_S: !W1:nat0. !W2:nat0. "
            "App_t (App_t (App_t S_t M) N) P = "
            "  App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "App_t (App_t M1 P1) (App_t N1 P1) = "
            "  App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume(
                "h_eq: App_t (App_t (App_t S_t M) N) P = "
                "      App_t (App_t S_t W1) W2"
            )
            # Outer APP_T_INJ: App_t (App_t S_t M) N = App_t S_t W1.
            p.have(
                "h_inj1: App_t (App_t S_t M) N = App_t S_t W1 /\\ P = W2"
            ).by(
                APP_T_INJ,
                "App_t (App_t S_t M) N", "P",
                "App_t S_t W1", "W2", "h_eq",
            )
            p.have(
                "h_inj1_L: App_t (App_t S_t M) N = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj1")))
            # Inner APP_T_INJ: App_t S_t M = S_t.  App vs leaf.
            p.have(
                "h_inj2: App_t S_t M = S_t /\\ N = W1"
            ).by(
                APP_T_INJ, "App_t S_t M", "N", "S_t", "W1", "h_inj1_L"
            )
            p.have(
                "h_inj2_L: App_t S_t M = S_t"
            ).by_thm(_C1(p.fact("h_inj2")))
            p.have(
                "h_inj2_L_sym: S_t = App_t S_t M"
            ).by_thm(SYM(p.fact("h_inj2_L")))
            p.have("h_neq: ~(S_t = App_t S_t M)").by(
                S_T_NEQ_APP_T, "S_t", "M"
            )
            p.absurd().by_conj("h_neq", "h_inj2_L_sym")
        p.thus(
            f"{_q_body('(App_t (App_t (App_t S_t M) N) P)', '(App_t (App_t M1 P1) (App_t N1 P1))')}"
        ).by_thm(_CONJ(p.fact("h_par_Sred"), p.fact("h_inv_S")))

    # --- APP-rule closure (firing case) --------------------------------
    with p.have(
        f"c_APP: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) ==> "
        f"{_q_body('(App_t M N)', '(App_t M1 N1)')}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')})"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_APP: sk_par_step (App_t M N) (App_t M1 N1)"
        ).by(PAR_APP, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            "h_inv_APP: !W1:nat0. !W2:nat0. "
            "App_t M N = App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "App_t M1 N1 = App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume("h_eq: App_t M N = App_t (App_t S_t W1) W2")
            p.have(
                "h_inj: M = App_t S_t W1 /\\ N = W2"
            ).by(APP_T_INJ, "M", "N", "App_t S_t W1", "W2", "h_eq")
            p.have(
                "h_M_eq: M = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have("h_N_eq: N = W2").by_thm(_C2(p.fact("h_inj")))
            # par_step M M1 + M = App_t S_t W1 ==> par_step (App_t S_t W1) M1.
            p.have(
                "h_par_SW1_M1: sk_par_step (App_t S_t W1) M1"
            ).by_rewrite_of("h_par_M", [p.fact("h_M_eq")])
            # Recursive App-atom inversion at the S_t head.
            p.have(
                "h_M1_shape: ?XP:nat0. "
                "M1 = App_t S_t XP /\\ sk_par_step W1 XP"
            ).by(
                PAR_STEP_S_T_APP_INV, "W1", "M1", "h_par_SW1_M1"
            )
            p.choose("M1_inner", from_="h_M1_shape")
            p.split("M1_inner_eq", "(h_M1_eq, h_par_W1_inner)")
            # par_step N N1 + N = W2  ==>  par_step W2 N1.
            p.have(
                "h_par_W2_N1: sk_par_step W2 N1"
            ).by_rewrite_of("h_par_N", [p.fact("h_N_eq")])
            # App_t M1 N1 = App_t (App_t S_t M1_inner) N1 via congruence.
            ap1 = _AP_TERM(App_t, p.fact("h_M1_eq"))
            ap2 = _AP_THM(ap1, p._parse("N1"))
            p.have(
                "h_app_eq: App_t M1 N1 = App_t (App_t S_t M1_inner) N1"
            ).by_thm(ap2)
            p.thus(
                "?W1p:nat0. ?W2p:nat0. "
                "App_t M1 N1 = App_t (App_t S_t W1p) W2p /\\ "
                "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
            ).by_exists(
                ["M1_inner", "N1"],
                "h_app_eq", "h_par_W1_inner", "h_par_W2_N1",
            )
        p.thus(
            f"{_q_body('(App_t M N)', '(App_t M1 N1)')}"
        ).by_thm(_CONJ(p.fact("h_par_APP"), p.fact("h_inv_APP")))

    # --- Compose closures, MP, project, conclude -----------------------
    cl_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    p.have(f"h_cl: {pp(cl_th._concl)}").by_thm(cl_th)
    p.have(
        f"h_Q: {_q_body('(App_t (App_t S_t X) Y)', 'Z')}"
    ).by("h_at_Q", "h_cl")

    p.split("h_Q", "(_, h_inv_Q)")
    p.have(
        "h_inv_XY: App_t (App_t S_t X) Y = App_t (App_t S_t X) Y ==> "
        "?W1p:nat0. ?W2p:nat0. "
        "Z = App_t (App_t S_t W1p) W2p /\\ "
        "sk_par_step X W1p /\\ sk_par_step Y W2p"
    ).by("h_inv_Q", "X", "Y")
    p.have(
        "h_refl: App_t (App_t S_t X) Y = App_t (App_t S_t X) Y"
    ).by_thm(REFL(p._parse("App_t (App_t S_t X) Y")))
    p.have(
        "h_ex: ?W1p:nat0. ?W2p:nat0. "
        "Z = App_t (App_t S_t W1p) W2p /\\ "
        "sk_par_step X W1p /\\ sk_par_step Y W2p"
    ).by("h_inv_XY", "h_refl")
    p.choose("XP", from_="h_ex")
    p.choose("YP", from_="XP_eq")
    p.split("YP_eq", "(h_Z_eq, h_par_X_XP, h_par_Y_YP)")
    p.thus(
        "?XP:nat0. ?YP:nat0. "
        "Z = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step X XP /\\ sk_par_step Y YP"
    ).by_exists(
        ["XP", "YP"], "h_Z_eq", "h_par_X_XP", "h_par_Y_YP"
    )


def _bullet_refl_app_case(p):
    """BULLET_REFL's App-but-not-K/S sub-case.

    Closes ``sk_par_step A (sk_bullet A)`` from:
      * ``a_eq``: ``?b. A = App_t a b`` (auto-bound by outer ``cases_on``)
      * ``h_nK``, ``h_nS``: A is neither K- nor S-redex
      * ``IH``:  the strong-induction hypothesis on ``A``

    PAR_APP combines IH at (a, b); SK_BULLET_APP_OTHER unfolds
    ``sk_bullet (App_t a b)`` to ``App_t (sk_bullet a) (sk_bullet b)``.
    Mirrors _par_step_app_case (halting.py:7185).
    """
    from tactics import CONJ as _CONJ, BETA_RULE

    # 'a' auto-introduced by cases_on; manually choose b.
    p.choose("b", from_="a_eq")
    # b_eq : A = App_t a b.
    # Lift the non-redex hypotheses from A to App_t a b via AP_TERM at
    # the negation-shape predicate, then BETA_RULE, then EQ_MP.
    P_K = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. x = App_t (App_t K_t u) v)"
    )
    h_nK_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_K, p.fact("b_eq"))),
        p.fact("h_nK"),
    )
    p.have(
        "h_nK_ab: ~(?u v. App_t a b = App_t (App_t K_t u) v)"
    ).by_thm(h_nK_ab_thm)
    P_S = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. ?w:nat0. "
        "          x = App_t (App_t (App_t S_t u) v) w)"
    )
    h_nS_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_S, p.fact("b_eq"))),
        p.fact("h_nS"),
    )
    p.have(
        "h_nS_ab: ~(?u v w. App_t a b = "
        "         App_t (App_t (App_t S_t u) v) w)"
    ).by_thm(h_nS_ab_thm)
    # IH at a, b -- both strictly smaller via NAT0_LT_APP_T_L/R.
    p.have(
        "h_lt_a_AB: nat0_lt a (App_t a b)"
    ).by(NAT0_LT_APP_T_L, "a", "b")
    p.have(
        "h_lt_b_AB: nat0_lt b (App_t a b)"
    ).by(NAT0_LT_APP_T_R, "a", "b")
    p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
        "h_lt_a_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
        "h_lt_b_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_ih_a: sk_par_step a (sk_bullet a)").by(
        "IH", "a", "h_lt_a"
    )
    p.have("h_ih_b: sk_par_step b (sk_bullet b)").by(
        "IH", "b", "h_lt_b"
    )
    # PAR_APP combines the two IHs.
    p.have(
        "h_par_AB: sk_par_step (App_t a b) "
        "                     (App_t (sk_bullet a) (sk_bullet b))"
    ).by(
        PAR_APP, "a", "sk_bullet a", "b", "sk_bullet b",
        _CONJ(p.fact("h_ih_a"), p.fact("h_ih_b")),
    )
    # SK_BULLET_APP_OTHER under the lifted non-redex guards.
    p.have(
        "h_nKnS_ab: "
        "~(?u v. App_t a b = App_t (App_t K_t u) v) /\\ "
        "~(?u v w. App_t a b = "
        "          App_t (App_t (App_t S_t u) v) w)"
    ).by_thm(_CONJ(p.fact("h_nK_ab"), p.fact("h_nS_ab")))
    p.have(
        "h_bullet_AB: sk_bullet (App_t a b) = "
        "             App_t (sk_bullet a) (sk_bullet b)"
    ).by(SK_BULLET_APP_OTHER, "a", "b", "h_nKnS_ab")
    p.have(
        "h_bullet_A: sk_bullet A = "
        "            App_t (sk_bullet a) (sk_bullet b)"
    ).by_rewrite_of("h_bullet_AB", [SYM(p.fact("b_eq"))])
    # Fold App_t a b back to A on the LHS slot, then sk_bullet a b's
    # RHS-form back to sk_bullet A.
    p.have(
        "h_par_A_bull: sk_par_step A "
        "             (App_t (sk_bullet a) (sk_bullet b))"
    ).by_rewrite_of("h_par_AB", [SYM(p.fact("b_eq"))])
    p.thus("sk_par_step A (sk_bullet A)").by_rewrite_of(
        "h_par_A_bull", [SYM(p.fact("h_bullet_A"))]
    )


def _bullet_refl_leaf_case(p):
    """BULLET_REFL's non-App leaf sub-case.

    Builds the D4 inner branch from h_nK / h_nS / h_nApp, lifts it via
    ``_sk_bullet_select_at`` to ``body[A, sk_bullet A]``, case-splits;
    D1/D2/D3 are App-shaped existentials refuted by the three non-shape
    hypotheses, D4 yields ``sk_bullet A = A`` which PAR_REFL closes.
    Mirrors _par_step_leaf_case (halting.py:7323).
    """
    from tactics import CONJ as _CONJ

    p.have(
        "inner_leaf: "
        "~(?a b. A = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. A = App_t (App_t (App_t S_t a) b) c) /\\ "
        "~(?a b. A = App_t a b) /\\ A = A"
    ).by_thm(
        _CONJ(
            p.fact("h_nK"),
            _CONJ(
                p.fact("h_nS"),
                _CONJ(p.fact("h_nApp"), REFL(p._parse("A"))),
            ),
        )
    )
    body_th = _sk_bullet_select_at(p, "A", "A", "inner_leaf")
    p.have(
        f"body: {_sk_bullet_body('A', 'sk_bullet A')}"
    ).by_thm(body_th)
    D1, D2, D3, D4 = _sk_bullet_disjuncts("A", "sk_bullet A")
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # Auto-bound 'a' from the outer ?a; manually choose b.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_kred_ex: ?a b. A = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], "h_app")
            p.absurd().by_conj("h_nK", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                "h_sred_ex: ?a b c. A = "
                "           App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], "h_app")
            p.absurd().by_conj("h_nS", "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_app)")
            p.choose("a", from_="h3_app")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_app_ex: ?a b. A = App_t a b"
            ).by_exists(["a", "b"], "h_app")
            p.absurd().by_conj("h_nApp", "h_app_ex")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, _, h_bull)")
            # h_bull : sk_bullet A = A.  SYM as a rewrite rule
            # (A -> sk_bullet A) would loop; lift via AP_TERM at the
            # RHS slot of ``sk_par_step A _`` instead.  DSL friction:
            # by_rewrite_of refuses non-terminating rules silently and
            # ``sk_par_step A A`` doesn't simp-match the goal, so the
            # explicit AP_TERM lift is the cleanest route here.
            p.have("h_refl: sk_par_step A A").by(PAR_REFL, "A")
            p.thus("sk_par_step A (sk_bullet A)").by_thm(
                EQ_MP(
                    AP_TERM(
                        p._parse("sk_par_step A"),
                        SYM(p.fact("h_bull")),
                    ),
                    p.fact("h_refl"),
                )
            )


@proof
def BULLET_REFL(p):
    """|- !A. sk_par_step A (sk_bullet A).

    Every term parallel-reduces (in one parallel step) to its complete
    development.  Despite the name this is NOT par_step's REFL rule:
    ``sk_bullet`` contracts every redex it sees, so the proof actually
    fires PAR_K / PAR_S / PAR_APP at the redex / non-redex App cases.

    Strong induction on ``A`` over ``nat0_lt`` with a 4-way LEM split
    on A's shape -- exact mirror of SK_PAR_STEP_TO_SK_STEP
    (halting.py:7395), substituting bullet's collapsing semantics:

      * K-redex (A = App K a b)         : sk_bullet A = sk_bullet a;
                                          PAR_K with IH at a, b.
      * S-redex (A = App (App S a) b c) : SK_BULLET_S_REDEX;
                                          PAR_S with IH at a, b, c.
      * generic App (~K, ~S)            : SK_BULLET_APP_OTHER;
                                          PAR_APP with IH at a, b.
      * leaf (~K, ~S, ~App)             : sk_bullet A = A via D4;
                                          PAR_REFL.

    Subterm-smaller-than-A facts go via NAT0_LT_APP_T_L/R (single hop
    in the App-other case) or NAT0_LT_TRANS chains (1 hop for the
    K-redex inner ``a``; 2-3 hops for the S-redex's a, b through
    nested App-spines).
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ

    p.goal("!A:nat0. sk_par_step A (sk_bullet A)")
    with p.strong_induction("A", "IH"):
        # IH : !k. nat0_lt k A ==> sk_par_step k (sk_bullet k).
        # ---- LEM split: is A a K-redex? ---------------------------------
        with p.cases_on(
            EXCLUDED_MIDDLE,
            "?a b. A = App_t (App_t K_t a) b",
        ):
            with p.case("h_K: ?a b. A = App_t (App_t K_t a) b"):
                # cases_on auto-introduces 'a' (outer ? bvar); we
                # manually peel the inner ?b.  DSL friction: leaf is
                # ``?a b. ...`` but auto-introduce only peels the
                # outermost ?, so the second p.choose remains explicit.
                p.choose("b", from_="a_eq")
                # b_eq : A = App_t (App_t K_t a) b.

                # nat0_lt a A: two-hop a < App K a < App (App K a) b.
                p.have(
                    "h_lt_a_Ka: nat0_lt a (App_t K_t a)"
                ).by(NAT0_LT_APP_T_R, "K_t", "a")
                p.have(
                    "h_lt_Ka_KAB: nat0_lt (App_t K_t a) "
                    "                     (App_t (App_t K_t a) b)"
                ).by(NAT0_LT_APP_T_L, "App_t K_t a", "b")
                p.have(
                    "h_lt_a_KAB: "
                    "nat0_lt a (App_t (App_t K_t a) b)"
                ).by(
                    NAT0_LT_TRANS,
                    "a", "App_t K_t a", "App_t (App_t K_t a) b",
                    "h_lt_a_Ka", "h_lt_Ka_KAB",
                )
                p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
                    "h_lt_a_KAB", [SYM(p.fact("b_eq"))]
                )
                # nat0_lt b A: direct from App_t-right.
                p.have(
                    "h_lt_b_KAB: "
                    "nat0_lt b (App_t (App_t K_t a) b)"
                ).by(NAT0_LT_APP_T_R, "App_t K_t a", "b")
                p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
                    "h_lt_b_KAB", [SYM(p.fact("b_eq"))]
                )

                p.have(
                    "h_ih_a: sk_par_step a (sk_bullet a)"
                ).by("IH", "a", "h_lt_a")
                p.have(
                    "h_ih_b: sk_par_step b (sk_bullet b)"
                ).by("IH", "b", "h_lt_b")
                # PAR_K with X1 := sk_bullet a, Y1 := sk_bullet b.
                p.have(
                    "h_par_KAB: "
                    "sk_par_step (App_t (App_t K_t a) b) (sk_bullet a)"
                ).by(
                    PAR_K, "a", "sk_bullet a", "b", "sk_bullet b",
                    _CONJ(p.fact("h_ih_a"), p.fact("h_ih_b")),
                )
                # Bullet collapses the K-redex.
                p.have(
                    "h_bullet_KAB: sk_bullet (App_t (App_t K_t a) b) "
                    "              = sk_bullet a"
                ).by(SK_BULLET_K_REDEX, "a", "b")
                p.have(
                    "h_bullet_A: sk_bullet A = sk_bullet a"
                ).by_rewrite_of(
                    "h_bullet_KAB", [SYM(p.fact("b_eq"))]
                )
                # Fold the K-redex back to A in the par-step, then
                # ``sk_bullet a`` back to ``sk_bullet A`` on the RHS.
                p.have(
                    "h_par_A_bull_a: sk_par_step A (sk_bullet a)"
                ).by_rewrite_of("h_par_KAB", [SYM(p.fact("b_eq"))])
                p.thus("sk_par_step A (sk_bullet A)").by_rewrite_of(
                    "h_par_A_bull_a", [SYM(p.fact("h_bullet_A"))]
                )
            with p.case("h_nK: ~(?a b. A = App_t (App_t K_t a) b)"):
                # ---- LEM split: is A an S-redex? --------------------
                with p.cases_on(
                    EXCLUDED_MIDDLE,
                    "?a b c. A = App_t (App_t (App_t S_t a) b) c",
                ):
                    with p.case(
                        "h_S: ?a b c. A = "
                        "     App_t (App_t (App_t S_t a) b) c"
                    ):
                        # 'a' auto-introduced; manually choose b, c.
                        p.choose("b", from_="a_eq")
                        p.choose("c", from_="b_eq")
                        # c_eq : A = App_t (App_t (App_t S_t a) b) c.

                        # nat0_lt c A: one hop.
                        p.have(
                            "h_lt_c_SABC: nat0_lt c "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_APP_T_R,
                            "App_t (App_t S_t a) b", "c",
                        )
                        p.have("h_lt_c: nat0_lt c A").by_rewrite_of(
                            "h_lt_c_SABC", [SYM(p.fact("c_eq"))]
                        )
                        # nat0_lt b A: two hops via App (App S a) b.
                        p.have(
                            "h_lt_b_SAb: "
                            "nat0_lt b (App_t (App_t S_t a) b)"
                        ).by(NAT0_LT_APP_T_R, "App_t S_t a", "b")
                        p.have(
                            "h_lt_SAb_SABC: "
                            "nat0_lt (App_t (App_t S_t a) b) "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_APP_T_L,
                            "App_t (App_t S_t a) b", "c",
                        )
                        p.have(
                            "h_lt_b_SABC: "
                            "nat0_lt b "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_TRANS,
                            "b", "App_t (App_t S_t a) b",
                            "App_t (App_t (App_t S_t a) b) c",
                            "h_lt_b_SAb", "h_lt_SAb_SABC",
                        )
                        p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
                            "h_lt_b_SABC", [SYM(p.fact("c_eq"))]
                        )
                        # nat0_lt a A: three hops via App S a, App (App S a) b.
                        p.have(
                            "h_lt_a_Sa: nat0_lt a (App_t S_t a)"
                        ).by(NAT0_LT_APP_T_R, "S_t", "a")
                        p.have(
                            "h_lt_Sa_SAb: "
                            "nat0_lt (App_t S_t a) "
                            "(App_t (App_t S_t a) b)"
                        ).by(NAT0_LT_APP_T_L, "App_t S_t a", "b")
                        p.have(
                            "h_lt_a_SAb: "
                            "nat0_lt a (App_t (App_t S_t a) b)"
                        ).by(
                            NAT0_LT_TRANS,
                            "a", "App_t S_t a",
                            "App_t (App_t S_t a) b",
                            "h_lt_a_Sa", "h_lt_Sa_SAb",
                        )
                        p.have(
                            "h_lt_a_SABC: "
                            "nat0_lt a "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_TRANS,
                            "a", "App_t (App_t S_t a) b",
                            "App_t (App_t (App_t S_t a) b) c",
                            "h_lt_a_SAb", "h_lt_SAb_SABC",
                        )
                        p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
                            "h_lt_a_SABC", [SYM(p.fact("c_eq"))]
                        )

                        p.have(
                            "h_ih_a: sk_par_step a (sk_bullet a)"
                        ).by("IH", "a", "h_lt_a")
                        p.have(
                            "h_ih_b: sk_par_step b (sk_bullet b)"
                        ).by("IH", "b", "h_lt_b")
                        p.have(
                            "h_ih_c: sk_par_step c (sk_bullet c)"
                        ).by("IH", "c", "h_lt_c")
                        # PAR_S aligned with SK_BULLET_S_REDEX's RHS:
                        # X1 := sk_bullet a, Y1 := sk_bullet b,
                        # Z1 := sk_bullet c.
                        p.have(
                            "h_par_SABC: "
                            "sk_par_step "
                            "(App_t (App_t (App_t S_t a) b) c) "
                            "(App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c)))"
                        ).by(
                            PAR_S,
                            "a", "sk_bullet a", "b", "sk_bullet b",
                            "c", "sk_bullet c",
                            _CONJ(
                                p.fact("h_ih_a"),
                                _CONJ(
                                    p.fact("h_ih_b"),
                                    p.fact("h_ih_c"),
                                ),
                            ),
                        )
                        p.have(
                            "h_bullet_SABC: "
                            "sk_bullet "
                            "(App_t (App_t (App_t S_t a) b) c) = "
                            "App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c))"
                        ).by(SK_BULLET_S_REDEX, "a", "b", "c")
                        p.have(
                            "h_bullet_A: sk_bullet A = "
                            "App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c))"
                        ).by_rewrite_of(
                            "h_bullet_SABC", [SYM(p.fact("c_eq"))]
                        )
                        p.have(
                            "h_par_A_bull: "
                            "sk_par_step A "
                            "(App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c)))"
                        ).by_rewrite_of(
                            "h_par_SABC", [SYM(p.fact("c_eq"))]
                        )
                        p.thus(
                            "sk_par_step A (sk_bullet A)"
                        ).by_rewrite_of(
                            "h_par_A_bull",
                            [SYM(p.fact("h_bullet_A"))],
                        )
                    with p.case(
                        "h_nS: ~(?a b c. A = "
                        "       App_t (App_t (App_t S_t a) b) c)"
                    ):
                        # ---- LEM split: is A an App at all? --------
                        with p.cases_on(
                            EXCLUDED_MIDDLE, "?a b. A = App_t a b"
                        ):
                            with p.case(
                                "h_App: ?a b. A = App_t a b"
                            ):
                                _bullet_refl_app_case(p)
                            with p.case(
                                "h_nApp: ~(?a b. A = App_t a b)"
                            ):
                                _bullet_refl_leaf_case(p)


@proof
def _TRIANGLE_APP_CLOSURE(p):
    """The APP-rule closure conjunct of TRIANGLE's P-instantiation:

    |- !A B A1 B1.
         (sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\
         (sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==>
         sk_par_step (App_t A B) (App_t A1 B1) /\\
         sk_par_step (App_t A1 B1) (sk_bullet (App_t A B)).

    *** SORRY STUB.  Hardest of the four closure conjuncts:
    case-split on ``App_t A B`` shape:
      * K-redex (A = App_t K_t A'): invert ``sk_par_step A A1`` via
        PAR_STEP_K_APP_INV to get A1 = App_t K_t A1'; ``sk_bullet``
        of the K-redex collapses to ``sk_bullet A'``; assemble via
        PAR_K on (A1' par-step to sk_bullet A', B1 par-step to anything).
      * S-redex (A = App_t (App_t S_t A') B'): PAR_STEP_S_APP_APP_INV
        gives A1 = App_t (App_t S_t A1') B1''; ``sk_bullet`` collapses
        via SK_BULLET_S_REDEX; assemble via PAR_S.
      * otherwise: SK_BULLET_APP_OTHER + PAR_APP on the two IHs'
        second conjuncts.
    ~150 LOC.
    """
    p.goal(
        "!A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==> "
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    )
    p.sorry()


@proof
def SK_BULLET_TRIANGLE(p):
    """|- !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A).

    Takahashi's triangle property.  Proven via impredicative
    P-instantiation with the strengthened invariant:

       P := \\AA BB. sk_par_step AA BB /\\ sk_par_step BB (sk_bullet AA).

    The strengthening (first conjunct preserves the underlying par_step)
    is required by the APP-rule case: to invert source-side redex
    shapes via PAR_STEP_K_APP_INV / PAR_STEP_S_APP_APP_INV, we need
    direct access to ``sk_par_step A A1`` not just the P-version
    ``sk_par_step A1 (sk_bullet A)``.

    Four closure conjuncts:
      REFL Z   -- PAR_REFL + BULLET_REFL.
      K-rule   -- PAR_K (first part) + SK_BULLET_K_REDEX rewrite (second).
      S-rule   -- PAR_S + SK_BULLET_S_REDEX + double PAR_APP composition.
      APP-rule -- delegated to ``_TRIANGLE_APP_CLOSURE`` (sorry stub).

    With closures(P) built, SPEC h_AB-unfolded at P, MP, CONJUNCT2.

    DSL friction noted inline at three sites.
    """
    from tactics import (
        AP_THM, BETA_CONV, BETA_NORM, TRANS, SPEC, MP, CONJ,
        CONJUNCT2, EQ_MP,
    )

    p.goal(
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (sk_bullet A)"
    )
    p.fix("A B")
    p.assume("h_AB: sk_par_step A B")

    A_t = p._parse("A")
    B_t = p._parse("B")
    h_AB_th = p.fact("h_AB")

    # Unfold sk_par_step A B to !P. closures(P) ==> P A B.  Two AP_THM
    # + BETA_CONV pairs, same dance as _par_step_to_P (halting.py:6794).
    ap1 = AP_THM(SK_PAR_STEP_DEF, A_t)
    spec_A = TRANS(ap1, BETA_CONV(rand(ap1._concl)))
    ap2 = AP_THM(spec_A, B_t)
    spec_AB = TRANS(ap2, BETA_CONV(rand(ap2._concl)))
    forall_P = EQ_MP(spec_AB, h_AB_th)
    # forall_P: |- !P. closures(P) ==> P A B

    # Strengthened P.  DSL friction: P's bvars must not collide with
    # the outer ``A``, ``B`` (fixed) -- use ``AA``, ``BB``.
    P_lambda = p._parse(
        "\\AA:nat0. \\BB:nat0. "
        "sk_par_step AA BB /\\ sk_par_step BB (sk_bullet AA)"
    )
    spec_P = SPEC(P_lambda, forall_P)
    # spec_P : |- closures[P_lambda] ==> P_lambda A B  (un-beta'd)

    # BETA_NORM the whole implication so antecedent and consequent
    # both reach their explicit forms.  DSL friction: BETA_NORM walks
    # ALL subterms, so the closure-form's per-rule lambda applications
    # (P A A1, P (App_t ...) ..., etc.) all reduce in one pass.
    spec_P_beta = EQ_MP(BETA_NORM(spec_P._concl), spec_P)
    # spec_P_beta : |- closures_beta ==> sk_par_step A B /\
    #                                    sk_par_step B (sk_bullet A)

    # ---- Build closures_beta as h_cl ------------------------------------

    # REFL conjunct: !Z. sk_par_step Z Z /\ sk_par_step Z (sk_bullet Z).
    with p.have(
        "c_refl: !Z:nat0. sk_par_step Z Z /\\ "
        "                 sk_par_step Z (sk_bullet Z)"
    ).proof():
        p.fix("Z")
        p.have("z_refl: sk_par_step Z Z").by_thm(
            SPEC(p._parse("Z"), PAR_REFL)
        )
        p.have("z_bull: sk_par_step Z (sk_bullet Z)").by_thm(
            SPEC(p._parse("Z"), BULLET_REFL)
        )
        p.thus(
            "sk_par_step Z Z /\\ sk_par_step Z (sk_bullet Z)"
        ).by_thm(CONJ(p.fact("z_refl"), p.fact("z_bull")))

    # K-rule conjunct.  DSL friction: the outer ``fix("A B")`` puts
    # ``A`` and ``B`` in scope, so the inner closure conjuncts can't
    # ``fix("A B ...")`` -- HolError on duplicate fix.  We rename the
    # closure-form's inner bvars to ``U V U1 V1`` (alpha-equivalent to
    # ``A Y A1 Y1``; CONJ + MP go through EQ_MP / alphaorder, so the
    # final closures_th still alpha-matches spec_P_beta's antecedent).
    with p.have(
        "c_K: !U:nat0. !V:nat0. !U1:nat0. !V1:nat0. "
        "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
        "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) ==> "
        "sk_par_step (App_t (App_t K_t U) V) U1 /\\ "
        "sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
    ).proof():
        p.fix("U V U1 V1")
        p.assume(
            "((h_U_step, h_U_bull), (h_V_step, h_V_bull)): "
            "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
            "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V))"
        )
        p.have(
            "k_first: sk_par_step (App_t (App_t K_t U) V) U1"
        ).by(
            PAR_K, "U", "U1", "V", "V1",
            CONJ(p.fact("h_U_step"), p.fact("h_V_step")),
        )
        p.have(
            "bull_K: sk_bullet (App_t (App_t K_t U) V) = sk_bullet U"
        ).by(SK_BULLET_K_REDEX, "U", "V")
        p.have(
            "k_second: sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
        ).by_rewrite_of("h_U_bull", [SYM(p.fact("bull_K"))])
        p.thus(
            "sk_par_step (App_t (App_t K_t U) V) U1 /\\ "
            "sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
        ).by_thm(CONJ(p.fact("k_first"), p.fact("k_second")))

    # S-rule conjunct.  Same bvar rename: U V W U1 V1 W1.
    with p.have(
        "c_S: !U:nat0. !V:nat0. !W:nat0. "
        "!U1:nat0. !V1:nat0. !W1:nat0. "
        "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
        "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) /\\ "
        "(sk_par_step W W1 /\\ sk_par_step W1 (sk_bullet W)) ==> "
        "sk_par_step (App_t (App_t (App_t S_t U) V) W) "
        "            (App_t (App_t U1 W1) (App_t V1 W1)) /\\ "
        "sk_par_step (App_t (App_t U1 W1) (App_t V1 W1)) "
        "            (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
    ).proof():
        p.fix("U V W U1 V1 W1")
        p.assume(
            "((h_U_step, h_U_bull), "
            " (h_V_step, h_V_bull), "
            " (h_W_step, h_W_bull)): "
            "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
            "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) /\\ "
            "(sk_par_step W W1 /\\ sk_par_step W1 (sk_bullet W))"
        )
        # First conjunct via PAR_S.
        p.have(
            "s_first: sk_par_step (App_t (App_t (App_t S_t U) V) W) "
            "                     (App_t (App_t U1 W1) (App_t V1 W1))"
        ).by(
            PAR_S, "U", "U1", "V", "V1", "W", "W1",
            CONJ(
                p.fact("h_U_step"),
                CONJ(p.fact("h_V_step"), p.fact("h_W_step")),
            ),
        )
        # Second conjunct.  Bullet-unfold of the S-redex.
        p.have(
            "bull_S: sk_bullet (App_t (App_t (App_t S_t U) V) W) = "
            "        App_t (App_t (sk_bullet U) (sk_bullet W)) "
            "              (App_t (sk_bullet V) (sk_bullet W))"
        ).by(SK_BULLET_S_REDEX, "U", "V", "W")
        # Combine three IH-second-parts via PAR_APP twice.
        p.have(
            "h_UW: sk_par_step (App_t U1 W1) "
            "                  (App_t (sk_bullet U) (sk_bullet W))"
        ).by(
            PAR_APP, "U1", "sk_bullet U", "W1", "sk_bullet W",
            CONJ(p.fact("h_U_bull"), p.fact("h_W_bull")),
        )
        p.have(
            "h_VW: sk_par_step (App_t V1 W1) "
            "                  (App_t (sk_bullet V) (sk_bullet W))"
        ).by(
            PAR_APP, "V1", "sk_bullet V", "W1", "sk_bullet W",
            CONJ(p.fact("h_V_bull"), p.fact("h_W_bull")),
        )
        p.have(
            "h_outer: sk_par_step "
            "  (App_t (App_t U1 W1) (App_t V1 W1)) "
            "  (App_t (App_t (sk_bullet U) (sk_bullet W)) "
            "         (App_t (sk_bullet V) (sk_bullet W)))"
        ).by(
            PAR_APP,
            "App_t U1 W1", "App_t (sk_bullet U) (sk_bullet W)",
            "App_t V1 W1", "App_t (sk_bullet V) (sk_bullet W)",
            CONJ(p.fact("h_UW"), p.fact("h_VW")),
        )
        p.have(
            "s_second: sk_par_step "
            "  (App_t (App_t U1 W1) (App_t V1 W1)) "
            "  (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
        ).by_rewrite_of("h_outer", [SYM(p.fact("bull_S"))])
        p.thus(
            "sk_par_step (App_t (App_t (App_t S_t U) V) W) "
            "            (App_t (App_t U1 W1) (App_t V1 W1)) /\\ "
            "sk_par_step (App_t (App_t U1 W1) (App_t V1 W1)) "
            "            (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
        ).by_thm(CONJ(p.fact("s_first"), p.fact("s_second")))

    # APP-rule conjunct: delegated to the stub.  Its bvars (A B A1 B1)
    # do not need renaming -- this is a by_thm with a stand-alone lemma;
    # the inner !A binders stay bound, alpha-equivalent to closures_beta.
    p.have(
        "c_APP: !A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==> "
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_thm(_TRIANGLE_APP_CLOSURE)

    # ---- Assemble closures, MP, extract second conjunct ----------------

    closures_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    result_pair = MP(spec_P_beta, closures_th)
    # result_pair: sk_par_step A B /\ sk_par_step B (sk_bullet A)

    p.thus("sk_par_step B (sk_bullet A)").by_thm(CONJUNCT2(result_pair))


# ---------------------------------------------------------------------------
# Phase 4d -- diamond / confluence theorems for ``sk_par_step``.
#
# These three now follow without sorry from SK_BULLET_TRIANGLE (which
# itself remains a stub):
#   * TRIANGLE_EXISTS   -- existential wrapper over sk_bullet + triangle.
#   * PAR_STEP_DIAMOND  -- W := sk_bullet X.
#   * PAR_STEPS_STRIP   -- RTC induction on top of DIAMOND.
#   * PAR_STEPS_CONFLUENT -- second RTC induction on top of STRIP.
# ---------------------------------------------------------------------------


@proof
def TRIANGLE_EXISTS(p):
    """|- ?bullet. !A B. sk_par_step A B ==> sk_par_step B (bullet A).

    Witness: ``sk_bullet`` (the top-level complete-development function).
    Body: ``SK_BULLET_TRIANGLE``.
    """
    p.goal(
        "?bullet:nat0->nat0. "
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (bullet A)"
    )
    p.have(
        "h_tri: !A:nat0. !B:nat0. "
        "       sk_par_step A B ==> sk_par_step B (sk_bullet A)"
    ).by_thm(SK_BULLET_TRIANGLE)
    p.thus(
        "?bullet:nat0->nat0. "
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (bullet A)"
    ).by_exists(["sk_bullet"], "h_tri")


@proof
def PAR_STEP_DIAMOND(p):
    """|- !X Y Z. sk_par_step X Y /\\ sk_par_step X Z
                   ==> ?W. sk_par_step Y W /\\ sk_par_step Z W.

    Takahashi diamond: from the triangle property at (X, Y) and
    (X, Z), both Y and Z par-step to the common reduct ``bullet X``.
    Witness W := bullet X.
    """
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step X Y /\\ sk_par_step X Z ==> "
        "?W:nat0. sk_par_step Y W /\\ sk_par_step Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_step X Y /\\ sk_par_step X Z"
    )
    p.have(
        "h_te: ?bullet:nat0->nat0. "
        "      !A:nat0. !B:nat0. "
        "      sk_par_step A B ==> sk_par_step B (bullet A)"
    ).by_thm(TRIANGLE_EXISTS)
    p.choose("bullet", from_="h_te")
    # bullet_eq: !A B. sk_par_step A B ==> sk_par_step B (bullet A).
    p.have(
        "h_Y_bull: sk_par_step Y (bullet X)"
    ).by("bullet_eq", "X", "Y", "h_XY")
    p.have(
        "h_Z_bull: sk_par_step Z (bullet X)"
    ).by("bullet_eq", "X", "Z", "h_XZ")
    p.thus(
        "?W:nat0. sk_par_step Y W /\\ sk_par_step Z W"
    ).by_exists(["bullet X"], "h_Y_bull", "h_Z_bull")


@proof
def PAR_STEPS_STRIP(p):
    """|- !X Y Z. sk_par_step X Y /\\ sk_par_steps X Z
                   ==> ?W. sk_par_steps Y W /\\ sk_par_step Z W.

    Strip lemma: combine a one-step par-step with an RTC chain by
    closing the diamond at each joint.  Impredicative induction on the
    RTC chain ``sk_par_steps X Z`` -- instantiate the encoding's P
    with
        \\A B. !V. sk_par_step A V ==>
                   ?W. sk_par_steps V W /\\ sk_par_step B W.
    REFL: take W := V (PAR_STEPS_REFL + the given step).
    STEP: given A→B and IH at B; for V from sk_par_step A V,
          PAR_STEP_DIAMOND on (A→B, A→V) finds U; IH at U yields W;
          chain V→U + U→*W via PAR_STEPS_STEP gives V→*W.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step X Y /\\ sk_par_steps X Z ==> "
        "?W:nat0. sk_par_steps Y W /\\ sk_par_step Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_step X Y /\\ sk_par_steps X Z"
    )

    spec_XZ = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Z")
    )
    h_forall = EQ_MP(spec_XZ, p.fact("h_XZ"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!V:nat0. sk_par_step A V ==> "
        "?W:nat0. sk_par_steps V W /\\ sk_par_step B W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # REFL closure -- bvar Zb to dodge outer Z.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!V:nat0. sk_par_step Zb V ==> "
        "?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W"
    ).proof():
        p.fix("Zb V")
        p.assume("h_ZbV: sk_par_step Zb V")
        p.have("h_VV: sk_par_steps V V").by(PAR_STEPS_REFL, "V")
        p.thus(
            "?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W"
        ).by_exists(["V"], "h_VV", "h_ZbV")

    # STEP closure -- bvars a b c to dodge outer.
    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!V:nat0. sk_par_step b V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step c W) ==> "
        "(!V:nat0. sk_par_step a V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step c W)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!V. sk_par_step b V ==> "
            "    ?W. sk_par_steps V W /\\ sk_par_step c W)"
        )
        p.fix("V")
        p.assume("h_aV: sk_par_step a V")
        p.have(
            "h_conj_diam: sk_par_step a b /\\ sk_par_step a V"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_aV")))
        p.have(
            "h_diam: ?U. sk_par_step b U /\\ sk_par_step V U"
        ).by(PAR_STEP_DIAMOND, "a", "b", "V", "h_conj_diam")
        p.choose("U", from_="h_diam")
        p.split("U_eq", "(h_bU, h_VU)")
        p.have(
            "h_IH_at: ?W. sk_par_steps U W /\\ sk_par_step c W"
        ).by("h_IH", "U", "h_bU")
        p.choose("W", from_="h_IH_at")
        p.split("W_eq", "(h_UW, h_cW)")
        p.have(
            "h_conj_chain: sk_par_step V U /\\ sk_par_steps U W"
        ).by_thm(CONJ(p.fact("h_VU"), p.fact("h_UW")))
        p.have(
            "h_VW: sk_par_steps V W"
        ).by(PAR_STEPS_STEP, "V", "U", "W", "h_conj_chain")
        p.thus(
            "?W:nat0. sk_par_steps V W /\\ sk_par_step c W"
        ).by_exists(["W"], "h_VW", "h_cW")

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !V:nat0. sk_par_step Zb V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!V:nat0. sk_par_step b V ==> "
        "        ?W:nat0. sk_par_steps V W /\\ sk_par_step c W) ==> "
        "    (!V:nat0. sk_par_step a V ==> "
        "        ?W:nat0. sk_par_steps V W /\\ sk_par_step c W))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXZ: !V:nat0. sk_par_step X V ==> "
        "       ?W:nat0. sk_par_steps V W /\\ sk_par_step Z W"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus(
        "?W:nat0. sk_par_steps Y W /\\ sk_par_step Z W"
    ).by("h_PXZ", "Y", "h_XY")


@proof
def PAR_STEPS_CONFLUENT(p):
    """|- !X Y Z. sk_par_steps X Y /\\ sk_par_steps X Z
                   ==> ?W. sk_par_steps Y W /\\ sk_par_steps Z W.

    Church-Rosser for the par-step RTC.  Impredicative induction on
    the first chain ``sk_par_steps X Y`` with ``PAR_STEPS_STRIP``
    closing each joint:
        P A B := !V. sk_par_steps A V ==>
                     ?W. sk_par_steps B W /\\ sk_par_steps V W.
    REFL: take W := V (the given chain + PAR_STEPS_REFL on V).
    STEP: a -> b given + IH at b; for V from sk_par_steps a V, STRIP
          on (a->b, a->*V) finds U with sk_par_steps b U /\\ sk_par_step
          V U; IH at U produces W; chain V->U + U->*W via PAR_STEPS_STEP
          gives V->*W.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_steps X Y /\\ sk_par_steps X Z ==> "
        "?W:nat0. sk_par_steps Y W /\\ sk_par_steps Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_steps X Y /\\ sk_par_steps X Z"
    )

    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!V:nat0. sk_par_steps A V ==> "
        "?W:nat0. sk_par_steps B W /\\ sk_par_steps V W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # REFL closure -- bvar Zb to dodge outer Z.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!V:nat0. sk_par_steps Zb V ==> "
        "?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W"
    ).proof():
        p.fix("Zb V")
        p.assume("h_ZbV: sk_par_steps Zb V")
        p.have("h_VV: sk_par_steps V V").by(PAR_STEPS_REFL, "V")
        p.thus(
            "?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W"
        ).by_exists(["V"], "h_ZbV", "h_VV")

    # STEP closure -- bvars a b c to dodge outer.
    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!V:nat0. sk_par_steps b V ==> "
        "    ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W) ==> "
        "(!V:nat0. sk_par_steps a V ==> "
        "    ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!V. sk_par_steps b V ==> "
            "    ?W. sk_par_steps c W /\\ sk_par_steps V W)"
        )
        p.fix("V")
        p.assume("h_aV: sk_par_steps a V")
        p.have(
            "h_conj_strip: sk_par_step a b /\\ sk_par_steps a V"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_aV")))
        p.have(
            "h_strip: ?U. sk_par_steps b U /\\ sk_par_step V U"
        ).by(PAR_STEPS_STRIP, "a", "b", "V", "h_conj_strip")
        p.choose("U", from_="h_strip")
        p.split("U_eq", "(h_bU, h_VU)")
        p.have(
            "h_IH_at: ?W. sk_par_steps c W /\\ sk_par_steps U W"
        ).by("h_IH", "U", "h_bU")
        p.choose("W", from_="h_IH_at")
        p.split("W_eq", "(h_cW, h_UW)")
        p.have(
            "h_conj_chain: sk_par_step V U /\\ sk_par_steps U W"
        ).by_thm(CONJ(p.fact("h_VU"), p.fact("h_UW")))
        p.have(
            "h_VW: sk_par_steps V W"
        ).by(PAR_STEPS_STEP, "V", "U", "W", "h_conj_chain")
        p.thus(
            "?W:nat0. sk_par_steps c W /\\ sk_par_steps V W"
        ).by_exists(["W"], "h_cW", "h_VW")

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !V:nat0. sk_par_steps Zb V ==> "
        "    ?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!V:nat0. sk_par_steps b V ==> "
        "        ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W) ==> "
        "    (!V:nat0. sk_par_steps a V ==> "
        "        ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: !V:nat0. sk_par_steps X V ==> "
        "       ?W:nat0. sk_par_steps Y W /\\ sk_par_steps V W"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus(
        "?W:nat0. sk_par_steps Y W /\\ sk_par_steps Z W"
    ).by("h_PXY", "Z", "h_XZ")


# ---------------------------------------------------------------------------
# Generic par-step infrastructure used by HALTS_PAR_INVARIANT and the
# par/bullet bridge: PAR_STEPS_TRANS (composition), SK_ITER_TO_PAR_STEPS
# (iter-form embedding into par-chains), NORMAL_STABILITY_PAR_STEPS
# (par-step from a normal goes nowhere).
# ---------------------------------------------------------------------------


@proof
def PAR_STEPS_TRANS(p):
    """|- !X Y Z. sk_par_steps X Y /\\ sk_par_steps Y Z
                   ==> sk_par_steps X Z.

    Transitivity of the par-step RTC.  Impredicative induction on the
    first chain: instantiate the encoding's P with
    ``\\A B. !W. sk_par_steps B W ==> sk_par_steps A W``.  REFL closure
    is the identity, STEP closure prepends one par-step via
    ``PAR_STEPS_STEP``.
    """
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_steps X Y /\\ sk_par_steps Y Z ==> sk_par_steps X Z"
    )
    from tactics import BETA_RULE
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_YZ): sk_par_steps X Y /\\ sk_par_steps Y Z"
    )

    # Unfold ``sk_par_steps X Y`` to its impredicative universal.
    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    # SPEC at the lifted P; BETA_RULE cleans redexes.
    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!W:nat0. sk_par_steps B W ==> sk_par_steps A W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # Lifted closures.  Bvars renamed to ``Zb / a b c w`` to dodge the
    # outer ``X Y Z`` fixed names.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!w:nat0. sk_par_steps Zb w ==> sk_par_steps Zb w"
    ).proof():
        p.fix("Zb w")
        p.assume("h: sk_par_steps Zb w")
        p.thus("sk_par_steps Zb w").by_thm(p.fact("h"))

    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!w:nat0. sk_par_steps c w ==> sk_par_steps b w) ==> "
        "(!w:nat0. sk_par_steps c w ==> sk_par_steps a w)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!w. sk_par_steps c w ==> sk_par_steps b w)"
        )
        p.fix("w")
        p.assume("h_cw: sk_par_steps c w")
        p.have("h_bw: sk_par_steps b w").by("h_IH", "w", "h_cw")
        p.have(
            "h_conj: sk_par_step a b /\\ sk_par_steps b w"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_bw")))
        p.thus("sk_par_steps a w").by(
            PAR_STEPS_STEP, "a", "b", "w", "h_conj"
        )

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !w:nat0. sk_par_steps Zb w ==> sk_par_steps Zb w) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!w. sk_par_steps c w ==> sk_par_steps b w) ==> "
        "    (!w. sk_par_steps c w ==> sk_par_steps a w))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: !w:nat0. sk_par_steps Y w ==> sk_par_steps X w"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus("sk_par_steps X Z").by("h_PXY", "Z", "h_YZ")


@proof
def SK_ITER_TO_PAR_STEPS(p):
    """|- !n X. sk_par_steps X (sk_iter n X).

    Induction on n.  Base: SK_ITER_ZERO + PAR_STEPS_REFL bridged via
    AP_TERM on ``sk_iter 0 X = X``.  Step: ``SK_PAR_STEP_TO_SK_STEP``
    plus ``PAR_STEP_TO_STEPS`` give a single-step extension; compose
    with IH via ``PAR_STEPS_TRANS``; rewrite head via SK_ITER_SUC.
    """
    p.goal("!n:nat0. !X:nat0. sk_par_steps X (sk_iter n X)")
    with p.induction("n"):
        with p.base():
            p.fix("X")
            p.have("h_z: sk_iter 0 X = X").by(SK_ITER_ZERO, "X")
            p.have("h_refl: sk_par_steps X X").by(PAR_STEPS_REFL, "X")
            # DSL friction: rewriting X -> sk_iter 0 X loops, so we
            # build the bridging equation explicitly via AP_TERM.
            sps_X = mk_app(sk_par_steps, p._parse("X"))
            eq_bridge = AP_TERM(sps_X, SYM(p.fact("h_z")))
            p.thus("sk_par_steps X (sk_iter 0 X)").by_eq_mp(
                eq_bridge, "h_refl"
            )
        with p.step("IH"):
            p.fix("X")
            p.have("h_ih: sk_par_steps X (sk_iter n X)").by("IH", "X")
            p.have(
                "h_suc: sk_iter (SUC0 n) X = sk_step (sk_iter n X)"
            ).by(SK_ITER_SUC, "n", "X")
            p.have(
                "h_par: sk_par_step (sk_iter n X) (sk_step (sk_iter n X))"
            ).by(SK_PAR_STEP_TO_SK_STEP, "sk_iter n X")
            p.have(
                "h_pss: sk_par_steps (sk_iter n X) (sk_step (sk_iter n X))"
            ).by(
                PAR_STEP_TO_STEPS,
                "sk_iter n X", "sk_step (sk_iter n X)", "h_par",
            )
            p.have(
                "h_conj: sk_par_steps X (sk_iter n X) /\\ "
                "        sk_par_steps (sk_iter n X) "
                "                     (sk_step (sk_iter n X))"
            ).by_thm(CONJ(p.fact("h_ih"), p.fact("h_pss")))
            p.have(
                "h_trans: sk_par_steps X (sk_step (sk_iter n X))"
            ).by(
                PAR_STEPS_TRANS,
                "X", "sk_iter n X", "sk_step (sk_iter n X)",
                "h_conj",
            )
            p.thus(
                "sk_par_steps X (sk_iter (SUC0 n) X)"
            ).by_rewrite_of("h_trans", [SYM(p.fact("h_suc"))])


@proof
def IS_NORMAL_NOT_K_REDEX_SHAPE(p):
    """|- !M N. ~is_normal (App_t (App_t K_t M) N).

    Size argument.  Suppose ``is_normal (App_t (App_t K_t M) N)``.
    Then ``sk_step (K-redex) = K-redex`` (IS_NORMAL_IMP_FIXED) while
    ``sk_step (K-redex) = M`` (SK_STEP_K); hence
    ``M = App_t (App_t K_t M) N``.  Apply SK_SIZE_LT_DEEP_LEFT
    (sk_size M < sk_size (App_t (App_t K_t M) N)) and substitute via
    the equation -- yields ``sk_size M < sk_size M``, contradicting
    ``NAT0_LT_NOT_REFL``.
    """
    from nat0_order import NAT0_LT_NOT_REFL
    p.goal("!M:nat0. !N:nat0. ~is_normal (App_t (App_t K_t M) N)")
    p.fix("M N")
    with p.suppose("h_norm: is_normal (App_t (App_t K_t M) N)"):
        p.have(
            "h_fixed: sk_step (App_t (App_t K_t M) N) "
            "         = App_t (App_t K_t M) N"
        ).by(
            IS_NORMAL_IMP_FIXED, "App_t (App_t K_t M) N", "h_norm"
        )
        p.have(
            "h_step: sk_step (App_t (App_t K_t M) N) = M"
        ).by(SK_STEP_K, "M", "N")
        p.have(
            "h_M_eq: M = App_t (App_t K_t M) N"
        ).by_thm(TRANS(SYM(p.fact("h_step")), p.fact("h_fixed")))
        p.have(
            "h_lt: nat0_lt (sk_size M) "
            "      (sk_size (App_t (App_t K_t M) N))"
        ).by(SK_SIZE_LT_DEEP_LEFT, "M", "K_t", "N")
        p.have(
            "h_self_lt: nat0_lt (sk_size M) (sk_size M)"
        ).by_rewrite_of("h_lt", [SYM(p.fact("h_M_eq"))])
        p.have(
            "h_nrefl: ~nat0_lt (sk_size M) (sk_size M)"
        ).by(NAT0_LT_NOT_REFL, "sk_size M")
        p.absurd().by_conj("h_nrefl", "h_self_lt")


@proof
def IS_NORMAL_NOT_S_REDEX_SHAPE(p):
    """|- !M N P. ~is_normal (App_t (App_t (App_t S_t M) N) P).

    Size argument via APP_T_INJ.  From ``is_normal (S-redex)`` derive
    ``App_t (App_t M P) (App_t N P) = App_t (App_t (App_t S_t M) N) P``
    (IS_NORMAL_IMP_FIXED + SK_STEP_S).  Outer APP_T_INJ exposes the
    right-conjunct ``App_t N P = P`` -- P would be a strict superterm
    of itself.  SK_SIZE_LT_APP_RIGHT + NAT0_LT_NOT_REFL on P contradicts.
    """
    from nat0_order import NAT0_LT_NOT_REFL
    p.goal(
        "!M:nat0. !N:nat0. !P:nat0. "
        "~is_normal (App_t (App_t (App_t S_t M) N) P)"
    )
    p.fix("M N P")
    with p.suppose(
        "h_norm: is_normal (App_t (App_t (App_t S_t M) N) P)"
    ):
        p.have(
            "h_fixed: "
            "sk_step (App_t (App_t (App_t S_t M) N) P) "
            "= App_t (App_t (App_t S_t M) N) P"
        ).by(
            IS_NORMAL_IMP_FIXED,
            "App_t (App_t (App_t S_t M) N) P",
            "h_norm",
        )
        p.have(
            "h_step: "
            "sk_step (App_t (App_t (App_t S_t M) N) P) "
            "= App_t (App_t M P) (App_t N P)"
        ).by(SK_STEP_S, "M", "N", "P")
        p.have(
            "h_eq: App_t (App_t M P) (App_t N P) "
            "      = App_t (App_t (App_t S_t M) N) P"
        ).by_thm(
            TRANS(SYM(p.fact("h_step")), p.fact("h_fixed"))
        )
        # Outer APP_T_INJ -- pick the right conjunct App_t N P = P.
        p.have(
            "h_inj: App_t M P = App_t (App_t S_t M) N "
            "       /\\ App_t N P = P"
        ).by(
            APP_T_INJ,
            "App_t M P", "App_t N P",
            "App_t (App_t S_t M) N", "P",
            "h_eq",
        )
        p.split("h_inj", "(_, h_NP)")
        p.have("h_P_eq: P = App_t N P").by_thm(SYM(p.fact("h_NP")))
        p.have(
            "h_lt: nat0_lt (sk_size P) (sk_size (App_t N P))"
        ).by(SK_SIZE_LT_APP_RIGHT, "P", "N")
        p.have(
            "h_self_lt: nat0_lt (sk_size P) (sk_size P)"
        ).by_rewrite_of("h_lt", [SYM(p.fact("h_P_eq"))])
        p.have(
            "h_nrefl: ~nat0_lt (sk_size P) (sk_size P)"
        ).by(NAT0_LT_NOT_REFL, "sk_size P")
        p.absurd().by_conj("h_nrefl", "h_self_lt")


@proof
def IS_NORMAL_APP_DECOMP(p):
    """|- !A B. is_normal (App_t A B) ==> is_normal A /\\ is_normal B.

    From ``is_normal (App_t A B)`` derive that the outer App is neither
    a K- nor S-redex (via IS_NORMAL_NOT_{K,S}_REDEX_SHAPE, by
    contradicting an assumed redex shape).  Then SK_STEP_LEFT with the
    two not-redex preconditions forces ``sk_step A = A`` by
    contradiction; SK_STEP_RIGHT chains in the established
    ``sk_step A = A`` to force ``sk_step B = B``.  Fold both back to
    ``is_normal`` via IS_NORMAL_DEF.
    """
    p.goal(
        "!A:nat0. !B:nat0. "
        "is_normal (App_t A B) ==> is_normal A /\\ is_normal B"
    )
    p.fix("A B")
    p.assume("h_norm_AB: is_normal (App_t A B)")
    p.have(
        "h_fixed: sk_step (App_t A B) = App_t A B"
    ).by(IS_NORMAL_IMP_FIXED, "App_t A B", "h_norm_AB")

    # not-K-redex precondition.
    with p.have(
        "not_kred: ~(?a b. App_t A B = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "h_kred: ?a b. App_t A B = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="h_kred")
            p.choose("b", from_="a_eq")
            p.have(
                "h_norm_kred: is_normal (App_t (App_t K_t a) b)"
            ).by_rewrite_of("h_norm_AB", ["b_eq"])
            p.have(
                "h_not_norm: ~is_normal (App_t (App_t K_t a) b)"
            ).by(IS_NORMAL_NOT_K_REDEX_SHAPE, "a", "b")
            p.absurd().by_conj("h_not_norm", "h_norm_kred")

    # not-S-redex precondition.
    with p.have(
        "not_sred: ~(?a b c. "
        "App_t A B = App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "h_sred: ?a b c. "
            "App_t A B = App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="h_sred")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_norm_sred: "
                "is_normal (App_t (App_t (App_t S_t a) b) c)"
            ).by_rewrite_of("h_norm_AB", ["c_eq"])
            p.have(
                "h_not_norm: "
                "~is_normal (App_t (App_t (App_t S_t a) b) c)"
            ).by(IS_NORMAL_NOT_S_REDEX_SHAPE, "a", "b", "c")
            p.absurd().by_conj("h_not_norm", "h_norm_sred")

    # sk_step A = A by contradiction via SK_STEP_LEFT.
    with p.have("h_step_A: sk_step A = A").by_contradiction("h_neg_A"):
        p.have(
            "h_left: sk_step (App_t A B) = App_t (sk_step A) B"
        ).by(
            SK_STEP_LEFT, "A", "B",
            "not_kred", "not_sred", "h_neg_A",
        )
        p.have(
            "h_App_eq: App_t (sk_step A) B = App_t A B"
        ).by_thm(TRANS(SYM(p.fact("h_left")), p.fact("h_fixed")))
        p.have(
            "h_inj: sk_step A = A /\\ B = B"
        ).by(APP_T_INJ, "sk_step A", "B", "A", "B", "h_App_eq")
        p.split("h_inj", "(h_eq_A, _)")
        p.absurd().by_conj("h_neg_A", "h_eq_A")

    p.have("h_norm_A: is_normal A").by_unfold(
        "h_step_A", IS_NORMAL_DEF
    )

    # sk_step B = B by contradiction via SK_STEP_RIGHT.
    with p.have("h_step_B: sk_step B = B").by_contradiction("h_neg_B"):
        p.have(
            "h_right: sk_step (App_t A B) = App_t A (sk_step B)"
        ).by(
            SK_STEP_RIGHT, "A", "B",
            "not_kred", "not_sred", "h_step_A", "h_neg_B",
        )
        p.have(
            "h_App_eq: App_t A (sk_step B) = App_t A B"
        ).by_thm(TRANS(SYM(p.fact("h_right")), p.fact("h_fixed")))
        p.have(
            "h_inj: A = A /\\ sk_step B = B"
        ).by(APP_T_INJ, "A", "sk_step B", "A", "B", "h_App_eq")
        p.split("h_inj", "(_, h_eq_B)")
        p.absurd().by_conj("h_neg_B", "h_eq_B")

    p.have("h_norm_B: is_normal B").by_unfold(
        "h_step_B", IS_NORMAL_DEF
    )

    p.thus("is_normal A /\\ is_normal B").by_thm(
        CONJ(p.fact("h_norm_A"), p.fact("h_norm_B"))
    )


@proof
def NORMAL_STABILITY_PAR_STEP(p):
    """|- !X Y. is_normal X /\\ sk_par_step X Y ==> Y = X.

    Impredicative induction on the par-step at
        P A B := is_normal A ==> B = A.
    REFL : tautology.
    K, S : vacuously true via IS_NORMAL_NOT_{K,S}_REDEX_SHAPE -- the
           hypothesis ``is_normal (K-/S-redex)`` is contradictory, so
           the implication's RHS holds via CONTR.
    APP  : decompose ``is_normal (App_t A B)`` into ``is_normal A`` and
           ``is_normal B`` via IS_NORMAL_APP_DECOMP, apply both IHs,
           lift to ``App_t A1 B1 = App_t A B`` via MK_COMB congruence.
    """
    from tactics import BETA_RULE, MK_COMB
    p.goal(
        "!X:nat0. !Y:nat0. is_normal X /\\ sk_par_step X Y ==> Y = X"
    )
    p.fix("X Y")
    p.assume(
        "(h_normX, h_XY): is_normal X /\\ sk_par_step X Y"
    )

    spec_XY = unfold_def_at(
        SK_PAR_STEP_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. is_normal A ==> B = A"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # REFL closure.
    with p.have(
        "lifted_refl: !Zb:nat0. is_normal Zb ==> Zb = Zb"
    ).proof():
        p.fix("Zb")
        p.assume("h: is_normal Zb")
        p.thus("Zb = Zb").by_thm(REFL(p._parse("Zb")))

    # K closure -- vacuous via IS_NORMAL_NOT_K_REDEX_SHAPE.
    with p.have(
        "lifted_K: !a:nat0. !y:nat0. !a1:nat0. !y1:nat0. "
        "(is_normal a ==> a1 = a) /\\ (is_normal y ==> y1 = y) ==> "
        "(is_normal (App_t (App_t K_t a) y) ==> "
        " a1 = App_t (App_t K_t a) y)"
    ).proof():
        p.fix("a y a1 y1")
        p.assume(
            "(_h_a, _h_y): "
            "(is_normal a ==> a1 = a) /\\ (is_normal y ==> y1 = y)"
        )
        p.assume("h_norm_K: is_normal (App_t (App_t K_t a) y)")
        p.have(
            "h_neg: ~is_normal (App_t (App_t K_t a) y)"
        ).by(IS_NORMAL_NOT_K_REDEX_SHAPE, "a", "y")
        p.absurd().by_conj("h_neg", "h_norm_K")

    # S closure -- vacuous via IS_NORMAL_NOT_S_REDEX_SHAPE.
    with p.have(
        "lifted_S: !a:nat0. !b:nat0. !c:nat0. "
        "!a1:nat0. !b1:nat0. !c1:nat0. "
        "(is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b) /\\ "
        "(is_normal c ==> c1 = c) ==> "
        "(is_normal (App_t (App_t (App_t S_t a) b) c) ==> "
        " App_t (App_t a1 c1) (App_t b1 c1) = "
        " App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        p.fix("a b c a1 b1 c1")
        p.assume(
            "(_h_a, _h_b, _h_c): "
            "(is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b) /\\ "
            "(is_normal c ==> c1 = c)"
        )
        p.assume(
            "h_norm_S: is_normal (App_t (App_t (App_t S_t a) b) c)"
        )
        p.have(
            "h_neg: ~is_normal (App_t (App_t (App_t S_t a) b) c)"
        ).by(IS_NORMAL_NOT_S_REDEX_SHAPE, "a", "b", "c")
        p.absurd().by_conj("h_neg", "h_norm_S")

    # APP closure -- decompose is_normal, apply IHs, lift via congruence.
    with p.have(
        "lifted_APP: !a:nat0. !b:nat0. !a1:nat0. !b1:nat0. "
        "(is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b) ==> "
        "(is_normal (App_t a b) ==> App_t a1 b1 = App_t a b)"
    ).proof():
        p.fix("a b a1 b1")
        p.assume(
            "(h_ih_a, h_ih_b): "
            "(is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b)"
        )
        p.assume("h_norm_ab: is_normal (App_t a b)")
        p.have(
            "h_dec: is_normal a /\\ is_normal b"
        ).by(IS_NORMAL_APP_DECOMP, "a", "b", "h_norm_ab")
        p.split("h_dec", "(h_norm_a, h_norm_b)")
        p.have("h_a1: a1 = a").by("h_ih_a", "h_norm_a")
        p.have("h_b1: b1 = b").by("h_ih_b", "h_norm_b")
        # MK_COMB lifts (a1 = a, b1 = b) to (App_t a1 b1 = App_t a b).
        eq_left = AP_TERM(p._parse("App_t"), p.fact("h_a1"))
        p.thus("App_t a1 b1 = App_t a b").by_thm(
            MK_COMB(eq_left, p.fact("h_b1"))
        )

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. is_normal Zb ==> Zb = Zb) /\\ "
        "(!a:nat0. !y:nat0. !a1:nat0. !y1:nat0. "
        "    (is_normal a ==> a1 = a) /\\ (is_normal y ==> y1 = y) ==> "
        "    (is_normal (App_t (App_t K_t a) y) ==> "
        "     a1 = App_t (App_t K_t a) y)) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        " !a1:nat0. !b1:nat0. !c1:nat0. "
        "    (is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b) /\\ "
        "    (is_normal c ==> c1 = c) ==> "
        "    (is_normal (App_t (App_t (App_t S_t a) b) c) ==> "
        "     App_t (App_t a1 c1) (App_t b1 c1) = "
        "     App_t (App_t (App_t S_t a) b) c)) /\\ "
        "(!a:nat0. !b:nat0. !a1:nat0. !b1:nat0. "
        "    (is_normal a ==> a1 = a) /\\ (is_normal b ==> b1 = b) ==> "
        "    (is_normal (App_t a b) ==> App_t a1 b1 = App_t a b))"
    ).by_thm(
        CONJ(
            p.fact("lifted_refl"),
            CONJ(
                p.fact("lifted_K"),
                CONJ(p.fact("lifted_S"), p.fact("lifted_APP")),
            ),
        )
    )

    p.have(
        "h_PXY: is_normal X ==> Y = X"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus("Y = X").by("h_PXY", "h_normX")


@proof
def NORMAL_STABILITY_PAR_STEPS(p):
    """|- !X Y. is_normal X /\\ sk_par_steps X Y ==> Y = X.

    Lifts NORMAL_STABILITY_PAR_STEP through the RTC.  Impredicative
    induction with P := ``\\A B. is_normal A ==> B = A``:
      REFL : tautology.
      STEP : a -> b given + IH ``is_normal b ==> c = b``; single-step
             stability at (a, b) gives b = a, which transports
             is_normal a to is_normal b; IH yields c = b; TRANS gives
             c = a.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. is_normal X /\\ sk_par_steps X Y ==> Y = X"
    )
    p.fix("X Y")
    p.assume(
        "(h_normX, h_XY): is_normal X /\\ sk_par_steps X Y"
    )

    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. is_normal A ==> B = A"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    with p.have(
        "lifted_refl: !Zb:nat0. is_normal Zb ==> Zb = Zb"
    ).proof():
        p.fix("Zb")
        p.assume("h: is_normal Zb")
        p.thus("Zb = Zb").by_thm(REFL(p._parse("Zb")))

    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ (is_normal b ==> c = b) ==> "
        "(is_normal a ==> c = a)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ (is_normal b ==> c = b)"
        )
        p.assume("h_norm_a: is_normal a")
        p.have(
            "h_conj: is_normal a /\\ sk_par_step a b"
        ).by_thm(CONJ(p.fact("h_norm_a"), p.fact("h_ab")))
        p.have("h_ba: b = a").by(
            NORMAL_STABILITY_PAR_STEP, "a", "b", "h_conj"
        )
        # is_normal b via a -> b rewrite (rule SYM h_ba = a = b).
        p.have("h_norm_b: is_normal b").by_rewrite_of(
            "h_norm_a", [SYM(p.fact("h_ba"))]
        )
        p.have("h_cb: c = b").by("h_IH", "h_norm_b")
        p.thus("c = a").by_thm(
            TRANS(p.fact("h_cb"), p.fact("h_ba"))
        )

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. is_normal Zb ==> Zb = Zb) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ (is_normal b ==> c = b) ==> "
        "    (is_normal a ==> c = a))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: is_normal X ==> Y = X"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus("Y = X").by("h_PXY", "h_normX")


# ---------------------------------------------------------------------------
# Bullet-form halts (the path used downstream).
#
#   bullet_iter 0        = \t. t
#   bullet_iter (SUC0 n) = \t. sk_bullet (bullet_iter n t)
#   halts_b t            := ?n. is_normal (bullet_iter n t)
#
# Takahashi-strategy halting: a term halts iff its deterministic
# parallel-development trajectory reaches normal form.  Classically
# equivalent to ``halts`` (the LMO sk_iter version) via standardization,
# but the bullet form sidesteps the standardization bridge entirely on
# the undecidability critical path.
#
# See iter_to_bullet.md for the full migration plan.  This block ships:
# the recursion equations for bullet_iter and the halts_b unfold
# (HALTS_B_AT).  Under Option C, the par-form halts_par is also retained
# downstream and bridged to halts_b via HALTS_B_IFF_HALTS_PAR.
# ---------------------------------------------------------------------------


# c : nat0 -> nat0  ==  \t. t.   (identical to sk_iter's base shape)
_c_bullet_iter = mk_abs(_n0_t_var, _n0_t_var)

# h : nat0 -> (nat0 -> nat0) -> (nat0 -> nat0)
#   == \k. \a. \t. sk_bullet (a t).
_h_bullet_iter = mk_abs(
    _n0_k_var,
    mk_abs(
        _n0_a_var,
        mk_abs(_n0_t_var, mk_app(sk_bullet, mk_app(_n0_a_var, _n0_t_var))),
    ),
)

BULLET_ITER_BASE, BULLET_ITER_STEP = define_unary_0(
    "bullet_iter",
    parse_type("nat0 -> nat0 -> nat0"),
    _c_bullet_iter,
    _h_bullet_iter,
    result_ty=parse_type("nat0 -> nat0"),
)
bullet_iter = mk_const("bullet_iter", [])
# BULLET_ITER_BASE : |- bullet_iter 0 = (\t. t)
# BULLET_ITER_STEP : |- !n. bullet_iter (SUC0 n) = (\t. sk_bullet (bullet_iter n t))


@proof
def BULLET_ITER_ZERO(p):
    """|- !t. bullet_iter 0 t = t.  Mirrors SK_ITER_ZERO."""
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    ap = AP_THM(BULLET_ITER_BASE, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. bullet_iter 0 t = t")
    p.thus("!t. bullet_iter 0 t = t").by_thm(GEN(_n0_t_var, spec_th))


@proof
def BULLET_ITER_SUC(p):
    """|- !n t. bullet_iter (SUC0 n) t = sk_bullet (bullet_iter n t).

    Mirrors SK_ITER_SUC: SPEC BULLET_ITER_STEP at n, AP_THM at t, BETA.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, SPEC, GENL

    n_var = Var("n", nat0_ty)
    step_at_n = SPEC(n_var, BULLET_ITER_STEP)
    ap = AP_THM(step_at_n, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!n t. bullet_iter (SUC0 n) t = sk_bullet (bullet_iter n t)")
    p.thus(
        "!n t. bullet_iter (SUC0 n) t = sk_bullet (bullet_iter n t)"
    ).by_thm(GENL([n_var, _n0_t_var], spec_th))


# halts_b t := ?n. is_normal (bullet_iter n t).
HALTS_B_DEF = define(
    "halts_b",
    parse_type("nat0 -> bool"),
    "\\t:nat0. ?n:nat0. is_normal (bullet_iter n t)",
)
halts_b = mk_const("halts_b", [])


@proof
def HALTS_B_AT(p):
    """|- !t. halts_b t = (?n. is_normal (bullet_iter n t)).

    Direct unfold of HALTS_B_DEF via AP_THM + BETA -- mirrors HALTS_AT.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    ap = AP_THM(HALTS_B_DEF, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. halts_b t = (?n. is_normal (bullet_iter n t))")
    p.thus(
        "!t. halts_b t = (?n. is_normal (bullet_iter n t))"
    ).by_thm(GEN(_n0_t_var, spec_th))


# halts_par t := ?N. sk_par_steps t N /\ is_normal N.
# Retained under Option C as the par-side of the bullet/par bridge.
HALTS_PAR_DEF = define(
    "halts_par",
    parse_type("nat0 -> bool"),
    "\\t:nat0. ?N:nat0. sk_par_steps t N /\\ is_normal N",
)
halts_par = mk_const("halts_par", [])


@proof
def HALTS_PAR_AT(p):
    """|- !t. halts_par t = (?N. sk_par_steps t N /\\ is_normal N).

    Direct unfold of HALTS_PAR_DEF via AP_THM + BETA -- mirrors HALTS_AT.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    ap = AP_THM(HALTS_PAR_DEF, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. halts_par t = (?N. sk_par_steps t N /\\ is_normal N)")
    p.thus(
        "!t. halts_par t = (?N. sk_par_steps t N /\\ is_normal N)"
    ).by_thm(GEN(_n0_t_var, spec_th))


@proof
def HALTS_B_IFF_HALTS_PAR(p):
    """|- !X. halts_b X = halts_par X.

    *** STUB.  The bullet/par halt-bridge (Option C's central lemma; see
    iter_to_bullet.md "HALTS_B_IFF_HALTS_PAR (the bridge -- Option C's
    new central lemma)").

    Forward (halts_b X ==> halts_par X): bullet trajectory is a chain
    of par-steps (BULLET_REFL: par_step W (sk_bullet W)).  If
    bullet_iter n X = N is normal, then sk_par_steps X N (n applications
    of PAR_STEPS_STEP) witnesses halts_par X.  ~10 lines.

    Backward (halts_par X ==> halts_b X): given ?N. sk_par_steps X N
    /\\ is_normal N, induct on the par-step count to N.  At each step
    SK_BULLET_TRIANGLE pushes ``par_step Y (sk_bullet X)`` past the
    remaining par-chain, so ``sk_par_steps (sk_bullet X) N`` and IH
    on sk_bullet X yields ``?m. is_normal (bullet_iter m (sk_bullet X))
    = is_normal (bullet_iter (SUC0 m) X)``.  ~50 lines.

    Gated on SK_BULLET_TRIANGLE (also stubbed via _TRIANGLE_APP_CLOSURE).
    """
    p.goal("!X. halts_b X = halts_par X")
    p.sorry()


@proof
def HALTS_PAR_INVARIANT(p):
    """|- !X Y. sk_par_steps X Y ==> halts_par X = halts_par Y.

    halts_par is invariant along par-step chains.  Iff-intro on the
    two directions:

    Forward (halts_par X ==> halts_par Y).  Unfold halts_par X to
    ``?N. sk_par_steps X N /\\ is_normal N``.  Combined with the
    hypothesis sk_par_steps X Y, PAR_STEPS_CONFLUENT gives a common
    reduct ``?W. sk_par_steps N W /\\ sk_par_steps Y W``.  N normal +
    NORMAL_STABILITY_PAR_STEPS forces W = N; transport sk_par_steps Y
    W to sk_par_steps Y N; witness halts_par Y.

    Backward (halts_par Y ==> halts_par X).  Unfold halts_par Y;
    PAR_STEPS_TRANS prepends sk_par_steps X Y; witness halts_par X.

    Stays inside the par calculus (no STANDARDIZATION_NORMAL).
    """
    p.goal(
        "!X Y. sk_par_steps X Y ==> halts_par X = halts_par Y"
    )
    p.fix("X Y")
    p.assume("h_XY: sk_par_steps X Y")

    # ---- Forward direction ----------------------------------------------
    with p.have(
        "h_fwd: halts_par X ==> halts_par Y"
    ).proof():
        p.assume("h_hX: halts_par X")
        p.have(
            "h_at_X: halts_par X = "
            "(?N. sk_par_steps X N /\\ is_normal N)"
        ).by(HALTS_PAR_AT, "X")
        p.have(
            "h_ex_X: ?N. sk_par_steps X N /\\ is_normal N"
        ).by_eq_mp("h_at_X", "h_hX")
        p.choose("N", from_="h_ex_X")
        p.split("N_eq", "(h_XN, h_norm_N)")

        # Confluence: X -*> N and X -*> Y join at some W.
        p.have(
            "h_conj_XN_XY: sk_par_steps X N /\\ sk_par_steps X Y"
        ).by_thm(CONJ(p.fact("h_XN"), p.fact("h_XY")))
        p.have(
            "h_join: ?W. sk_par_steps N W /\\ sk_par_steps Y W"
        ).by(
            PAR_STEPS_CONFLUENT, "X", "N", "Y", "h_conj_XN_XY"
        )
        p.choose("W", from_="h_join")
        p.split("W_eq", "(h_NW, h_YW)")

        # N normal + N -*> W forces W = N.
        p.have(
            "h_conj_NW: is_normal N /\\ sk_par_steps N W"
        ).by_thm(CONJ(p.fact("h_norm_N"), p.fact("h_NW")))
        p.have("h_W_N: W = N").by(
            NORMAL_STABILITY_PAR_STEPS, "N", "W", "h_conj_NW"
        )
        # Transport h_YW : sk_par_steps Y W along W = N.
        p.have("h_YN: sk_par_steps Y N").by_rewrite_of(
            "h_YW", [p.fact("h_W_N")]
        )

        # Witness halts_par Y.
        p.have(
            "h_at_Y: halts_par Y = "
            "(?N. sk_par_steps Y N /\\ is_normal N)"
        ).by(HALTS_PAR_AT, "Y")
        p.have(
            "h_ex_Y: ?N. sk_par_steps Y N /\\ is_normal N"
        ).by_exists(["N"], "h_YN", "h_norm_N")
        p.thus("halts_par Y").by_eq_mp("h_at_Y", "h_ex_Y")

    # ---- Backward direction ---------------------------------------------
    with p.have(
        "h_bwd: halts_par Y ==> halts_par X"
    ).proof():
        p.assume("h_hY: halts_par Y")
        p.have(
            "h_at_Y: halts_par Y = "
            "(?N. sk_par_steps Y N /\\ is_normal N)"
        ).by(HALTS_PAR_AT, "Y")
        p.have(
            "h_ex_Y: ?N. sk_par_steps Y N /\\ is_normal N"
        ).by_eq_mp("h_at_Y", "h_hY")
        p.choose("N", from_="h_ex_Y")
        p.split("N_eq", "(h_YN, h_norm_N)")

        # X -*> Y, Y -*> N => X -*> N via PAR_STEPS_TRANS.
        p.have(
            "h_conj_XY_YN: sk_par_steps X Y /\\ sk_par_steps Y N"
        ).by_thm(CONJ(p.fact("h_XY"), p.fact("h_YN")))
        p.have("h_XN: sk_par_steps X N").by(
            PAR_STEPS_TRANS, "X", "Y", "N", "h_conj_XY_YN"
        )

        p.have(
            "h_at_X: halts_par X = "
            "(?N. sk_par_steps X N /\\ is_normal N)"
        ).by(HALTS_PAR_AT, "X")
        p.have(
            "h_ex_X: ?N. sk_par_steps X N /\\ is_normal N"
        ).by_exists(["N"], "h_XN", "h_norm_N")
        p.thus("halts_par X").by_eq_mp("h_at_X", "h_ex_X")

    p.thus("halts_par X = halts_par Y").by_iff(
        "h_fwd", "h_bwd"
    )


# ``halts_decider H`` says H is an SK term that decides halting via the
# flipped halting-status output convention (post bullet-migration):
# ``halts_b t  iff  ~halts_b (App_t H t)``.  Per iter_to_bullet.md
# "Output convention change" -- the flipped convention turns the
# diagonal equation ``halts_b d = halts_b (App H d)`` into a P = ~P
# contradiction directly, no K_t / KI_t case-split needed.
HALTS_DECIDER_DEF = define(
    "halts_decider",
    parse_type("nat0 -> bool"),
    "\\H:nat0. is_sk_term H /\\ "
    "         !t:nat0. is_sk_term t ==> "
    "             (halts_b t = ~(halts_b (App_t H t)))",
)
halts_decider = mk_const("halts_decider", [])


@proof
def HALTS_DECIDER_DEF_THM(p):
    """|- !H. halts_decider H =
              (is_sk_term H /\\
               !t. is_sk_term t ==>
                   (halts_b t = ~(halts_b (App_t H t)))).

    Direct unfold of HALTS_DECIDER_DEF via AP_THM + BETA (same shape as
    HALTS_AT for HALTS_DEF).
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GEN
    H_var = Var("H", nat0_ty)
    ap = AP_THM(HALTS_DECIDER_DEF, H_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts_b t = ~(halts_b (App_t H t))))"
    )
    p.thus(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts_b t = ~(halts_b (App_t H t))))"
    ).by_thm(GEN(H_var, spec_th))


# ---------------------------------------------------------------------------
# bullet_eval / bullet_chain -- kernel-level evaluators for sk_bullet.
#
# Given a concrete term `start` over {S_t, K_t, App_t}, build a kernel
# theorem ``|- sk_bullet start = end`` where ``end`` is the fully-evaluated
# parallel-development result of one bullet step.  Composes via TRANS
# chains through SK_BULLET_S_T / SK_BULLET_K_T / SK_BULLET_K_REDEX /
# SK_BULLET_S_REDEX / SK_BULLET_APP_OTHER.
#
# ``bullet_chain`` threads BULLET_ITER_SUC over a sequence of bullet_eval
# results to register ``label: bullet_iter <SUC0-tower n> start = end``
# as a fact in the surrounding proof.
#
# Limitation: inputs must be fully concrete over {S_t, K_t, App_t}.  Free
# variables and folded constants like Omega_t / I_t are not handled
# (SK_BULLET_APP_OTHER's K-shape and S-shape guards can't be discharged
# when the head is opaque -- the structural-clash walk in ``_be_eq_to_F``
# would fail).  Unfold such constants at the call site.
# ---------------------------------------------------------------------------


def _be_eq_to_F(eq_th):
    """Given ``eq_th: asl |- L = R`` over {S_t, K_t, App_t} where L and R
    are structurally distinct, return ``asl |- F``.

    Walks L/R in parallel:
      * Atom-atom clash (one S_t, one K_t): S_T_NEQ_K_T (oriented).
      * Atom-App clash: S_T_NEQ_APP_T or K_T_NEQ_APP_T (oriented).
      * App-App: APP_T_INJ + recurse on the first conjunct; falls back
        to the second conjunct if the first doesn't clash.

    Used to discharge SK_BULLET_APP_OTHER's negation guards.
    """
    from basics import is_const, dest_const
    from tactics import (
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
        NOT_ELIM as _NOT_ELIM,
        NE_SYM as _NE_SYM,
    )

    L, R = dest_eq(eq_th._concl)

    # Atom-atom clash.
    if is_const(L) and is_const(R):
        if L.name == R.name:
            raise HolError(
                f"_be_eq_to_F: atoms identical ({L.name}); not a disequality"
            )
        if L.name == "S_t" and R.name == "K_t":
            return MP(_NOT_ELIM(S_T_NEQ_K_T), eq_th)
        if L.name == "K_t" and R.name == "S_t":
            return MP(_NOT_ELIM(_NE_SYM(S_T_NEQ_K_T)), eq_th)
        raise HolError(
            f"_be_eq_to_F: unsupported atom pair {L.name}, {R.name}"
        )

    # Atom-App clash.  Use atom_neq_app_t lemmas directly.
    if is_const(L):
        rL, rR = _split_app_t(R)
        if rL is None:
            raise HolError(f"_be_eq_to_F: RHS not App_t-shaped: {pp(R)}")
        if L.name == "S_t":
            return MP(_NOT_ELIM(SPECL([rL, rR], S_T_NEQ_APP_T)), eq_th)
        if L.name == "K_t":
            return MP(_NOT_ELIM(SPECL([rL, rR], K_T_NEQ_APP_T)), eq_th)
        raise HolError(f"_be_eq_to_F: unsupported atom {L.name}")

    # App-Atom clash: flip and recurse.
    if is_const(R):
        return _be_eq_to_F(SYM(eq_th))

    # App-App: APP_T_INJ + try first conjunct, fall back to second.
    lL, lR = _split_app_t(L)
    rL, rR = _split_app_t(R)
    if lL is None or rL is None:
        raise HolError(
            f"_be_eq_to_F: unrecognized term shape: {pp(L)} = {pp(R)}"
        )
    pair = MP(SPECL([lL, lR, rL, rR], APP_T_INJ), eq_th)
    # Try left descent first (most clashes live in the head).
    try:
        return _be_eq_to_F(_C1(pair))
    except HolError:
        return _be_eq_to_F(_C2(pair))


def _be_prove_neg_app_pattern(X, Y, bvar_count, pattern_builder):
    """Build ``|- ~(?v1 ... vN. App_t X Y = RHS_template)`` where N is
    ``bvar_count`` and ``pattern_builder(*vs) -> term`` constructs the
    RHS template using the fresh bvars.

    Precondition: ``App_t X Y`` is structurally distinct from
    ``RHS_template[w/v...]`` for the witnesses chosen by ``CHOOSE_WITNESS``
    -- in practice this means ``X`` cannot match the shape of the
    RHS_template's first arg (which is the part of the template that's
    concrete and doesn't depend on bvars).

    Algorithm: ASSUME the nested existential, peel via N applications of
    CHOOSE_WITNESS to get ``App_t X Y = RHS_template[w/v]`` (asl is the
    ASSUMEd existential), then APP_T_INJ + ``_be_eq_to_F`` to derive F,
    then DISCH + NOT_INTRO.
    """
    from tactics import CHOOSE_WITNESS as _CHOOSE_WITNESS
    from basics import is_comb, is_const
    from fusion import ASSUME

    # Build fresh bvars.
    bvar_names = ["a", "b", "c", "d"][:bvar_count]
    bvars = [Var(name, nat0_ty) for name in bvar_names]

    LHS = mk_app(mk_app(App_t, X), Y)
    RHS = pattern_builder(*bvars)
    eq_body = mk_eq(LHS, RHS)

    # Build nested existential: ?v1. ?v2. ... ?vN. eq_body.
    nested_ex = eq_body
    for v in reversed(bvars):
        nested_ex = mk_exists(v, nested_ex)

    # Peel via CHOOSE_WITNESS.  cur_th carries the existential as a hyp.
    cur_th = ASSUME(nested_ex)
    for v in bvars:
        # cur_th._concl should be ?v. body_v.
        ex_concl = cur_th._concl
        if not (
            is_comb(ex_concl)
            and is_const(ex_concl.fun)
            and ex_concl.fun.name == "?"
        ):
            raise HolError(
                f"_be_prove_neg_app_pattern: expected ?, got {pp(ex_concl)}"
            )
        pred = ex_concl.arg  # Abs(v_actual, body)
        cur_th = _CHOOSE_WITNESS(pred, cur_th)
    # cur_th : {nested_ex} |- App_t X Y = RHS[w1...wN].

    # APP_T_INJ to descend to the head clash.  At this point the equation
    # has the form ``App_t X Y = App_t L' R'`` where L', R' may contain
    # SELECT-bound witnesses; _be_eq_to_F handles them since it only
    # descends through structural matches on concrete sub-terms (the X
    # side).
    _, RHS_concrete = dest_eq(cur_th._concl)
    rL, rR = _split_app_t(RHS_concrete)
    if rL is None:
        raise HolError("_be_prove_neg_app_pattern: RHS not App_t-shaped")
    pair = MP(SPECL([X, Y, rL, rR], APP_T_INJ), cur_th)
    # pair : {nested_ex} |- X = rL /\ Y = rR.  Use the first conjunct.
    X_eq = CONJUNCT1(pair)
    F_th = _be_eq_to_F(X_eq)  # {nested_ex} |- F

    from tactics import DISCH as _DISCH, NOT_INTRO as _NOT_INTRO
    return _NOT_INTRO(_DISCH(nested_ex, F_th))


def _be_prove_not_kred(X, Y):
    """|- ~(?a b. App_t X Y = App_t (App_t K_t a) b).

    Precondition: X is concrete and NOT of shape ``App_t K_t _``.
    """
    def pattern(a, b):
        return mk_app(
            mk_app(App_t, mk_app(mk_app(App_t, K_t), a)),
            b,
        )

    return _be_prove_neg_app_pattern(X, Y, 2, pattern)


def _be_prove_not_sred(X, Y):
    """|- ~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c).

    Precondition: X is concrete and NOT of shape ``App_t (App_t S_t _) _``.
    """
    def pattern(a, b, c):
        return mk_app(
            mk_app(
                App_t,
                mk_app(
                    mk_app(App_t, mk_app(mk_app(App_t, S_t), a)),
                    b,
                ),
            ),
            c,
        )

    return _be_prove_neg_app_pattern(X, Y, 3, pattern)


def _be_mk_app_eq(eq_L, eq_R):
    """Given ``eq_L : |- L1 = L2`` and ``eq_R : |- R1 = R2``, build
    ``|- App_t L1 R1 = App_t L2 R2`` via MK_COMB.

    Direct construction (no REWRITE_CONV) so identity-shaped sub-equations
    -- which arise from the opaque-Var fallback in ``_be_synth_bullet`` --
    don't trip REWRITE_CONV's loop detector on rules of shape ``t = t``.
    """
    from fusion import MK_COMB as _MK_COMB
    # MK_COMB(L1=L2, R1=R2) : App_t L1 R1 = App_t L2 R2 (after AP_TERM lift on App_t).
    return _MK_COMB(AP_TERM(App_t, eq_L), eq_R)


def _be_synth_bullet(start):
    """Return ``(end_term, |- sk_bullet start = end_term)`` for concrete
    ``start`` over {S_t, K_t, App_t}.

    Recursion:
      * K-redex ``App (App K X) Y``: SK_BULLET_K_REDEX gives
        ``sk_bullet (App (App K X) Y) = sk_bullet X``; recurse on X and
        TRANS.  Note this collapses through K-redexes eagerly.
      * S-redex ``App (App (App S X) Y) Z``: SK_BULLET_S_REDEX gives
        the explicit ``App (App (sb X) (sb Z)) (App (sb Y) (sb Z))`` RHS;
        recurse on X, Y, Z; REWRITE_CONV rewrites the four sk_bullet
        chunks on the RHS using the recursive results; TRANS.
      * Atom S_t / K_t: SK_BULLET_S_T / SK_BULLET_K_T.
      * App-other: discharge K-shape and S-shape guards via
        ``_be_prove_not_kred`` / ``_be_prove_not_sred``; MP with
        SK_BULLET_APP_OTHER; recurse on both children; REWRITE_CONV
        on the RHS chunks; TRANS.

    Raises ``HolError`` if ``start`` doesn't match any pattern (e.g. a
    free Var or a folded constant like ``Omega_t``).
    """
    from basics import is_const

    # K-redex first (most-specific).
    Kred = _pc_try_K_redex(start)
    if Kred is not None:
        X, Y = Kred
        head_eq = SPECL([X, Y], SK_BULLET_K_REDEX)
        # head_eq : sk_bullet (App (App K X) Y) = sk_bullet X.
        _, X_eq = _be_synth_bullet(X)
        # X_eq : sk_bullet X = X_norm.
        composed = TRANS(head_eq, X_eq)
        return (rand(composed._concl), composed)

    # S-redex.
    Sred = _pc_try_S_redex(start)
    if Sred is not None:
        X, Y, Z = Sred
        head_eq = SPECL([X, Y, Z], SK_BULLET_S_REDEX)
        # head_eq RHS = App (App (sk_bullet X) (sk_bullet Z))
        #               (App (sk_bullet Y) (sk_bullet Z)).
        _, X_eq = _be_synth_bullet(X)
        _, Y_eq = _be_synth_bullet(Y)
        _, Z_eq = _be_synth_bullet(Z)
        # Build the RHS rewrite via direct MK_COMB compositions rather
        # than REWRITE_CONV, since identity-shaped X_eq / Y_eq / Z_eq
        # (from the opaque fallback) would loop REWRITE_CONV's
        # _bottom_up at sk_bullet H sub-positions.
        rhs_eq = _be_mk_app_eq(
            _be_mk_app_eq(X_eq, Z_eq),
            _be_mk_app_eq(Y_eq, Z_eq),
        )
        composed = TRANS(head_eq, rhs_eq)
        return (rand(composed._concl), composed)

    # Atom leaves.
    if is_const(start):
        if start.name == "S_t":
            return (S_t, SK_BULLET_S_T)
        if start.name == "K_t":
            return (K_t, SK_BULLET_K_T)
        raise HolError(
            f"_be_synth_bullet: unsupported atom {start.name}; "
            "unfold folded constants (Omega_t, I_t, ...) at the call site"
        )

    # App-other.
    App = _pc_dest_App_t(start)
    if App is not None:
        X, Y = App
        not_K = _be_prove_not_kred(X, Y)
        not_S = _be_prove_not_sred(X, Y)
        head_inst = SPECL([X, Y], SK_BULLET_APP_OTHER)
        head_eq = MP(head_inst, CONJ(not_K, not_S))
        # head_eq RHS = App (sk_bullet X) (sk_bullet Y).
        _, X_eq = _be_synth_bullet(X)
        _, Y_eq = _be_synth_bullet(Y)
        rhs_eq = _be_mk_app_eq(X_eq, Y_eq)
        composed = TRANS(head_eq, rhs_eq)
        return (rand(composed._concl), composed)

    # Opaque fallback: free Var or folded constant.  Return REFL(sk_bullet
    # start) so that ``sk_bullet start`` carries through as a symbolic
    # chunk.  This lets bullet trajectories of H-containing terms (e.g.
    # DIAG_TERM's diagonal) compute to a closed form modulo opaque
    # ``sk_bullet H`` residuals -- the App-other and K/S guards above
    # discharge cleanly so long as the *head* of each App is concrete
    # over {S_t, K_t, App_t}, even if leaf positions are opaque.
    #
    # DSL friction: when ``start`` is a free Var, the App-other K-shape
    # guard ``~(?a b. App X start = App (App K_t a) b)`` for any wrapping
    # App goes through because the head clash is on the *first* arg side
    # (X vs App K_t a, both concrete on the X side), not on the leaf
    # ``start`` side -- ``_be_eq_to_F``'s CONJUNCT1 path picks the head
    # branch before ever inspecting ``start``.
    fallback = mk_app(sk_bullet, start)
    return (fallback, REFL(fallback))


def bullet_eval(p, start, *, label):
    """Register a fact ``label: sk_bullet start = end`` for a concrete
    ``start``.  Returns the kernel ``end`` term.

    Example::

        end = bullet_eval(p, "App_t (App_t K_t S_t) K_t", label="h_step")
        # registers h_step: sk_bullet (App_t (App_t K_t S_t) K_t) = S_t
        # returns S_t (kernel term).

    Use ``bullet_chain`` instead when you need a multi-step
    ``bullet_iter`` chain rather than a single sk_bullet equation.
    """
    start_kt = p._parse(start) if isinstance(start, str) else start
    end_kt, th = _be_synth_bullet(start_kt)
    p.have(f"{label}: {pp(th._concl)}").by_thm(th)
    return end_kt


class _BulletChain:
    """Context manager assembling a ``bullet_iter <SUC0-tower n> start = end``
    equation by chaining n single-bullet steps.

    See ``bullet_chain`` for usage; ``_close`` builds the chain by induction
    on the step count using BULLET_ITER_ZERO + BULLET_ITER_SUC and the
    per-step ``sk_bullet T_i = T_{i+1}`` equations from ``_be_synth_bullet``.
    """

    def __init__(self, p, start, label):
        self.p = p
        self.label = label
        self.start = (
            p._parse(start) if isinstance(start, str) else start
        )
        self.current = self.start
        self.steps = []  # list of (start_i, end_i, |- sk_bullet start_i = end_i)
        self._closed = False

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc_type is None and not self._closed:
            self._close()
        return False

    def step(self):
        """Apply one ``sk_bullet`` step.  Returns the resulting kernel term."""
        end_kt, eq_th = _be_synth_bullet(self.current)
        self.steps.append((self.current, end_kt, eq_th))
        self.current = end_kt
        return end_kt

    def _close(self):
        # Build by induction over self.steps:
        #   cur_eq_i : bullet_iter <SUC0^i 0> start = end_i  (with end_0 = start).
        # Inductive step from i to i+1:
        #   BULLET_ITER_SUC at (SUC0^i 0, start):
        #     bullet_iter (SUC0 (SUC0^i 0)) start = sk_bullet (bullet_iter (SUC0^i 0) start)
        #   AP_TERM(sk_bullet, cur_eq_i):
        #     sk_bullet (bullet_iter (SUC0^i 0) start) = sk_bullet end_i
        #   eq_th_{i+1} from steps[i]:
        #     sk_bullet end_i = end_{i+1}
        # TRANS them all.
        start_t = self.start
        cur_tower = ZERO
        # Seed: bullet_iter 0 start = start.
        cur_eq = SPEC(start_t, BULLET_ITER_ZERO)
        for (_s_i, _e_i, eq_i) in self.steps:
            iter_suc = SPECL([cur_tower, start_t], BULLET_ITER_SUC)
            # iter_suc : bullet_iter (SUC0 cur_tower) start
            #            = sk_bullet (bullet_iter cur_tower start)
            sb_eq = AP_TERM(sk_bullet, cur_eq)
            # sb_eq : sk_bullet (bullet_iter cur_tower start) = sk_bullet s_i
            #         (where s_i = the previous step's start, == cur_eq's RHS)
            cur_eq = TRANS(TRANS(iter_suc, sb_eq), eq_i)
            cur_tower = mk_suc0(cur_tower)
        self.p.have(f"{self.label}: {pp(cur_eq._concl)}").by_thm(cur_eq)
        self._closed = True


def bullet_chain(p, start, *, label):
    """Open a ``bullet_iter`` chain starting at ``start``.

    Each ``c.step()`` advances one ``sk_bullet`` step (auto-evaluating via
    ``_be_synth_bullet``).  On context exit, registers a fact
    ``label: bullet_iter <SUC0-tower n> start = end`` where ``n`` is the
    number of ``step()`` calls and ``end`` is the final term.

    Example::

        with bullet_chain(p, "App_t (App_t K_t S_t) K_t", label="h_4") as c:
            c.step()  # sk_bullet 1
            c.step()  # sk_bullet 2
            c.step()
            c.step()
        # registers h_4: bullet_iter (SUC0 (SUC0 (SUC0 (SUC0 0))))
        #                   (App_t (App_t K_t S_t) K_t) = <end>
    """
    return _BulletChain(p, start, label)


_DIAG_I = "App_t (App_t S_t K_t) K_t"
_DIAG_SII = f"App_t (App_t S_t ({_DIAG_I})) ({_DIAG_I})"
_DIAG_KH = "App_t K_t H"
_DIAG_E = f"App_t (App_t S_t ({_DIAG_KH})) ({_DIAG_SII})"
_DIAG_D = f"App_t ({_DIAG_E}) ({_DIAG_E})"


@proof
def DIAG_TERM(p):
    """|- !H. is_sk_term H ==>
              ?d. is_sk_term d /\\ sk_par_steps d (App_t H d).

    Classical Curry diagonal under parallel reduction.  Witness with I_t
    unfolded inline as ``(S_t K_t) K_t`` so ``par_chain``'s structural
    synth sees the S-redex shape at each ``I_unf e`` site (the
    existential over d doesn't care that I_unf = I_t definitionally)::

        I_unf := App_t (App_t S_t K_t) K_t
        SII   := App_t (App_t S_t I_unf) I_unf
        KH    := App_t K_t H
        e     := App_t (App_t S_t KH) SII        (* S (K H) SII *)
        d     := App_t e e

    4-link par-step chain (each link a single parallel-reduction step;
    par_chain synth emits PAR_S / PAR_K / PAR_APP from the start/end
    shapes, REFL on H carries through every link)::

        d --> (KH e)(SII e)                          [outer S]
          --> H ((I_unf e)(I_unf e))                 [PAR_K on left, PAR_S on right]
          --> H (((K e)(K e))((K e)(K e)))           [2 x I_unf-as-SKK fires PAR_S]
          --> H (e e) = App_t H d                    [4 x parallel K]

    History (see iter_to_bullet.md "Post-spike audit"):
    commit 01ac895 attempted to migrate this proof to a bullet form
    `bullet_iter 4 d = App H d`, on the spike-validated trajectory for
    atomic H.  Composite-H stress testing (EXP 5/6 in outside/sk_par.py)
    falsified the equation under `is_sk_term H` -- for H = App K K,
    the trajectory collapses at iter 3; for H = I = SKK, it cycles
    period-4 without ever reaching App H d.  Under Option C the
    diagonal is back in par form (the calculus that has PAR_REFL on H,
    which is precisely the "keep H unreduced" operation bullet's
    eager-everywhere semantics forbids), and the par-to-bullet bridge
    is provided downstream by `HALTS_B_IFF_HALTS_PAR` (not yet
    shipped).
    """
    _I = _DIAG_I
    _SII = _DIAG_SII
    _KH = _DIAG_KH
    _E = _DIAG_E
    _D = _DIAG_D

    p.goal(
        "!H. is_sk_term H ==> "
        "    ?d. is_sk_term d /\\ sk_par_steps d (App_t H d)"
    )
    p.fix("H")
    p.assume("h_is_sk_H: is_sk_term H")

    # ---- (1) is_sk_term cascade for d. -----------------------------------
    p.have("h_SK: is_sk_term (App_t S_t K_t)").by_match(
        IS_SK_TERM_APP, IS_SK_TERM_S, IS_SK_TERM_K
    )
    p.have(f"h_I: is_sk_term ({_I})").by_match(
        IS_SK_TERM_APP, "h_SK", IS_SK_TERM_K
    )
    p.have(f"h_S_I: is_sk_term (App_t S_t ({_I}))").by_match(
        IS_SK_TERM_APP, IS_SK_TERM_S, "h_I"
    )
    p.have(f"h_SII: is_sk_term ({_SII})").by_match(
        IS_SK_TERM_APP, "h_S_I", "h_I"
    )
    p.have(f"h_KH: is_sk_term ({_KH})").by_match(
        IS_SK_TERM_APP, IS_SK_TERM_K, "h_is_sk_H"
    )
    p.have(f"h_S_KH: is_sk_term (App_t S_t ({_KH}))").by_match(
        IS_SK_TERM_APP, IS_SK_TERM_S, "h_KH"
    )
    p.have(f"h_e: is_sk_term ({_E})").by_match(
        IS_SK_TERM_APP, "h_S_KH", "h_SII"
    )
    p.have(f"h_is_sk_d: is_sk_term ({_D})").by_match(
        IS_SK_TERM_APP, "h_e", "h_e"
    )

    # ---- (2) 4-link par-step chain. --------------------------------------
    _T1 = f"App_t (App_t ({_KH}) ({_E})) (App_t ({_SII}) ({_E}))"
    _I_E = f"App_t ({_I}) ({_E})"
    _T2 = f"App_t H (App_t ({_I_E}) ({_I_E}))"
    _KE = f"App_t K_t ({_E})"
    _KE_KE = f"App_t ({_KE}) ({_KE})"
    _T3 = f"App_t H (App_t ({_KE_KE}) ({_KE_KE}))"
    _T4 = f"App_t H ({_D})"

    with par_chain(p, _D, label="h_par") as c:
        c.link(_T1)
        c.link(_T2)
        c.link(_T3)
        c.link(_T4)

    # ---- (3) Witness d. --------------------------------------------------
    p.thus(
        "?d. is_sk_term d /\\ sk_par_steps d (App_t H d)"
    ).by_exists([_D], "h_is_sk_d", "h_par")


@proof
def OMEGA_T_NOT_FIXED(p):
    """|- !n. ~(sk_step (sk_iter n Omega_t) = sk_iter n Omega_t).

    Pointwise corollary of OMEGA_NON_HALTING: if any iterate of
    Omega were sk_step-fixed it would be normal by IS_NORMAL_DEF,
    contradicting ``~halts Omega_t`` via the HALTS_AT witness.
    """
    p.goal("!n. ~(sk_step (sk_iter n Omega_t) = sk_iter n Omega_t)")
    p.fix("n")
    with p.suppose(
        "h_fixed: sk_step (sk_iter n Omega_t) = sk_iter n Omega_t"
    ):
        p.have("h_norm: is_normal (sk_iter n Omega_t)").by_unfold(
            "h_fixed", IS_NORMAL_DEF
        )
        p.have("h_ex: ?m. is_normal (sk_iter m Omega_t)").by_witness(
            "n", "h_norm"
        )
        p.have("h_halts: halts Omega_t").by_eq_mp(
            SPEC(p._parse("Omega_t"), HALTS_AT), "h_ex"
        )
        p.absurd().by_conj("h_halts", OMEGA_NON_HALTING)


@proof
def SK_ITER_K_OMEGA_SHAPE(p):
    """|- !n. sk_iter n (App_t K_t Omega_t) = App_t K_t (sk_iter n Omega_t).

    ``K_t Omega`` is single-arg K (not a redex); leftmost-outermost
    ``sk_step`` descends right indefinitely.  Each step preserves the
    ``App_t K_t _`` shape since SK_STEP_K_DESC_RIGHT fires whenever
    the right child is non-fixed -- and Omega's iterates are all
    non-fixed by OMEGA_T_NOT_FIXED.
    """
    p.goal(
        "!n. sk_iter n (App_t K_t Omega_t) = App_t K_t (sk_iter n Omega_t)"
    )
    with p.induction("n"):
        with p.base():
            p.thus(
                "sk_iter 0 (App_t K_t Omega_t) = App_t K_t (sk_iter 0 Omega_t)"
            ).by_rewrite([SK_ITER_ZERO])
        with p.step("IH"):
            # IH:   sk_iter n (App_t K_t Omega_t) = App_t K_t (sk_iter n Omega_t).
            # Goal: sk_iter (SUC0 n) (App_t K_t Omega_t)
            #         = App_t K_t (sk_iter (SUC0 n) Omega_t).
            p.have(
                "h_not_fixed: "
                "~(sk_step (sk_iter n Omega_t) = sk_iter n Omega_t)"
            ).by(OMEGA_T_NOT_FIXED, "n")
            # SK_STEP_K_DESC_RIGHT at Z = sk_iter n Omega_t.
            p.have(
                "h_desc: sk_step (App_t K_t (sk_iter n Omega_t)) "
                "      = App_t K_t (sk_step (sk_iter n Omega_t))"
            ).by(SK_STEP_K_DESC_RIGHT, "sk_iter n Omega_t", "h_not_fixed")
            # Rewrite chain:
            #   sk_iter (SUC n) (App K Omega)
            #     = sk_step (sk_iter n (App K Omega))   [SK_ITER_SUC]
            #     = sk_step (App K (sk_iter n Omega))   [IH]
            #     = App K (sk_step (sk_iter n Omega))   [h_desc]
            #     = App K (sk_iter (SUC n) Omega)       [SYM SK_ITER_SUC]
            p.thus(
                "sk_iter (SUC0 n) (App_t K_t Omega_t) "
                "= App_t K_t (sk_iter (SUC0 n) Omega_t)"
            ).by_rewrite([SK_ITER_SUC, "IH", "h_desc"])


@proof
def HALTS_K_OMEGA_FALSE(p):
    """|- ~halts (App_t K_t Omega_t).

    ``K_t Omega`` is a one-arg K (not a K-redex; K-redex needs two
    args), so leftmost-outermost ``sk_step`` descends right into
    Omega indefinitely.  If a witness ``n`` made
    ``sk_iter n (App_t K_t Omega_t)`` normal, by SK_ITER_K_OMEGA_SHAPE
    that iterate equals ``App_t K_t (sk_iter n Omega_t)``, so
    ``sk_step (App_t K_t (sk_iter n Omega_t)) = App_t K_t (sk_iter n Omega_t)``.
    SK_STEP_K_DESC_RIGHT rewrites the LHS to
    ``App_t K_t (sk_step (sk_iter n Omega_t))``; APP_T_INJ peels the
    common ``App_t K_t`` and yields ``sk_step (sk_iter n Omega_t)
    = sk_iter n Omega_t``, contradicting OMEGA_T_NOT_FIXED.
    """
    from tactics import CONJUNCT2 as _C2
    p.goal("~halts (App_t K_t Omega_t)")
    with p.suppose("h_halts: halts (App_t K_t Omega_t)"):
        # Extract a normal iterate.
        p.have(
            "h_ex: ?n. is_normal (sk_iter n (App_t K_t Omega_t))"
        ).by_eq_mp(
            SPEC(p._parse("App_t K_t Omega_t"), HALTS_AT), "h_halts"
        )
        p.choose("n", from_="h_ex")
        # n_eq: is_normal (sk_iter n (App_t K_t Omega_t)).

        # Reshape the iterate.
        p.have(
            "h_shape: sk_iter n (App_t K_t Omega_t) "
            "       = App_t K_t (sk_iter n Omega_t)"
        ).by(SK_ITER_K_OMEGA_SHAPE, "n")
        p.have(
            "h_norm_K: is_normal (App_t K_t (sk_iter n Omega_t))"
        ).by_eq_mp(AP_TERM(is_normal, p.fact("h_shape")), "n_eq")
        # Unfold is_normal to sk_step-fixed form.
        p.have(
            "h_fixed_K: sk_step (App_t K_t (sk_iter n Omega_t)) "
            "         = App_t K_t (sk_iter n Omega_t)"
        ).by_unfold("h_norm_K", IS_NORMAL_DEF)

        # The Omega iterate itself is not sk_step-fixed.
        p.have(
            "h_not_fixed: "
            "~(sk_step (sk_iter n Omega_t) = sk_iter n Omega_t)"
        ).by(OMEGA_T_NOT_FIXED, "n")

        # Descend-right rewrite of the LHS.
        p.have(
            "h_desc: sk_step (App_t K_t (sk_iter n Omega_t)) "
            "      = App_t K_t (sk_step (sk_iter n Omega_t))"
        ).by(SK_STEP_K_DESC_RIGHT, "sk_iter n Omega_t", "h_not_fixed")

        # Combine: App K (sk_step (sk_iter n Omega)) = App K (sk_iter n Omega).
        p.have(
            "h_eq: App_t K_t (sk_step (sk_iter n Omega_t)) "
            "    = App_t K_t (sk_iter n Omega_t)"
        ).by_thm(TRANS(SYM(p.fact("h_desc")), p.fact("h_fixed_K")))

        # Peel the common App_t K_t with APP_T_INJ.
        p.have(
            "h_inj: K_t = K_t /\\ "
            "       sk_step (sk_iter n Omega_t) = sk_iter n Omega_t"
        ).by(
            APP_T_INJ,
            "K_t", "sk_step (sk_iter n Omega_t)",
            "K_t", "sk_iter n Omega_t",
            "h_eq",
        )
        p.have(
            "h_inner: sk_step (sk_iter n Omega_t) = sk_iter n Omega_t"
        ).by_thm(_C2(p.fact("h_inj")))

        p.absurd().by_conj("h_not_fixed", "h_inner")


@proof
def HALTS_KI_OMEGA_TRUE(p):
    """|- halts (App_t KI_t Omega_t).

    ``KI_t Omega = App_t (App_t K_t I_t) Omega_t`` after unfolding
    ``KI_T_DEF``, a top-level K-redex with x=I_t, y=Omega.  Fires in
    one ``sk_step`` to ``I_t``, which is normal (``IS_NORMAL_I_T``).
    Witness n = SUC0 0.
    """
    p.goal("halts (App_t KI_t Omega_t)")

    KIO = "App_t KI_t Omega_t"
    KIO_unfolded = "App_t (App_t K_t I_t) Omega_t"

    # One head K-step at (I_t, Omega_t).
    p.have(
        f"kstep: sk_step ({KIO_unfolded}) = I_t"
    ).by(SK_STEP_K, "I_t", "Omega_t")

    # sk_iter (SUC0 0) (App_t KI_t Omega_t)
    #   = sk_step (sk_iter 0 (App_t KI_t Omega_t))   [SK_ITER_SUC]
    #   = sk_step (App_t KI_t Omega_t)               [SK_ITER_ZERO]
    #   = sk_step (App_t (App_t K_t I_t) Omega_t)    [KI_T_DEF]
    #   = I_t                                         [kstep]
    p.have(
        f"iter_eq: sk_iter (SUC0 0) ({KIO}) = I_t"
    ).by_rewrite([SK_ITER_SUC, SK_ITER_ZERO, KI_T_DEF, p.fact("kstep")])

    # IS_NORMAL_I_T + iter_eq -> is_normal of the iter form.
    p.have(
        f"norm_iter: is_normal (sk_iter (SUC0 0) ({KIO}))"
    ).by_thm(
        EQ_MP(
            SYM(AP_TERM(is_normal, p.fact("iter_eq"))),
            IS_NORMAL_I_T,
        )
    )
    # DSL friction: ``by_eq_mp(AP_TERM(is_normal, "iter_eq"), IS_NORMAL_I_T)``
    # would be a cleaner one-liner, but ``by_eq_mp``'s sym-tolerance
    # is on the FACT side (matching RHS-form facts to LHS-form goals);
    # here the eq_th itself comes out RHS-of-fact = LHS-of-goal, so we
    # SYM it manually before EQ_MP.

    # HALTS_AT-witness path: ?n. is_normal (sk_iter n KIO) -> halts KIO.
    p.have(
        f"ex_norm: ?n. is_normal (sk_iter n ({KIO}))"
    ).by_witness("SUC0 0", "norm_iter")
    p.thus(f"halts ({KIO})").by_eq_mp(
        SPEC(p._parse(KIO), HALTS_AT), "ex_norm"
    )


@proof
def DIAGONAL_TERM_EXISTS(p):
    """|- !H. is_sk_term H ==>
              ?d. is_sk_term d /\\ halts_b d = halts_b (App_t H d).

    Halts-form diagonal in the new (bullet) convention.  Combines:

      * DIAG_TERM           : the par-form Curry diagonal
                              ``sk_par_steps d (App_t H d)``.
      * HALTS_PAR_INVARIANT : par-step chains preserve halts_par.
      * HALTS_B_IFF_HALTS_PAR : the bullet/par halt-bridge.

    Pipeline: DIAG_TERM gives ``d`` and ``sk_par_steps d (App_t H d)``.
    Apply HALTS_PAR_INVARIANT to get ``halts_par d = halts_par (App_t
    H d)``.  Sandwich with HALTS_B_IFF_HALTS_PAR (on both sides) to
    convert each ``halts_par`` to ``halts_b``.  Witness d.
    """
    p.goal(
        "!H. is_sk_term H ==> "
        "    ?d. is_sk_term d /\\ halts_b d = halts_b (App_t H d)"
    )
    p.fix("H")
    p.assume("h_is_sk_H: is_sk_term H")

    # Pull in the par-form diagonal witness.
    p.have(
        "h_diag: ?d. is_sk_term d /\\ sk_par_steps d (App_t H d)"
    ).by(DIAG_TERM, "H", "h_is_sk_H")
    p.choose("d", from_="h_diag")
    p.split("d_eq", "(h_is_sk_d, h_par)")

    # halts_par d = halts_par (App H d) via par-step invariance.
    p.have(
        "h_par_eq: halts_par d = halts_par (App_t H d)"
    ).by(HALTS_PAR_INVARIANT, "d", "App_t H d", "h_par")

    # Sandwich with the bullet/par halt-bridge.
    # halts_b d = halts_par d.
    p.have("h_b_d: halts_b d = halts_par d").by_thm(
        SPEC(p._parse("d"), HALTS_B_IFF_HALTS_PAR)
    )
    # halts_b (App H d) = halts_par (App H d).
    p.have(
        "h_b_Hd: halts_b (App_t H d) = halts_par (App_t H d)"
    ).by_thm(SPEC(p._parse("App_t H d"), HALTS_B_IFF_HALTS_PAR))
    # Chain: halts_b d = halts_par d = halts_par (App H d) = halts_b (App H d).
    p.have("h_step1: halts_b d = halts_par (App_t H d)").by_trans(
        "h_b_d", "h_par_eq"
    )
    p.have(
        "h_halts_eq: halts_b d = halts_b (App_t H d)"
    ).by_trans("h_step1", SYM(p.fact("h_b_Hd")))

    p.thus(
        "?d. is_sk_term d /\\ halts_b d = halts_b (App_t H d)"
    ).by_exists(["d"], "h_is_sk_d", "h_halts_eq")


@proof
def HALTING_UNDECIDABLE(p):
    """|- ~ ?H. halts_decider H.

    THE THEOREM.  No SK combinator decides halting.

    Proof (the diagonal sketched above):

      Assume H with halts_decider H.  Build
        f := an SK term satisfying  App_t f x -->* App_t (App_t (App_t H x)
                                                            Omega_t) K_t
             for all x   (via bracket abstraction on x).
        d := App_t Y_t f.

      By Y_FIXED_POINT:  d -->* App_t f d
                            -->* App_t (App_t (App_t H d) Omega_t) K_t.

      Case 1.  halts d.
        Then App_t H d -->* K_t (decider hypothesis), so
          d -->* App_t (App_t K_t Omega_t) K_t -->* Omega_t
        (by CHURCH_TRUE_REDUCES).  By HALTING_REDUCTION_PRESERVED,
        halts Omega_t -- contradicting OMEGA_NON_HALTING.

      Case 2.  ~halts d.
        Then App_t H d -->* KI_t, so
          d -->* App_t (App_t KI_t Omega_t) K_t -->* K_t
        (by CHURCH_FALSE_REDUCES).  K_t is normal (IS_NORMAL_K), so
        halts d via HALTING_REDUCTION_PRESERVED -- contradicting
        the case hypothesis.

      Either branch contradicts; hence no such H.

    The "d --> Omega_t / K_t" steps are packaged into DIAGONAL_TERM_EXISTS
    (still a stub); HALTING_REDUCTION_PRESERVED, CHURCH_*_REDUCES,
    HALTS_DECIDER_DEF_THM, OMEGA_NON_HALTING, IS_NORMAL_K, HALTS_AT,
    EXCLUDED_MIDDLE are all live.  Once DIAGONAL_TERM_EXISTS is
    discharged the diagonal closes without further holes.
    """
    from classical import EXCLUDED_MIDDLE

    p.goal("~ (?H. halts_decider H)")
    with p.suppose("h_ex: ?H. halts_decider H"):
        p.choose("H", from_="h_ex")
        # H_eq : halts_decider H.

        # ---- Unfold the (flipped, bullet-form) halts_decider spec. ----
        p.have(
            "h_thm: halts_decider H = "
            "       (is_sk_term H /\\ "
            "        !t. is_sk_term t ==> "
            "            (halts_b t = ~(halts_b (App_t H t))))"
        ).by(HALTS_DECIDER_DEF_THM, "H")
        p.have(
            "h_unf: is_sk_term H /\\ "
            "       !t. is_sk_term t ==> "
            "           (halts_b t = ~(halts_b (App_t H t)))"
        ).by_eq_mp("h_thm", "H_eq")
        p.split("h_unf", "(h_is_sk_H, h_decides)")

        # ---- Diagonal term d (halts_b form). --------------------------
        p.have(
            "h_diag: ?d. is_sk_term d /\\ "
            "        halts_b d = halts_b (App_t H d)"
        ).by(DIAGONAL_TERM_EXISTS, "H", "h_is_sk_H")
        p.choose("d", from_="h_diag")
        p.split("d_eq", "(h_is_sk_d, h_dd_eq)")

        # ---- Decider's promise specialised at t := d. -----------------
        p.have(
            "h_dec_d: halts_b d = ~halts_b (App_t H d)"
        ).by("h_decides", "d", "h_is_sk_d")

        # ---- Compose to a P = ~P contradiction at App_t H d. ----------
        # h_dd_eq  : halts_b d           = halts_b (App_t H d)
        # h_dec_d  : halts_b d           = ~halts_b (App_t H d)
        # SYM h_dd_eq + h_dec_d :
        #   halts_b (App_t H d) = ~halts_b (App_t H d)
        p.have(
            "h_pne: halts_b (App_t H d) = ~halts_b (App_t H d)"
        ).by_trans(SYM(p.fact("h_dd_eq")), "h_dec_d")

        # ---- Discharge via EXCLUDED_MIDDLE on halts_b (App_t H d). ----
        with p.cases_on(EXCLUDED_MIDDLE, "halts_b (App_t H d)"):
            with p.case("h_yes: halts_b (App_t H d)"):
                p.have(
                    "h_no: ~halts_b (App_t H d)"
                ).by_eq_mp("h_pne", "h_yes")
                p.absurd().by_conj("h_yes", "h_no")
            with p.case("h_no: ~halts_b (App_t H d)"):
                p.have(
                    "h_yes: halts_b (App_t H d)"
                ).by_eq_mp(SYM(p.fact("h_pne")), "h_no")
                p.absurd().by_conj("h_yes", "h_no")


# ---------------------------------------------------------------------------
# Stage 7 -- corollaries.
# ---------------------------------------------------------------------------


@proof
def HALTS_NOT_SK_REPRESENTABLE(p):
    """|- ~ ?H. is_sk_term H /\\
                !t. is_sk_term t ==>
                    (halts_b t = ~(halts_b (App_t H t))).

    HALTING_UNDECIDABLE, restated as non-existence of an SK term
    deciding bullet halting under the flipped output convention.
    Immediate from HALTING_UNDECIDABLE + HALTS_DECIDER_DEF_THM: any
    H satisfying the unfolded predicate also satisfies
    ``halts_decider H``, witnessing the existential refuted by
    HALTING_UNDECIDABLE.
    """
    p.goal(
        "~ (?H. is_sk_term H /\\ "
        "       !t. is_sk_term t ==> "
        "           (halts_b t = ~(halts_b (App_t H t))))"
    )
    with p.suppose(
        "h_ex: ?H. is_sk_term H /\\ "
        "      !t. is_sk_term t ==> "
        "          (halts_b t = ~(halts_b (App_t H t)))"
    ):
        p.choose("H", from_="h_ex")
        # H_eq : is_sk_term H /\ ...   (the unfolded body at H).
        # HALTS_DECIDER_DEF_THM at H: halts_decider H = (unfolded body).
        p.have(
            "h_thm: halts_decider H = "
            "       (is_sk_term H /\\ "
            "        !t. is_sk_term t ==> "
            "            (halts_b t = ~(halts_b (App_t H t))))"
        ).by(HALTS_DECIDER_DEF_THM, "H")
        # Fold H_eq back into halts_decider H via SYM-tolerant by_eq_mp.
        p.have("h_hd: halts_decider H").by_eq_mp("h_thm", "H_eq")
        p.have("h_ex_hd: ?H. halts_decider H").by_witness("H", "h_hd")
        # HALTING_UNDECIDABLE : ~?H. halts_decider H.  Contradict.
        p.absurd().by_conj(HALTING_UNDECIDABLE, "h_ex_hd")


# ---------------------------------------------------------------------------
# Estimated line budget (once stubs are discharged):
#
#   Stage 0 (SK terms + is_sk_term)          : ~50  lines
#   Stage 1 (sk_step + is_normal)            : ~80  lines (spine analysis)
#   Stage 2 (sk_iter + halts)                : ~30  lines
#   Stage 3 (I, KI, Omega + OMEGA_NON_HALT)  : ~40  lines
#   Stage 4 (Y + fixed-point thm)            : ~30  lines
#   Stage 5 (Church-bool selectors)          : ~20  lines
#   Stage 6 (diagonal + HALTING_UNDECIDABLE) : ~50  lines
#   Stage 7 (corollaries)                    : ~10  lines
#   -----------------------------------------------------
#   Total                                    : ~310 lines
#
# Comparison: Norrish's HOL4 ``lambdaTheory`` halting development is
# ~2k lines because it carries the lambda-calculus substitution
# infrastructure.  Replacing lambda with SK removes that piece outright;
# the diagonal portion is the same size.
# ---------------------------------------------------------------------------
