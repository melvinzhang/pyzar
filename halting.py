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

from fusion import Var, new_constant
from basics import mk_const, mk_app, mk_abs, rand
from parser import define, parse_type, add_const
from nat0 import nat0_ty, ZERO, mk_suc0
from nat0_order import define_wf_lt
from proof import proof, define_with_at
from tactics import REFL, SPEC, SPECL, SYM, EQ_MP, DISJ1, DISJ2, CONJ, EXISTS, MP
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
def I_T_REDUCES(p):
    """|- !x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x.

    I = SKK; in two head steps:
        sk_iter 0 (I x) = I x = App_t (App_t (App_t S_t K_t) K_t) x
        sk_iter 1 (I x) = sk_step (I x) = App_t (App_t K_t x) (App_t K_t x)
                                          (by SK_STEP_S at K_t, K_t, x)
        sk_iter 2 (I x) = sk_step (App_t (App_t K_t x) (App_t K_t x)) = x
                                          (by SK_STEP_K at x, App_t K_t x)

    The is_sk_term hypothesis isn't actually used by the head-redex
    rules -- they fire on any term of the right shape -- but it's
    carried in the goal for interface consistency with downstream.
    """
    from tactics import AP_TERM, SPEC, SPECL, TRANS, SYM

    p.goal("!x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x")
    p.fix("x")
    p.assume("h_st: is_sk_term x")  # unused (see docstring)

    # Step A: sk_iter 0 (App_t I_t x) = App_t I_t x.
    p.have("h_iter0: sk_iter 0 (App_t I_t x) = App_t I_t x").by(
        SK_ITER_ZERO, "App_t I_t x"
    )

    # Step B: sk_iter 1 = sk_step (sk_iter 0 ...) -- using SK_ITER_SUC at n=0.
    p.have(
        "h_iter1_raw: sk_iter (SUC0 0) (App_t I_t x) "
        "= sk_step (sk_iter 0 (App_t I_t x))"
    ).by(SK_ITER_SUC, "0", "App_t I_t x")
    # Substitute Step A into the RHS to collapse the inner iter.
    p.have(
        "h_iter1: sk_iter (SUC0 0) (App_t I_t x) = sk_step (App_t I_t x)"
    ).by_rewrite_of("h_iter1_raw", ["h_iter0"])

    # Step C: sk_step (App_t I_t x) = App_t (App_t K_t x) (App_t K_t x).
    # Unfold I_t via I_T_DEF to recognize the S-redex shape, then SK_STEP_S.
    p.have(
        "h_S: sk_step (App_t (App_t (App_t S_t K_t) K_t) x) "
        "= App_t (App_t K_t x) (App_t K_t x)"
    ).by(SK_STEP_S, "K_t", "K_t", "x")
    # Fold (App_t S_t K_t) K_t back to I_t via SYM(I_T_DEF).
    p.have(
        "h_step_I: sk_step (App_t I_t x) "
        "= App_t (App_t K_t x) (App_t K_t x)"
    ).by_rewrite_of("h_S", [SYM(I_T_DEF)])

    # Compose B + C: sk_iter 1 (App_t I_t x) = App_t (App_t K_t x) (App_t K_t x).
    p.have(
        "h_iter1_final: sk_iter (SUC0 0) (App_t I_t x) "
        "= App_t (App_t K_t x) (App_t K_t x)"
    ).by_thm(TRANS(p.fact("h_iter1"), p.fact("h_step_I")))

    # Step D: sk_iter 2 = sk_step (sk_iter 1 ...) via SK_ITER_SUC at n=SUC0 0.
    p.have(
        "h_iter2_raw: sk_iter (SUC0 (SUC0 0)) (App_t I_t x) "
        "= sk_step (sk_iter (SUC0 0) (App_t I_t x))"
    ).by(SK_ITER_SUC, "SUC0 0", "App_t I_t x")
    p.have(
        "h_iter2: sk_iter (SUC0 (SUC0 0)) (App_t I_t x) "
        "= sk_step (App_t (App_t K_t x) (App_t K_t x))"
    ).by_rewrite_of("h_iter2_raw", ["h_iter1_final"])

    # Step E: sk_step (App_t (App_t K_t x) (App_t K_t x)) = x by SK_STEP_K.
    p.have(
        "h_K: sk_step (App_t (App_t K_t x) (App_t K_t x)) = x"
    ).by(SK_STEP_K, "x", "App_t K_t x")

    p.thus("sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x").by_thm(
        TRANS(p.fact("h_iter2"), p.fact("h_K"))
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


@proof
def OMEGA_NON_HALTING(p):
    """|- ~ halts Omega_t.

    TRUE under the (now-shipped) leftmost-outermost congruence
    ``sk_step``, but the proof requires machinery this module does
    not yet provide.  Concrete sk_step trajectory (see
    OMEGA_T_STEP1 for the first step):

      T0 = Omega_t                              = App_t SII SII
      T1 = sk_step T0                           = App_t (I_t SII) (I_t SII)
      T2 = sk_step T1                           = App_t ((K_t SII)(K_t SII)) (I_t SII)
                                                  [descend-L: inner I_t SII fires
                                                   as S-redex via I_T_DEF]
      T3 = sk_step T2                           = App_t SII (I_t SII)
                                                  [descend-L: K-redex fires]
      T4 = sk_step T3                           = App_t (I_t (I_t SII)) (I_t (I_t SII))
                                                  [top-level S-redex with
                                                   x=I_t, y=I_t, z=I_t SII]
      ...
    where SII = App_t (App_t S_t I_t) I_t.  Each 3-step window
    transforms ``App_t (I_t X) (I_t X)`` into ``App_t (I_t (I_t X))
    (I_t (I_t X))`` -- the nesting depth on each side strictly grows
    by one, so the term size strictly grows by a constant per cycle.
    Therefore no ``sk_iter n Omega_t`` is a fixed point of sk_step,
    so ``~ halts Omega_t``.

    Infrastructure already shipped:
      Stage 3b (size measure)
        ``sk_size``, ``SK_SIZE_S``, ``SK_SIZE_K``, ``SK_SIZE_APP``,
        ``NAT0_LT_SUC0_N0PLUS_{L,R}``,
        ``SK_SIZE_GROWTH_OMEGA_SHAPE``.
      Stage 3 (Omega first step + normality propagation)
        ``OMEGA_T_STEP1``                 -- sk_step Omega_t computed.
        ``OMEGA_T_NOT_NORMAL``            -- BASE CASE: rules out n = 0.
        ``SK_ITER_PUSH``                  -- commute sk_step in/out of iter.
        ``IS_NORMAL_SK_STEP``             -- normality preserved forward.
        ``IS_NORMAL_SK_ITER_FIXED``       -- fixed point is fixed under iter.
        ``HALTS_SK_STEP_FWD``             -- halts shifts forward.

    Remaining gap for the full proof:

    The base case ``n = 0`` is closed by OMEGA_T_NOT_NORMAL.  The
    general case ``n > 0`` requires showing that no state in the
    Omega trajectory is a fixed point of sk_step, equivalently
    ``!n. ~ is_normal (sk_iter n Omega_t)``.

    The cleanest path: compute the explicit 3-step transformation
    that sends ``App_t (App_t I_t X) (App_t I_t X)`` to
    ``App_t (App_t I_t (App_t I_t X)) (App_t I_t (App_t I_t X))``,
    then combine with SK_SIZE_GROWTH_OMEGA_SHAPE to get
    ``!k. nat0_lt (sk_size (sk_iter (3 * k + 1) Omega_t))
                   (sk_size (sk_iter (3 * (k+1) + 1) Omega_t))``.
    From any supposed fixed point at ``n0 >= 1``, derive
    ``sk_iter (n0 + 3) Omega_t = sk_iter n0 Omega_t`` via
    IS_NORMAL_SK_ITER_FIXED and contradict the strict-growth
    sub-sequence.

    The trajectory computation breaks down to three sk_step
    case-splits (~80 lines each, mirroring SK_STEP_K / SK_STEP_S):
      T1  =  App_t (I X) (I X)                             [given]
      T2  =  App_t ((K X)(K X)) (I X)                      [descent-L: I X --> K X (K X)]
      T3  =  App_t X (I X)                                 [descent-L: K X (K X) --> X]
      T4  =  App_t (I (I X)) (I (I X))                     [top-level S-redex with z = I X]
    Each step uses SK_STEP_REC at the appropriate term plus
    APP_T_INJ chains to refute the wrong-disjunct guards.

    Total estimated: ~300-400 lines of trajectory work.  Out of
    scope for this turn; left as ``sorry``.
    """
    p.goal("~ halts Omega_t")
    p.sorry()


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


new_constant("Y_t", nat0_ty)
Y_t = mk_const("Y_t", [])


@proof
def IS_SK_TERM_Y(p):
    """|- is_sk_term Y_t.

    Y_t is a fixed concrete SK term; ``is_sk_term`` follows by
    repeated application of IS_SK_TERM_S/K/APP.
    """
    p.goal("is_sk_term Y_t")
    p.sorry()


@proof
def Y_FIXED_POINT(p):
    """|- !f. is_sk_term f ==>
              ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f).

    Curry's fixed-point theorem in SK.  Discharges by unfolding Y_t's
    concrete encoding and computing the reduction explicitly (~5
    sk_step's, all K/S rule applications).
    """
    p.goal(
        "!f. is_sk_term f ==> "
        "    ?n. sk_iter n (App_t Y_t f) = App_t f (App_t Y_t f)"
    )
    p.sorry()


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
    """
    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t K_t a) c) = a"
    )
    p.sorry()


@proof
def CHURCH_FALSE_REDUCES(p):
    """|- !a c. is_sk_term a /\\ is_sk_term c ==>
                ?n. sk_iter n (App_t (App_t KI_t a) c) = c.

    KI_t a c = K I a c -->* I c -->* c.
    """
    p.goal(
        "!a c. is_sk_term a /\\ is_sk_term c ==> "
        "      ?n. sk_iter n (App_t (App_t KI_t a) c) = c"
    )
    p.sorry()


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


# ``halts_decider H`` says H is an SK term that decides halting via the
# K_t / KI_t output convention.
new_constant("halts_decider", parse_type("nat0 -> bool"))
halts_decider = mk_const("halts_decider", [])
add_const("halts_decider", halts_decider)


@proof
def HALTS_DECIDER_DEF_THM(p):
    """|- !H. halts_decider H <=>
              is_sk_term H /\\
              !t. is_sk_term t ==>
                  (halts t  ==> ?n. sk_iter n (App_t H t) = K_t) /\\
                  (~halts t ==> ?n. sk_iter n (App_t H t) = KI_t).

    Characterisation of ``halts_decider``.  This is the *definition*
    expanded; once we drop the ``new_constant`` placeholder and write
    a real ``define``, this becomes a one-liner.
    """
    p.goal(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts t ==> (?n. sk_iter n (App_t H t) = K_t)) /\\ "
        "         (~halts t ==> (?n. sk_iter n (App_t H t) = KI_t)))"
    )
    p.sorry()


@proof
def HALTING_REDUCTION_PRESERVED(p):
    """|- !t u n. is_sk_term t /\\ sk_iter n t = u ==> (halts t <=> halts u).

    Halting is invariant under reduction: prepending finitely many
    steps doesn't change whether a normal form is reachable.  Needed
    in both branches of the diagonal contradiction to push ``halts``
    through ``-->*``.
    """
    p.goal(
        "!t u n. is_sk_term t /\\ sk_iter n t = u ==> "
        "        (halts t = halts u)"
    )
    p.sorry()


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
    """
    p.goal("~ (?H. halts_decider H)")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 -- corollaries.
# ---------------------------------------------------------------------------


@proof
def HALTS_NOT_SK_REPRESENTABLE(p):
    """|- ~ ?H. is_sk_term H /\\
                !t. is_sk_term t ==>
                    (halts t  ==> ?n. sk_iter n (App_t H t) = K_t) /\\
                    (~halts t ==> ?n. sk_iter n (App_t H t) = KI_t).

    HALTING_UNDECIDABLE, restated as non-existence of an SK term
    computing the characteristic function of ``halts``.  Immediate
    from HALTING_UNDECIDABLE + HALTS_DECIDER_DEF_THM.
    """
    p.goal(
        "~ (?H. is_sk_term H /\\ "
        "       !t. is_sk_term t ==> "
        "           (halts t ==> (?n. sk_iter n (App_t H t) = K_t)) /\\ "
        "           (~halts t ==> (?n. sk_iter n (App_t H t) = KI_t)))"
    )
    p.sorry()


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
