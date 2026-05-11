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
# Stage 1 -- one-step reduction.
#
# Strategy: head-only.  ``sk_step`` fires a K- or S- redex at the head
# spine when one is present; otherwise returns the term unchanged.
# This is weaker than the standard leftmost-outermost (no congruence
# into subterms), but suffices for the diagonal: I_t / Omega_t / the
# constructed diagonal term ``d`` all have head redexes throughout
# their reduction sequences.
#
# ``sk_step`` is defined directly via SELECT over a three-disjunct
# characterizing predicate.  The disjuncts are mutually exclusive by
# the guard conjuncts (``~K-redex``, ``~S-redex``):
#
#   sk_step t  :=  @r.  (K-redex(t)  /\ r = K-reduct(t))
#                    \/ (S-redex(t)  /\ ~K-redex(t) /\ r = S-reduct(t))
#                    \/ (~K-redex(t) /\ ~S-redex(t) /\ r = t)
#
# Using SELECT directly avoids the COND polymorphism friction (mk_cond
# would still work, but with three layers it gets unwieldy).  The
# guards make the disjunction functional, so SK_STEP_K / SK_STEP_S
# proofs reduce to case-splits with two contradicting branches each.
SK_STEP_DEF = define(
    "sk_step",
    parse_type("nat0 -> nat0"),
    "\\t:nat0. @r:nat0. "
    "(?x y. t = App_t (App_t K_t x) y /\\ r = x) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ?x y z. t = App_t (App_t (App_t S_t x) y) z /\\ "
    "         r = App_t (App_t x z) (App_t y z)) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " r = t)",
)
sk_step = mk_const("sk_step", [])


# ``is_normal`` is *defined* (head-only) as the conjunction of
#   ~ K-redex-shape /\ ~ S-redex-shape.
# This matches sk_step's head-only behaviour: when both clauses hold,
# sk_step is the identity at the head; when either fails, sk_step makes
# progress.
IS_NORMAL_DEF = define(
    "is_normal",
    parse_type("nat0 -> bool"),
    "\\t:nat0. "
    "~(?x y. t = App_t (App_t K_t x) y) /\\ "
    "~(?x y z. t = App_t (App_t (App_t S_t x) y) z)",
)
is_normal = mk_const("is_normal", [])


@proof
def SK_STEP_K(p):
    """|- !x y. sk_step (App_t (App_t K_t x) y) = x.

    Strategy:
      1. Show the SELECT body has a witness at r = x (first disjunct).
      2. ``by_select_def`` substitutes ``sk_step (App_t (App_t K_t x) y)``
         for the SELECT variable, yielding the 3-disjunction at the
         actual sk_step value.
      3. Case-split: the K-redex disjunct gives sk_step ... = x'
         for some x', APP_T_INJ then identifies x' with x.  The
         S-redex and "else" disjuncts both carry ``~(K-redex)`` and
         contradict the K-redex shape of the input.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _CONJ1, CONJUNCT2 as _CONJ2

    p.goal("!x y. sk_step (App_t (App_t K_t x) y) = x")
    p.fix("x y")

    # ---- Stage 1: existence witness for the SELECT body. -------------------
    # We need: ?r. (K-disjunct) \/ (S-disjunct) \/ (else-disjunct), with
    # ``t`` slot pre-substituted to App_t (App_t K_t x) y.  Witness:
    # r := x, taking the K-disjunct.
    with p.have(
        "ex: ?r. "
        "(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ r = a) \\/ "
        "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
        " (?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c /\\ "
        "          r = App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c) /\\ "
        " r = App_t (App_t K_t x) y)"
    ).proof():
        # The witness for the outer existential is r := x.
        # Inner: the K-redex disjunct with a := x, b := y.
        p.have(
            "inner: "
            "?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ x = a"
        ).by_exists(
            ["x", "y"],
            REFL(p._parse("App_t (App_t K_t x) y")),
            REFL(p._parse("x")),
        )
        # Now DISJ1 it into the 3-disjunction.
        p.have(
            "rhs: "
            "(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ x = a) \\/ "
            "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            " (?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c /\\ "
            "          x = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c) /\\ "
            " x = App_t (App_t K_t x) y)"
        ).by_disj("inner")
        # Existential introduction on ``r``.
        p.thus(
            "?r. "
            "(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ r = a) \\/ "
            "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            " (?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c /\\ "
            "          r = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c) /\\ "
            " r = App_t (App_t K_t x) y)"
        ).by_witness("x", "rhs")

    # ---- Stage 2: by_select_def to substitute sk_step value. ---------------
    p.have(
        "body: "
        "(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ "
        "       sk_step (App_t (App_t K_t x) y) = a) \\/ "
        "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
        " (?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c /\\ "
        "          sk_step (App_t (App_t K_t x) y) = "
        "             App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. App_t (App_t K_t x) y = App_t (App_t (App_t S_t a) b) c) /\\ "
        " sk_step (App_t (App_t K_t x) y) = App_t (App_t K_t x) y)"
    ).by_select_def(SK_STEP_DEF, "App_t (App_t K_t x) y", from_="ex")

    # ---- Stage 3: case analysis. -------------------------------------------
    # We need K-redex facts to refute the S/else branches.
    p.have(
        "is_kred: ?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b"
    ).by_exists(
        ["x", "y"], REFL(p._parse("App_t (App_t K_t x) y"))
    )
    with p.cases_on("body"):
        with p.case(
            "h1: ?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b /\\ "
            "         sk_step (App_t (App_t K_t x) y) = a"
        ):
            # The leaf is ``?a. (?b. body)`` and the case auto-chooses
            # the outermost ``a``; we then manually choose ``b``.
            # DSL friction: auto-choose is single-binder; nested ``?a b.``
            # gives ``a_eq: ?b. body[a]`` which requires a manual
            # ``p.choose("b", from_="a_eq")`` to finish destructuring.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_sk)")
            # APP_T_INJ on h_app: App_t (App_t K_t x) y = App_t (App_t K_t a) b
            # gives (App_t K_t x = App_t K_t a) /\ (y = b); then again on the
            # first conjunct gives (K_t = K_t) /\ (x = a).
            p.have("h_o: App_t K_t x = App_t K_t a /\\ y = b").by(
                APP_T_INJ, "App_t K_t x", "y", "App_t K_t a", "b", "h_app"
            )
            p.have("h_o1: App_t K_t x = App_t K_t a").by_thm(_CONJ1(p.fact("h_o")))
            p.have("h_i: K_t = K_t /\\ x = a").by(
                APP_T_INJ, "K_t", "x", "K_t", "a", "h_o1"
            )
            p.have("h_xa: x = a").by_thm(_CONJ2(p.fact("h_i")))
            # sk_step (...) = a = x.
            p.thus("sk_step (App_t (App_t K_t x) y) = x").by_rewrite_of(
                "h_sk", [SYM(p.fact("h_xa"))]
            )
        with p.case(
            "h2: ~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            "    (?a b c. App_t (App_t K_t x) y = "
            "                 App_t (App_t (App_t S_t a) b) c /\\ "
            "             sk_step (App_t (App_t K_t x) y) = "
            "                 App_t (App_t a c) (App_t b c))"
        ):
            p.split("h2", "(h_nk, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(
            "h3: ~(?a b. App_t (App_t K_t x) y = App_t (App_t K_t a) b) /\\ "
            "    ~(?a b c. App_t (App_t K_t x) y = "
            "                 App_t (App_t (App_t S_t a) b) c) /\\ "
            "    sk_step (App_t (App_t K_t x) y) = App_t (App_t K_t x) y"
        ):
            p.split("h3", "(h_nk, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")


@proof
def SK_STEP_S(p):
    """|- !x y z. sk_step (App_t (App_t (App_t S_t x) y) z)
                  = App_t (App_t x z) (App_t y z).

    Same shape as SK_STEP_K, but the witness lands in the second
    disjunct and the K-redex disjunct must be explicitly refuted via
    K_T_NEQ_APP_T (the K-shape can't unify with an S-shape input).
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _CONJ1, CONJUNCT2 as _CONJ2, NE_SYM

    p.goal(
        "!x y z. sk_step (App_t (App_t (App_t S_t x) y) z) "
        "         = App_t (App_t x z) (App_t y z)"
    )
    p.fix("x y z")

    # ---- ~K-redex(S-input): used both for the witness and for refuting
    # the K-disjunct in the case analysis. ----------------------------------
    with p.have(
        "not_kred: ~(?a b. "
        "App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex_kred: ?a b. "
            "App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex_kred")
            p.choose("b", from_="a_eq")
            # b_eq : App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b.
            p.have(
                "outer_inj: App_t (App_t S_t x) y = App_t K_t a /\\ z = b"
            ).by(APP_T_INJ, "App_t (App_t S_t x) y", "z",
                 "App_t K_t a", "b", "b_eq")
            p.have("outer1: App_t (App_t S_t x) y = App_t K_t a").by_thm(
                _CONJ1(p.fact("outer_inj"))
            )
            p.have(
                "inner_inj: App_t S_t x = K_t /\\ y = a"
            ).by(APP_T_INJ, "App_t S_t x", "y", "K_t", "a", "outer1")
            p.have("ASx_eq_K: App_t S_t x = K_t").by_thm(
                _CONJ1(p.fact("inner_inj"))
            )
            # Flip and contradict K_T_NEQ_APP_T at (S_t, x).
            p.have("K_neq: ~(K_t = App_t S_t x)").by(K_T_NEQ_APP_T, "S_t", "x")
            p.have("K_eq: K_t = App_t S_t x").by_thm(SYM(p.fact("ASx_eq_K")))
            p.absurd().by_conj("K_neq", "K_eq")

    # ---- Stage 1: existence witness, taking the S-redex disjunct. ---------
    with p.have(
        "ex: ?r. "
        "(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b /\\ "
        "       r = a) \\/ "
        "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
        " (?a b c. App_t (App_t (App_t S_t x) y) z = "
        "              App_t (App_t (App_t S_t a) b) c /\\ "
        "          r = App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. App_t (App_t (App_t S_t x) y) z = "
        "              App_t (App_t (App_t S_t a) b) c) /\\ "
        " r = App_t (App_t (App_t S_t x) y) z)"
    ).proof():
        # Inner witness for the S-disjunct: a=x, b=y, c=z.
        p.have(
            "inner: ?a b c. App_t (App_t (App_t S_t x) y) z = "
            "                  App_t (App_t (App_t S_t a) b) c /\\ "
            "               App_t (App_t x z) (App_t y z) = "
            "                  App_t (App_t a c) (App_t b c)"
        ).by_exists(
            ["x", "y", "z"],
            REFL(p._parse("App_t (App_t (App_t S_t x) y) z")),
            REFL(p._parse("App_t (App_t x z) (App_t y z)")),
        )
        # Combine with not_kred to make the 2nd-disjunct shape.
        p.have(
            "s_branch: "
            "~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            "(?a b c. App_t (App_t (App_t S_t x) y) z = "
            "             App_t (App_t (App_t S_t a) b) c /\\ "
            "         App_t (App_t x z) (App_t y z) = App_t (App_t a c) (App_t b c))"
        ).by_thm(_CONJ(p.fact("not_kred"), p.fact("inner")))
        # DISJ2/DISJ1 into the 3-disjunction.
        p.have(
            "rhs: "
            "(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b /\\ "
            "       App_t (App_t x z) (App_t y z) = a) \\/ "
            "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            " (?a b c. App_t (App_t (App_t S_t x) y) z = "
            "              App_t (App_t (App_t S_t a) b) c /\\ "
            "          App_t (App_t x z) (App_t y z) = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. App_t (App_t (App_t S_t x) y) z = "
            "              App_t (App_t (App_t S_t a) b) c) /\\ "
            " App_t (App_t x z) (App_t y z) = App_t (App_t (App_t S_t x) y) z)"
        ).by_disj("s_branch")
        p.thus(
            "?r. "
            "(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b /\\ "
            "       r = a) \\/ "
            "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            " (?a b c. App_t (App_t (App_t S_t x) y) z = "
            "              App_t (App_t (App_t S_t a) b) c /\\ "
            "          r = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. App_t (App_t (App_t S_t x) y) z = "
            "              App_t (App_t (App_t S_t a) b) c) /\\ "
            " r = App_t (App_t (App_t S_t x) y) z)"
        ).by_witness("App_t (App_t x z) (App_t y z)", "rhs")

    # ---- Stage 2: by_select_def. ------------------------------------------
    p.have(
        "body: "
        "(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b /\\ "
        "       sk_step (App_t (App_t (App_t S_t x) y) z) = a) \\/ "
        "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
        " (?a b c. App_t (App_t (App_t S_t x) y) z = "
        "              App_t (App_t (App_t S_t a) b) c /\\ "
        "          sk_step (App_t (App_t (App_t S_t x) y) z) = "
        "              App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. App_t (App_t (App_t S_t x) y) z = "
        "              App_t (App_t (App_t S_t a) b) c) /\\ "
        " sk_step (App_t (App_t (App_t S_t x) y) z) = "
        "    App_t (App_t (App_t S_t x) y) z)"
    ).by_select_def(
        SK_STEP_DEF, "App_t (App_t (App_t S_t x) y) z", from_="ex"
    )

    # Pre-build the S-redex existence (used in case 3 contradiction).
    p.have(
        "is_sred: ?a b c. App_t (App_t (App_t S_t x) y) z = "
        "                    App_t (App_t (App_t S_t a) b) c"
    ).by_exists(
        ["x", "y", "z"],
        REFL(p._parse("App_t (App_t (App_t S_t x) y) z")),
    )

    # ---- Stage 3: case analysis. ------------------------------------------
    with p.cases_on("body"):
        with p.case(
            "h1: ?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b /\\ "
            "         sk_step (App_t (App_t (App_t S_t x) y) z) = a"
        ):
            # K-disjunct on S-input is impossible: a, b would give a K-redex
            # equation, contradicting not_kred.
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_kred_ex: ?a b. App_t (App_t (App_t S_t x) y) z = "
                "              App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(
            "h2: ~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            "    (?a b c. App_t (App_t (App_t S_t x) y) z = "
            "                 App_t (App_t (App_t S_t a) b) c /\\ "
            "             sk_step (App_t (App_t (App_t S_t x) y) z) = "
            "                 App_t (App_t a c) (App_t b c))"
        ):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, h_sk)")
            # h_app: App_t (App_t (App_t S_t x) y) z =
            #            App_t (App_t (App_t S_t a) b) c.
            # APP_T_INJ thrice: x = a, y = b, z = c.
            p.have(
                "h_o: App_t (App_t S_t x) y = App_t (App_t S_t a) b /\\ z = c"
            ).by(APP_T_INJ, "App_t (App_t S_t x) y", "z",
                 "App_t (App_t S_t a) b", "c", "h_app")
            p.have("h_o1: App_t (App_t S_t x) y = App_t (App_t S_t a) b").by_thm(
                _CONJ1(p.fact("h_o"))
            )
            p.have("h_zc: z = c").by_thm(_CONJ2(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t x = App_t S_t a /\\ y = b"
            ).by(APP_T_INJ, "App_t S_t x", "y", "App_t S_t a", "b", "h_o1")
            p.have("h_m1: App_t S_t x = App_t S_t a").by_thm(
                _CONJ1(p.fact("h_m"))
            )
            p.have("h_yb: y = b").by_thm(_CONJ2(p.fact("h_m")))
            p.have(
                "h_i: S_t = S_t /\\ x = a"
            ).by(APP_T_INJ, "S_t", "x", "S_t", "a", "h_m1")
            p.have("h_xa: x = a").by_thm(_CONJ2(p.fact("h_i")))
            # Rewrite h_sk via x = a, y = b, z = c (symmetric).
            p.thus(
                "sk_step (App_t (App_t (App_t S_t x) y) z) = "
                "App_t (App_t x z) (App_t y z)"
            ).by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_xa")), SYM(p.fact("h_yb")), SYM(p.fact("h_zc"))],
            )
        with p.case(
            "h3: ~(?a b. App_t (App_t (App_t S_t x) y) z = App_t (App_t K_t a) b) /\\ "
            "    ~(?a b c. App_t (App_t (App_t S_t x) y) z = "
            "                 App_t (App_t (App_t S_t a) b) c) /\\ "
            "    sk_step (App_t (App_t (App_t S_t x) y) z) = "
            "        App_t (App_t (App_t S_t x) y) z"
        ):
            p.split("h3", "(_, h_nS, _)")
            p.absurd().by_conj("h_nS", "is_sred")


@proof
def IS_NORMAL_S(p):
    """|- is_normal S_t.

    S_t is a leaf atom: it doesn't unify with the K-redex shape
    ``App_t (App_t K_t x) y`` (would need S_t = App_t something,
    ruled out by S_T_NEQ_APP_T) nor the S-redex shape (same).  Unfold
    is_normal, conjoin the two negations.
    """
    p.goal("is_normal S_t")
    # Negation of the K-redex shape.
    with p.have("nK: ~(?x y. S_t = App_t (App_t K_t x) y)").proof():
        with p.suppose("hex: ?x y. S_t = App_t (App_t K_t x) y"):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            # y_eq : S_t = App_t (App_t K_t x) y
            p.have("hneq: ~(S_t = App_t (App_t K_t x) y)").by(
                S_T_NEQ_APP_T, "App_t K_t x", "y"
            )
            p.absurd().by_conj("hneq", "y_eq")
    # Negation of the S-redex shape.
    with p.have("nS: ~(?x y z. S_t = App_t (App_t (App_t S_t x) y) z)").proof():
        with p.suppose("hex: ?x y z. S_t = App_t (App_t (App_t S_t x) y) z"):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            p.choose("z", from_="y_eq")
            p.have("hneq: ~(S_t = App_t (App_t (App_t S_t x) y) z)").by(
                S_T_NEQ_APP_T, "App_t (App_t S_t x) y", "z"
            )
            p.absurd().by_conj("hneq", "z_eq")
    # Combine via IS_NORMAL_DEF unfolded at S_t.
    from tactics import CONJ as _CONJ
    p.thus("is_normal S_t").by_unfold(
        _CONJ(p.fact("nK"), p.fact("nS")), IS_NORMAL_DEF
    )


@proof
def IS_NORMAL_K(p):
    """|- is_normal K_t.  Same shape as IS_NORMAL_S, via K_T_NEQ_APP_T."""
    p.goal("is_normal K_t")
    with p.have("nK: ~(?x y. K_t = App_t (App_t K_t x) y)").proof():
        with p.suppose("hex: ?x y. K_t = App_t (App_t K_t x) y"):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            p.have("hneq: ~(K_t = App_t (App_t K_t x) y)").by(
                K_T_NEQ_APP_T, "App_t K_t x", "y"
            )
            p.absurd().by_conj("hneq", "y_eq")
    with p.have("nS: ~(?x y z. K_t = App_t (App_t (App_t S_t x) y) z)").proof():
        with p.suppose("hex: ?x y z. K_t = App_t (App_t (App_t S_t x) y) z"):
            p.choose("x", from_="hex")
            p.choose("y", from_="x_eq")
            p.choose("z", from_="y_eq")
            p.have("hneq: ~(K_t = App_t (App_t (App_t S_t x) y) z)").by(
                K_T_NEQ_APP_T, "App_t (App_t S_t x) y", "z"
            )
            p.absurd().by_conj("hneq", "z_eq")
    from tactics import CONJ as _CONJ
    p.thus("is_normal K_t").by_unfold(
        _CONJ(p.fact("nK"), p.fact("nS")), IS_NORMAL_DEF
    )


@proof
def IS_NORMAL_IMP_FIXED(p):
    """|- !t. is_normal t ==> sk_step t = t.

    Forward direction of IS_NORMAL_CASES.  When ``is_normal t``
    expands to the conjunction of two negated existentials, the
    SELECT body's third (``else'') disjunct is the unique satisfying
    branch and r = t.

    Same ``by_select_def`` pattern as SK_STEP_K / SK_STEP_S, but the
    other two disjuncts are refuted by the negated existentials carried
    by ``is_normal`` rather than by APP_T_INJ tag-clashes.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _CONJ1, CONJUNCT2 as _CONJ2

    p.goal("!t. is_normal t ==> sk_step t = t")
    p.fix("t")
    p.assume("h_norm: is_normal t")

    # Unfold is_normal: get the two negated existentials as facts.
    p.have(
        "h_norm_body: ~(?x y. t = App_t (App_t K_t x) y) /\\ "
        "             ~(?x y z. t = App_t (App_t (App_t S_t x) y) z)"
    ).by_unfold("h_norm", IS_NORMAL_DEF)
    p.split("h_norm_body", "(not_kred, not_sred)")

    # ---- Stage 1: existence witness, taking the else disjunct. ------------
    with p.have(
        "ex: ?r. "
        "(?a b. t = App_t (App_t K_t a) b /\\ r = a) \\/ "
        "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
        " (?a b c. t = App_t (App_t (App_t S_t a) b) c /\\ "
        "          r = App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
        " r = t)"
    ).proof():
        # Else-disjunct holds at r = t.
        p.have(
            "else_branch: "
            "~(?a b. t = App_t (App_t K_t a) b) /\\ "
            "~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
            "t = t"
        ).by_thm(
            _CONJ(p.fact("not_kred"), _CONJ(p.fact("not_sred"), REFL(p._parse("t"))))
        )
        p.have(
            "rhs: "
            "(?a b. t = App_t (App_t K_t a) b /\\ t = a) \\/ "
            "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
            " (?a b c. t = App_t (App_t (App_t S_t a) b) c /\\ "
            "          t = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
            " t = t)"
        ).by_disj("else_branch")
        p.thus(
            "?r. "
            "(?a b. t = App_t (App_t K_t a) b /\\ r = a) \\/ "
            "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
            " (?a b c. t = App_t (App_t (App_t S_t a) b) c /\\ "
            "          r = App_t (App_t a c) (App_t b c))) \\/ "
            "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
            " ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
            " r = t)"
        ).by_witness("t", "rhs")

    # ---- Stage 2: by_select_def. ------------------------------------------
    p.have(
        "body: "
        "(?a b. t = App_t (App_t K_t a) b /\\ sk_step t = a) \\/ "
        "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
        " (?a b c. t = App_t (App_t (App_t S_t a) b) c /\\ "
        "          sk_step t = App_t (App_t a c) (App_t b c))) \\/ "
        "(~(?a b. t = App_t (App_t K_t a) b) /\\ "
        " ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
        " sk_step t = t)"
    ).by_select_def(SK_STEP_DEF, "t", from_="ex")

    # ---- Stage 3: case analysis. ------------------------------------------
    with p.cases_on("body"):
        with p.case(
            "h1: ?a b. t = App_t (App_t K_t a) b /\\ sk_step t = a"
        ):
            # K-disjunct contradicts not_kred (just drop the sk_step
            # conjunct to recover the existential it carries).
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_kred_ex: ?a b. t = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(
            "h2: ~(?a b. t = App_t (App_t K_t a) b) /\\ "
            "    (?a b c. t = App_t (App_t (App_t S_t a) b) c /\\ "
            "             sk_step t = App_t (App_t a c) (App_t b c))"
        ):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                "h_sred_ex: ?a b c. t = App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], p.fact("h_app"))
            p.absurd().by_conj("not_sred", "h_sred_ex")
        with p.case(
            "h3: ~(?a b. t = App_t (App_t K_t a) b) /\\ "
            "    ~(?a b c. t = App_t (App_t (App_t S_t a) b) c) /\\ "
            "    sk_step t = t"
        ):
            p.split("h3", "(_, _, h_sk)")
            p.thus("sk_step t = t").by_thm(p.fact("h_sk"))


@proof
def IS_NORMAL_CASES(p):
    """|- !t. is_sk_term t ==> (is_normal t = (sk_step t = t)).

    Forward: IS_NORMAL_IMP_FIXED specialized at t.

    Reverse: assume sk_step t = t.  Show ``~K-redex(t)`` and
    ``~S-redex(t)`` separately, then conjoin and fold to is_normal.

    Each negation is by contradiction using NAT0_LT_NOT_REFL:
      * K-redex case: t = App_t (App_t K_t x) y and SK_STEP_K give
        sk_step t = x.  With h_fix: t = x.  But
        nat0_lt x (App_t (App_t K_t x) y) follows from
        NAT0_LT_APP_T_R (K_t, x) and NAT0_LT_APP_T_L composed via
        NAT0_LT_TRANS.  Rewriting by t = App_t (App_t K_t x) y
        gives nat0_lt x t, then by x = t gives nat0_lt t t -- contra.
      * S-redex case: t = App_t (App_t (App_t S_t x) y) z and
        SK_STEP_S give sk_step t = App_t (App_t x z) (App_t y z).
        With h_fix: App_t (App_t x z) (App_t y z) = t.
        APP_T_INJ yields ``App_t y z = z``, and
        NAT0_LT_APP_T_R (y, z) gives nat0_lt z (App_t y z).
        Substituting the equality flips to nat0_lt z z -- contra.

    The is_sk_term hypothesis isn't used; carried in the goal for
    interface consistency with downstream consumers.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _CONJ1,
        CONJUNCT2 as _CONJ2,
        TRANS as _TRANS,
    )
    from nat0_order import NAT0_LT_TRANS, NAT0_LT_NOT_REFL

    p.goal("!t. is_sk_term t ==> (is_normal t = (sk_step t = t))")
    p.fix("t")
    p.assume("h_st: is_sk_term t")  # unused, see docstring

    # ---- Forward direction (specialize IS_NORMAL_IMP_FIXED). ---------------
    p.have("fwd: is_normal t ==> sk_step t = t").by_inst(
        IS_NORMAL_IMP_FIXED, "t"
    )

    # ---- Reverse direction. -----------------------------------------------
    with p.have("rev: sk_step t = t ==> is_normal t").proof():
        p.assume("h_fix: sk_step t = t")

        # not_kred: ~K-redex.
        with p.have("not_kred: ~(?x y. t = App_t (App_t K_t x) y)").proof():
            with p.suppose("hex: ?x y. t = App_t (App_t K_t x) y"):
                p.choose("x", from_="hex")
                p.choose("y", from_="x_eq")
                # y_eq : t = App_t (App_t K_t x) y
                p.have(
                    "hsk_red: sk_step (App_t (App_t K_t x) y) = x"
                ).by(SK_STEP_K, "x", "y")
                # Pull along y_eq: sk_step t = x.
                p.have("hsk_tx: sk_step t = x").by_rewrite_of(
                    "hsk_red", [SYM(p.fact("y_eq"))]
                )
                # x = t via SYM(hsk_tx); h_fix; TRANS.
                p.have("hxt: x = t").by_thm(
                    _TRANS(SYM(p.fact("hsk_tx")), p.fact("h_fix"))
                )
                # nat0_lt x (App_t K_t x).
                p.have("lt1: nat0_lt x (App_t K_t x)").by(
                    NAT0_LT_APP_T_R, "K_t", "x"
                )
                # nat0_lt (App_t K_t x) (App_t (App_t K_t x) y).
                p.have(
                    "lt2: nat0_lt (App_t K_t x) (App_t (App_t K_t x) y)"
                ).by(NAT0_LT_APP_T_L, "App_t K_t x", "y")
                # Compose: nat0_lt x (App_t (App_t K_t x) y).
                p.have(
                    "lt_x_red: nat0_lt x (App_t (App_t K_t x) y)"
                ).by(
                    NAT0_LT_TRANS,
                    "x", "App_t K_t x", "App_t (App_t K_t x) y",
                    "lt1", "lt2",
                )
                # Rewrite using y_eq to fold App_t (App_t K_t x) y back to t.
                p.have("lt_x_t: nat0_lt x t").by_rewrite_of(
                    "lt_x_red", [SYM(p.fact("y_eq"))]
                )
                # Substitute x := t (via hxt) to get nat0_lt t t.
                p.have("lt_t_t: nat0_lt t t").by_rewrite_of(
                    "lt_x_t", [p.fact("hxt")]
                )
                p.have("nrefl: ~(nat0_lt t t)").by(NAT0_LT_NOT_REFL, "t")
                p.absurd().by_conj("nrefl", "lt_t_t")

        # not_sred: ~S-redex.
        with p.have(
            "not_sred: ~(?x y z. t = App_t (App_t (App_t S_t x) y) z)"
        ).proof():
            with p.suppose(
                "hex: ?x y z. t = App_t (App_t (App_t S_t x) y) z"
            ):
                p.choose("x", from_="hex")
                p.choose("y", from_="x_eq")
                p.choose("z", from_="y_eq")
                # z_eq : t = App_t (App_t (App_t S_t x) y) z
                p.have(
                    "hsk_red: sk_step (App_t (App_t (App_t S_t x) y) z) "
                    "= App_t (App_t x z) (App_t y z)"
                ).by(SK_STEP_S, "x", "y", "z")
                # Fold to sk_step t.
                p.have(
                    "hsk_t: sk_step t = App_t (App_t x z) (App_t y z)"
                ).by_rewrite_of("hsk_red", [SYM(p.fact("z_eq"))])
                # h_fix : sk_step t = t, so
                # App_t (App_t x z) (App_t y z) = t.
                p.have(
                    "h_redt: App_t (App_t x z) (App_t y z) = t"
                ).by_thm(_TRANS(SYM(p.fact("hsk_t")), p.fact("h_fix")))
                # Replace t with the S-redex form on the RHS.
                p.have(
                    "h_eq: App_t (App_t x z) (App_t y z) "
                    "= App_t (App_t (App_t S_t x) y) z"
                ).by_rewrite_of("h_redt", [p.fact("z_eq")])
                # APP_T_INJ on the outer App_t:
                #   App_t x z = App_t (App_t S_t x) y  AND  App_t y z = z.
                p.have(
                    "h_outer: App_t x z = App_t (App_t S_t x) y /\\ "
                    "         App_t y z = z"
                ).by(
                    APP_T_INJ,
                    "App_t x z", "App_t y z",
                    "App_t (App_t S_t x) y", "z",
                    "h_eq",
                )
                p.have("h_yz: App_t y z = z").by_thm(
                    _CONJ2(p.fact("h_outer"))
                )
                # nat0_lt z (App_t y z), substitute App_t y z = z to get
                # nat0_lt z z.
                p.have("lt_z: nat0_lt z (App_t y z)").by(
                    NAT0_LT_APP_T_R, "y", "z"
                )
                p.have("lt_z_z: nat0_lt z z").by_rewrite_of(
                    "lt_z", [p.fact("h_yz")]
                )
                p.have("nrefl: ~(nat0_lt z z)").by(NAT0_LT_NOT_REFL, "z")
                p.absurd().by_conj("nrefl", "lt_z_z")

        # Combine the two negations and fold to is_normal.
        p.thus("is_normal t").by_unfold(
            _CONJ(p.fact("not_kred"), p.fact("not_sred")), IS_NORMAL_DEF
        )

    p.thus("is_normal t = (sk_step t = t)").by_iff("fwd", "rev")


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
#   I_t x   -->  x                              (S K K x --> K x (K x) --> x)
#   Omega_t -->  Omega_t                        (one-step self-loop)
#
# Hence Omega_t never reaches a normal form: every ``sk_iter n Omega_t``
# equals Omega_t.
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

    I = SKK; SKK x reduces in two steps to x (one for S, one to drop the
    spurious K-redex).
    """
    p.goal("!x. is_sk_term x ==> sk_iter (SUC0 (SUC0 0)) (App_t I_t x) = x")
    p.sorry()


@proof
def OMEGA_T_SELF_LOOP(p):
    """|- sk_step Omega_t = Omega_t.

    Proof:  Omega_t = App (S I I) (S I I)
                  --> App (App I (S I I)) (App I (S I I))   (S-rule)
                  -->* (S I I) (S I I)
                   = Omega_t.

    The "-->*" hides two I-reductions; for the leftmost-outermost step
    we land back at Omega_t after exactly three steps, so the cleaner
    invariant is ``sk_iter 3 Omega_t = Omega_t``.  Either form is fine
    for OMEGA_NON_HALTING; we pick whichever matches sk_step's
    definition.
    """
    p.goal("sk_step Omega_t = Omega_t")
    p.sorry()


@proof
def OMEGA_NON_HALTING(p):
    """|- ~ halts Omega_t.

    From OMEGA_T_SELF_LOOP by induction on the step count:
    sk_iter n Omega_t = Omega_t for every n, and Omega_t is not normal
    (its head spine has an active S-redex).
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
