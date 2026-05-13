"""Undecidability of the halting problem, via SK combinators over HF.

Final theorem (``HALTING_UNDECIDABLE``):

    |- ~ ?H. halts_decider H

where ``halts_decider H`` says ``H`` is an SK term and, for every SK
term ``t``,

    halts_b t = ~halts_b (App_t H t)

i.e. the *halt-status of the decider's output on t* encodes the
answer (flipped, so the diagonal contradiction lands cleanly).

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
              No substitution lemmas. The non-halting witness ``Omega``
              is definable in five symbols (and unused in the final
              theorem -- see "Diagonal" below).

The diagonal is the same shape in all three.  SK wins by avoiding the
nastiest infrastructure piece (substitution under binders) while
keeping the diagonal mechanically identical.

------------------------------------------------------------------
The idea (Turing 1936; SK presentation: Barendregt Ch. 7)
------------------------------------------------------------------

Three ingredients:

  (1) *Encoding.* SK terms are finite ternary trees: leaves S/K, internal
      nodes App.  Each is a tagged HF tuple, hence a nat0.  Reduction
      rules ``K x y -> x`` and ``S x y z -> x z (y z)`` are local
      pattern matches.

  (2) *Halting.*  ``halts_b t := ?n. is_normal (bullet_iter n t)``,
      Takahashi-style halting via the deterministic complete-development
      ``sk_bullet`` iterated on nat0.  Sigma_1 over nat0 (r.e.) but,
      the theorem says, not decidable by an SK term.

  (3) *Diagonal.*  Curry's classical diagonal ``e = S (K H) SII``,
      ``d = e e``.  Under parallel reduction one gets
      ``d ->>_par App_t H d`` (PAR_REFL lets H stay un-reduced inside
      the residue, which is what makes the diagonal work for arbitrary
      ``is_sk_term H``).  Bridge to bullet via ``HALTS_B_IFF_HALTS_PAR``
      gives ``halts_b d = halts_b (App_t H d)``.  Combined with the
      flipped decider spec, ``halts_b d = ~halts_b d`` -- contradiction.

      No fixed-point combinator, no Omega.  See ``iter_to_bullet.md``
      for the design history (initial bullet-only DIAG_TERM was
      empirically falsified for composite H; current proof uses par).

------------------------------------------------------------------
Stage map
------------------------------------------------------------------

  Stage 0 (sk):       SK terms as tagged HF tuples
                      (S_t, K_t, App_t, is_sk_term).
  Stage 1 (is_normal): Syntactic no-redex predicate (WF-rec on
                      Pair_ord depth) + normal-form structural lemmas
                      (IS_NORMAL_NOT_K_REDEX_SHAPE, _NOT_S_REDEX_SHAPE,
                      _APP_DECOMP).
  Stage 2 (par):      Parallel reduction relation ``sk_par_step`` +
                      RTC ``sk_par_steps`` + ``par_chain`` DSL.
  Stage 3 (bullet):   Takahashi's complete development ``sk_bullet``
                      + triangle property + Tait/Martin-Loef diamond
                      + Church-Rosser confluence on par.
  Stage 4 (halts):    ``bullet_iter`` + ``halts_b`` (user-facing) +
                      ``halts_par`` (internal) + the bridge
                      ``HALTS_B_IFF_HALTS_PAR``.
  Stage 5 (diag):     Classical Curry diagonal ``DIAG_TERM`` in par
                      form; ``DIAGONAL_TERM_EXISTS`` lifts to halts_b
                      via the bridge.
  Stage 6:            ``HALTING_UNDECIDABLE`` and the corollary
                      ``HALTS_NOT_SK_REPRESENTABLE``.

------------------------------------------------------------------
What this gives and doesn't give
------------------------------------------------------------------

Derived from the bare HOL kernel + ``hf_sets.py``:
  * Undecidability of halting for SK combinators (the headline).
  * Church-Rosser for SK via parallel reduction (en route to the bridge).
  * SK is Turing-complete in the weak sense (par-form Curry diagonal
    gives general self-reference).

Not in scope here:
  * Equivalence with Turing machines or lambda calculus (would need a
    third file). The theorem stands on its own without it.
  * Equivalence between Takahashi halting (``halts_b``) and LMO halting.
    Classically the same by standardization; this codebase doesn't
    need the equivalence for the undecidability proof.

Pairs especially well with ``godel_first.py``: the diagonal in this
file is mechanically the same as the Goedel diagonal -- self-application
producing self-reference. Tarski's undefinability of truth is the same
diagonal a third time.
"""

from fusion import Var, new_constant, HolError
from basics import mk_const, mk_app, mk_abs, mk_eq, rand, rator, aconv, dest_eq
from parser import define, parse_type, add_const, pp
from nat0 import nat0_ty, ZERO, mk_suc0
from nat0_order import define_wf_lt, NAT0_LT_TRANS
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
# Common helpers for sk_bullet's wf-recursive SELECT-shaped body.
# ---------------------------------------------------------------------------


_nat0_fn_ty = parse_type("nat0 -> nat0")


def _lift_select_eq(r_var, pw_eq_th):
    """Given ``|- P r = Q r`` with ``r`` free (and not in hypotheses),
    return ``|- (@r. P r) = (@r. Q r)``.

    Two-step lift: ``ABS`` over ``r`` to land on
    ``(\\r. P r) = (\\r. Q r)``, then ``AP_TERM`` the polymorphic ``@``
    constant instantiated at ``r``'s type.  Used by SK_BULLET_MONO to
    lift per-disjunct iffs through the SELECT body.
    """
    from tactics import AP_TERM as _AP_TERM
    from fusion import ABS as _ABS, aty as _aty
    abs_eq = _ABS(r_var, pw_eq_th)
    eps_const = mk_const("@", [(r_var.ty, _aty)])
    return _AP_TERM(eps_const, abs_eq)


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


def _atom_neq_App_negations(p, atom, atom_neq_lemma):
    """For an atom term (S_t or K_t), prove the three "atom is not
    App_t-shaped" existentials:
      ``~(?x y. atom = App_t (App_t K_t x) y)``,
      ``~(?x y z. atom = App_t (App_t (App_t S_t x) y) z)``,
      ``~(?a b. atom = App_t a b)``.
    Returns the three fact-name strings.  Uses S_T_NEQ_APP_T / K_T_NEQ_APP_T.
    """
    atom_str = atom
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


# ---------------------------------------------------------------------------
# Stage 1 -- ``is_normal``: syntactic no-redex predicate.
#
# A term ``n`` is "normal" iff it contains no K-redex or S-redex
# anywhere.  WF-recursion on Pair_ord depth, same shape as
# ``is_sk_term``:
#
#   _is_normal_F f n  :=  n = S_t
#                       \/ n = K_t
#                       \/ ( ~(?M N. n = App_t (App_t K_t M) N)
#                          /\ ~(?M N P. n = App_t (App_t (App_t S_t M) N) P)
#                          /\ ?a b. n = App_t a b /\ f a /\ f b )
#
# The two not-redex guards are non-recursive in f; only the inner
# App-existential drives recursion, at NAT0_LT_APP_T_L/R-smaller args.
#
# Under leftmost-outermost reduction this is classically equivalent to
# ``sk_bullet t = t``; the equivalence is not needed for the halting
# proof, so we don't formalise it.
# ---------------------------------------------------------------------------


_IS_NORMAL_F_DEF = define(
    "_is_normal_F",
    _F_pred_ty,
    "\\f:nat0->bool. \\n:nat0. "
    "n = S_t \\/ n = K_t \\/ "
    "(~(?u v. n = App_t (App_t K_t u) v) /\\ "
    " ~(?u v w. n = App_t (App_t (App_t S_t u) v) w) /\\ "
    " (?a b. n = App_t a b /\\ f a /\\ f b))",
)
_IS_NORMAL_F = mk_const("_is_normal_F", [])


@proof
def IS_NORMAL_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
    ==> _is_normal_F f n = _is_normal_F g n.

    D1 (n = S_t), D2 (n = K_t) are f-free (REFL).  D3's outer
    ~K-redex / ~S-redex guards are f-free; the inner
    ``?a b. n = App_t a b /\\ f a /\\ f b`` recurses at strictly-
    smaller arguments (NAT0_LT_APP_T_L/R), handled by
    ``mono_iff_binary_step``.  Conjoin the f-free guards on top via
    AP_TERM, then chain disjuncts via ``or_chain_collapse``.
    """
    from tactics import AP_TERM as _AP_TERM
    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _is_normal_F f n = _is_normal_F g n",
        types={"f": _pred_ty, "g": _pred_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")

    h_th = p.fact("h")
    eq_S = REFL(p._parse("n = S_t"))
    eq_K = REFL(p._parse("n = K_t"))
    eq_app_inner = mono_iff_binary_step(
        App_t, NAT0_LT_APP_T_L, NAT0_LT_APP_T_R, h_th
    )
    nK_guard = p._parse("~(?u v. n = App_t (App_t K_t u) v)")
    nS_guard = p._parse("~(?u v w. n = App_t (App_t (App_t S_t u) v) w)")
    and_const = mk_const("/\\", [])
    # Right-associative /\: nest as nK /\ (nS /\ inner) to match the
    # body's right-associative chain.
    eq_with_nS = _AP_TERM(mk_app(and_const, nS_guard), eq_app_inner)
    eq_app = _AP_TERM(mk_app(and_const, nK_guard), eq_with_nS)
    body_eq = or_chain_collapse([eq_S, eq_K, eq_app])

    p.thus("_is_normal_F f n = _is_normal_F g n").by_unfold(
        body_eq, _IS_NORMAL_F_DEF
    )


IS_NORMAL_DEF, _IS_NORMAL_REC_RAW = define_wf_lt(
    "is_normal",
    _pred_ty,
    _IS_NORMAL_F,
    IS_NORMAL_MONO,
)
is_normal = mk_const("is_normal", [])


# IS_NORMAL_REC : |- !n. is_normal n =
#                          n = S_t \/ n = K_t \/
#                          (~(?M N. n = App_t (App_t K_t M) N) /\
#                           ~(?M N P. n = App_t (App_t (App_t S_t M) N) P) /\
#                           ?a b. n = App_t a b /\ is_normal a /\ is_normal b).
IS_NORMAL_REC = _unfold_rec_via_F_def(_IS_NORMAL_REC_RAW, _IS_NORMAL_F_DEF)



# ---------------------------------------------------------------------------
# Stage 3 -- parallel reduction.
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
# itself), and (2) the triangle / diamond proofs (instantiating P with
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
# ---------------------------------------------------------------------------
# Inversion lemmas for ``sk_par_step``.
#
# The impredicative encoding admits inversion only via careful
# P-instantiation: pick a Q such that ``closures(Q)`` is provable,
# SPEC the unfolded universal at Q, and BETA_NORM the resulting redexes.
# The two atom inversions below establish the technique; they are
# prerequisites for the App-shape inversion lemmas needed by the
# triangle / diamond proofs.
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
    ``S_t``.  Used by the triangle / diamond proofs and by the App-
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
# Stage 4 -- Takahashi's complete-development function ``sk_bullet``.
#
# Defined by well-founded recursion on Pair_ord depth (via
# ``define_wf_lt``).  Contracts every redex visible at a node
# simultaneously:
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
# other-App, leaf).  Atom unfolds (S_t / K_t) fall into the leaf branch.
#
# The triangle property
#     SK_BULLET_TRIANGLE : !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A)
# is the headline lemma; ``TRIANGLE_EXISTS`` packages it as the
# existential consumed by ``PAR_STEP_DIAMOND`` / ``PAR_STEPS_STRIP`` /
# ``PAR_STEPS_CONFLUENT`` (Tait/Martin-Loef diamond + Church-Rosser).
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
    f_var = Var("f", _nat0_fn_ty)
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

    Stitch pattern (or_chain_collapse + _lift_select_eq + SPECL through
    ``_SK_BULLET_F_AT``).  Per-disjunct iffs:
      D1 (K-redex, single recurse)    -- ``_bullet_F_d1_mono_iff``.
      D2 (S-redex, ternary recurse)   -- ``_bullet_F_d2_mono_iff``;
                                         prepended with ``~K`` via
                                         AP_TERM(/\\) lift.
      D3 (other-App, binary recurse)  -- ``_mono_iff_value_binary_pw_step``;
                                         prepended with ``~K /\\ ~S`` via
                                         two AP_TERM(/\\) lifts.
      D4 (leaf, f-free)               -- REFL.

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
            "f": _nat0_fn_ty,
            "g": _nat0_fn_ty,
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
    _nat0_fn_ty,
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
    existential bvars (matching SK_STEP_LEFT's convention) -- this aligns
    with ``_sk_bullet_disjuncts``' bvar choice so
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
# Dependencies for SK_BULLET_TRIANGLE.
#
# PAR_STEP_K_APP_INV and PAR_STEP_S_APP_APP_INV are discharged below
# via the shared ``_par_step_app_atom_inv`` template.  TRIANGLE itself
# (further below) assembles the four pieces via impredicative
# P-instantiation with the strengthened invariant
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
    on A's shape:

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


def _triangle_K_case(p):
    """K-redex sub-case of _TRIANGLE_APP_CLOSURE.

    Context (from outer cases_on auto-introduce):
      ``Ai`` in scope; ``Ai_eq : A = App_t K_t Ai``.
      Plus the four hyps h_A / h_A_bull / h_B / h_B_bull.

    Goal: ``sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))``.

    App_t A B is the K-redex ``App_t (App_t K_t Ai) B`` whose bullet
    collapses to sk_bullet Ai (SK_BULLET_K_REDEX).  Strategy:
      1. PAR_STEP_K_APP_INV on h_A : A1 = App_t K_t A1_in,
         sk_par_step Ai A1_in.
      2. Compute sk_bullet (App_t K_t Ai) = App_t K_t (sk_bullet Ai)
         via SK_BULLET_APP_OTHER (App_t K_t Ai is not itself a K/S
         redex -- single App layer) + SK_BULLET_K_T.
      3. PAR_STEP_K_APP_INV on h_A_bull (rewritten through (1) and
         (2)) : sk_par_step A1_in (sk_bullet Ai).
      4. PAR_K with X1 := sk_bullet Ai, Y1 := sk_bullet B yields
         sk_par_step (App_t (App_t K_t A1_in) B1) (sk_bullet Ai).
      5. Fold (App_t K_t A1_in) -> A1 and sk_bullet Ai -> sk_bullet
         (App_t A B) via SK_BULLET_K_REDEX.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
    )

    # ---- Step 1: invert h_A using A = App_t K_t Ai. -------------------
    p.have(
        "h_A_K: sk_par_step (App_t K_t Ai) A1"
    ).by_rewrite_of("h_A", [p.fact("Ai_eq")])
    p.have(
        "h_A1_shape: ?XP:nat0. A1 = App_t K_t XP /\\ "
        "            sk_par_step Ai XP"
    ).by(PAR_STEP_K_APP_INV, "Ai", "A1", "h_A_K")
    p.choose("A1_in", from_="h_A1_shape")
    p.split("A1_in_eq", "(h_A1_eq, h_par_Ai_A1_in)")

    # ---- Step 2a: ~K and ~S guards for App_t K_t Ai. ------------------
    with p.have(
        "h_nK_KAi: "
        "~(?a b. App_t K_t Ai = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex: ?a b. App_t K_t Ai = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                "h_inj: K_t = App_t K_t a /\\ Ai = b"
            ).by(
                APP_T_INJ, "K_t", "Ai",
                "App_t K_t a", "b", "b_eq",
            )
            p.have(
                "h_K_app: K_t = App_t K_t a"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_K_neq: ~(K_t = App_t K_t a)"
            ).by(K_T_NEQ_APP_T, "K_t", "a")
            p.absurd().by_conj("h_K_neq", "h_K_app")
    with p.have(
        "h_nS_KAi: ~(?a b c. App_t K_t Ai = "
        "          App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "ex: ?a b c. App_t K_t Ai = "
            "    App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_inj: K_t = App_t (App_t S_t a) b /\\ Ai = c"
            ).by(
                APP_T_INJ, "K_t", "Ai",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_K_app: K_t = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_K_neq: ~(K_t = App_t (App_t S_t a) b)"
            ).by(K_T_NEQ_APP_T, "App_t S_t a", "b")
            p.absurd().by_conj("h_K_neq", "h_K_app")
    p.have(
        "h_nKnS_KAi: "
        "~(?a b. App_t K_t Ai = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t K_t Ai = "
        "  App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact("h_nK_KAi"), p.fact("h_nS_KAi")))

    # ---- Step 2b: sk_bullet (App_t K_t Ai) = App_t K_t (sk_bullet Ai).
    p.have(
        "h_bull_KAi_raw: sk_bullet (App_t K_t Ai) = "
        "                App_t (sk_bullet K_t) (sk_bullet Ai)"
    ).by(SK_BULLET_APP_OTHER, "K_t", "Ai", "h_nKnS_KAi")
    p.have(
        "h_bull_KAi: sk_bullet (App_t K_t Ai) = "
        "            App_t K_t (sk_bullet Ai)"
    ).by_rewrite_of("h_bull_KAi_raw", [SK_BULLET_K_T])

    # ---- Step 3: invert h_A_bull. -------------------------------------
    # First propagate Ai_eq and A1_in_eq into h_A_bull's surface form.
    p.have(
        "h_bull_A_step1: sk_bullet A = sk_bullet (App_t K_t Ai)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("Ai_eq")))
    p.have(
        "h_bull_A: sk_bullet A = App_t K_t (sk_bullet Ai)"
    ).by_trans("h_bull_A_step1", "h_bull_KAi")
    # DSL friction: by_rewrite_of with h_A1_eq is rejected as
    # non-terminating because A1_in's @-binder body contains A1
    # free.  Compose the congruence equation manually via by_cong +
    # by_eq_mp -- this skips REWRITE_CONV's loop guard entirely.
    p.have(
        "h_A_bull_eq: "
        "sk_par_step A1 (sk_bullet A) = "
        "sk_par_step (App_t K_t A1_in) (App_t K_t (sk_bullet Ai))"
    ).by_cong(sk_par_step, "h_A1_eq", "h_bull_A")
    p.have(
        "h_A_bull_K: "
        "sk_par_step (App_t K_t A1_in) (App_t K_t (sk_bullet Ai))"
    ).by_eq_mp("h_A_bull_eq", "h_A_bull")
    # Now invert at K_t.
    p.have(
        "h_inv_A1: ?XP:nat0. "
        "App_t K_t (sk_bullet Ai) = App_t K_t XP /\\ "
        "sk_par_step A1_in XP"
    ).by(
        PAR_STEP_K_APP_INV,
        "A1_in", "App_t K_t (sk_bullet Ai)", "h_A_bull_K",
    )
    p.choose("Xp", from_="h_inv_A1")
    p.split("Xp_eq", "(h_app_eq, h_par_A1in_Xp)")
    p.have(
        "h_inj_Xp: K_t = K_t /\\ sk_bullet Ai = Xp"
    ).by(
        APP_T_INJ, "K_t", "sk_bullet Ai", "K_t", "Xp", "h_app_eq"
    )
    p.have(
        "h_Xp_eq: sk_bullet Ai = Xp"
    ).by_thm(_C2(p.fact("h_inj_Xp")))
    p.have(
        "h_par_A1in_bullAi: sk_par_step A1_in (sk_bullet Ai)"
    ).by_rewrite_of(
        "h_par_A1in_Xp", [SYM(p.fact("h_Xp_eq"))]
    )

    # ---- Step 4: PAR_K to assemble. -----------------------------------
    p.have(
        "h_par_PAR_K: "
        "sk_par_step (App_t (App_t K_t A1_in) B1) (sk_bullet Ai)"
    ).by(
        PAR_K,
        "A1_in", "sk_bullet Ai", "B1", "sk_bullet B",
        _CONJ(
            p.fact("h_par_A1in_bullAi"), p.fact("h_B_bull")
        ),
    )

    # ---- Step 5: fold to the goal form. -------------------------------
    # App_t A B = App_t (App_t K_t Ai) B; sk_bullet collapses to
    # sk_bullet Ai via SK_BULLET_K_REDEX.
    p.have(
        "h_AB_eq: App_t A B = App_t (App_t K_t Ai) B"
    ).by_cong(App_t, "Ai_eq", REFL(p._parse("B")))
    p.have(
        "h_bull_KaiB: "
        "sk_bullet (App_t (App_t K_t Ai) B) = sk_bullet Ai"
    ).by(SK_BULLET_K_REDEX, "Ai", "B")
    p.have(
        "h_bull_AB_eq1: "
        "sk_bullet (App_t A B) = sk_bullet (App_t (App_t K_t Ai) B)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("h_AB_eq")))
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = sk_bullet Ai"
    ).by_trans("h_bull_AB_eq1", "h_bull_KaiB")
    # SYM(h_A1_eq) rewrites App_t K_t A1_in -> A1 (safe).
    # SYM(h_bull_AB) rewrites sk_bullet Ai -> sk_bullet (App_t A B) (safe).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_K",
        [SYM(p.fact("h_A1_eq")), SYM(p.fact("h_bull_AB"))],
    )


def _triangle_S_case(p):
    """S-redex sub-case of _TRIANGLE_APP_CLOSURE.

    Context: Ai, Bi in scope; ``Bi_eq : A = App_t (App_t S_t Ai) Bi``
    (Bi_eq because the outer ``?Ai Bi.`` auto-introduced Ai and the
    inner ?Bi was choose'd).

    App_t A B = App_t (App_t (App_t S_t Ai) Bi) B is an S-redex;
    SK_BULLET_S_REDEX collapses its bullet to
    ``App_t (App_t (sk_bullet Ai) (sk_bullet B))
            (App_t (sk_bullet Bi) (sk_bullet B))``.

    Strategy mirrors _triangle_K_case but with a 2-tuple inversion
    via PAR_STEP_S_APP_APP_INV:
      1. PAR_STEP_S_APP_APP_INV on h_A : A1 = App_t (App_t S_t A1_in)
         B1_in, sk_par_step Ai A1_in, sk_par_step Bi B1_in.
      2. Compute sk_bullet A = App_t (App_t S_t (sk_bullet Ai))
         (sk_bullet Bi) via two SK_BULLET_APP_OTHER (App_t (App_t S_t
         Ai) Bi has 2 App layers, neither K- nor S-redex shape) +
         SK_BULLET_S_T.
      3. PAR_STEP_S_APP_APP_INV on h_A_bull (rewritten through (1)
         and (2)) : sk_par_step A1_in (sk_bullet Ai) and sk_par_step
         B1_in (sk_bullet Bi).
      4. PAR_S with X1 := sk_bullet Ai, Y1 := sk_bullet Bi, Z1 :=
         sk_bullet B.
      5. Fold to goal via SK_BULLET_S_REDEX.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
    )

    # ---- Step 1: invert h_A. -----------------------------------------
    p.have(
        "h_A_S: sk_par_step (App_t (App_t S_t Ai) Bi) A1"
    ).by_rewrite_of("h_A", [p.fact("Bi_eq")])
    p.have(
        "h_A1_shape: ?XP:nat0. ?YP:nat0. "
        "A1 = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step Ai XP /\\ sk_par_step Bi YP"
    ).by(PAR_STEP_S_APP_APP_INV, "Ai", "Bi", "A1", "h_A_S")
    p.choose("A1_in", from_="h_A1_shape")
    p.choose("B1_in", from_="A1_in_eq")
    p.split(
        "B1_in_eq",
        "(h_A1_eq, h_par_Ai_A1_in, h_par_Bi_B1_in)",
    )

    # ---- Step 2: compute sk_bullet (App_t (App_t S_t Ai) Bi). ---------
    # We need negation guards at two nesting levels.
    # First: App_t S_t Ai is not a K/S redex (1 App layer, S_t head).
    with p.have(
        "h_nK_SAi: ~(?a b. App_t S_t Ai = "
        "          App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex: ?a b. App_t S_t Ai = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                "h_inj: S_t = App_t K_t a /\\ Ai = b"
            ).by(
                APP_T_INJ, "S_t", "Ai",
                "App_t K_t a", "b", "b_eq",
            )
            p.have(
                "h_S_app: S_t = App_t K_t a"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_S_neq: ~(S_t = App_t K_t a)"
            ).by(S_T_NEQ_APP_T, "K_t", "a")
            p.absurd().by_conj("h_S_neq", "h_S_app")
    with p.have(
        "h_nS_SAi: ~(?a b c. App_t S_t Ai = "
        "          App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "ex: ?a b c. App_t S_t Ai = "
            "    App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_inj: S_t = App_t (App_t S_t a) b /\\ Ai = c"
            ).by(
                APP_T_INJ, "S_t", "Ai",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_S_app: S_t = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_S_neq: ~(S_t = App_t (App_t S_t a) b)"
            ).by(S_T_NEQ_APP_T, "App_t S_t a", "b")
            p.absurd().by_conj("h_S_neq", "h_S_app")
    p.have(
        "h_nKnS_SAi: "
        "~(?a b. App_t S_t Ai = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t S_t Ai = "
        "  App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact("h_nK_SAi"), p.fact("h_nS_SAi")))
    p.have(
        "h_bull_SAi_raw: sk_bullet (App_t S_t Ai) = "
        "                App_t (sk_bullet S_t) (sk_bullet Ai)"
    ).by(SK_BULLET_APP_OTHER, "S_t", "Ai", "h_nKnS_SAi")
    p.have(
        "h_bull_SAi: sk_bullet (App_t S_t Ai) = "
        "            App_t S_t (sk_bullet Ai)"
    ).by_rewrite_of("h_bull_SAi_raw", [SK_BULLET_S_T])

    # Next layer: App_t (App_t S_t Ai) Bi is not a K/S redex either.
    # K-redex check: needs App_t (App_t K_t _) _ at the top; here we
    # have App_t (App_t S_t Ai) Bi, so inner App's head is S_t.
    with p.have(
        "h_nK_SAB: ~(?a b. App_t (App_t S_t Ai) Bi = "
        "          App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex: ?a b. App_t (App_t S_t Ai) Bi = "
            "    App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                "h_inj1: App_t S_t Ai = App_t K_t a /\\ Bi = b"
            ).by(
                APP_T_INJ, "App_t S_t Ai", "Bi",
                "App_t K_t a", "b", "b_eq",
            )
            p.have(
                "h_inj1_L: App_t S_t Ai = App_t K_t a"
            ).by_thm(_C1(p.fact("h_inj1")))
            p.have(
                "h_inj2: S_t = K_t /\\ Ai = a"
            ).by(
                APP_T_INJ, "S_t", "Ai", "K_t", "a", "h_inj1_L"
            )
            p.have("h_SK: S_t = K_t").by_thm(_C1(p.fact("h_inj2")))
            p.absurd().by_conj(S_T_NEQ_K_T, "h_SK")
    # S-redex check: needs App_t (App_t (App_t S_t _) _) _ at the top.
    # Here we have App_t (App_t S_t Ai) Bi which has only 2 App layers.
    with p.have(
        "h_nS_SAB: ~(?a b c. App_t (App_t S_t Ai) Bi = "
        "          App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "ex: ?a b c. App_t (App_t S_t Ai) Bi = "
            "    App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_inj1: App_t S_t Ai = "
                "        App_t (App_t S_t a) b /\\ Bi = c"
            ).by(
                APP_T_INJ, "App_t S_t Ai", "Bi",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_inj1_L: App_t S_t Ai = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_inj1")))
            p.have(
                "h_inj2: S_t = App_t S_t a /\\ Ai = b"
            ).by(
                APP_T_INJ, "S_t", "Ai",
                "App_t S_t a", "b", "h_inj1_L",
            )
            p.have(
                "h_S_app: S_t = App_t S_t a"
            ).by_thm(_C1(p.fact("h_inj2")))
            p.have(
                "h_S_neq: ~(S_t = App_t S_t a)"
            ).by(S_T_NEQ_APP_T, "S_t", "a")
            p.absurd().by_conj("h_S_neq", "h_S_app")
    p.have(
        "h_nKnS_SAB: "
        "~(?a b. App_t (App_t S_t Ai) Bi = "
        "  App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t (App_t S_t Ai) Bi = "
        "  App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact("h_nK_SAB"), p.fact("h_nS_SAB")))
    p.have(
        "h_bull_SAB_raw: "
        "sk_bullet (App_t (App_t S_t Ai) Bi) = "
        "App_t (sk_bullet (App_t S_t Ai)) (sk_bullet Bi)"
    ).by(
        SK_BULLET_APP_OTHER, "App_t S_t Ai", "Bi", "h_nKnS_SAB"
    )
    p.have(
        "h_bull_SAB: sk_bullet (App_t (App_t S_t Ai) Bi) = "
        "            App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)"
    ).by_rewrite_of("h_bull_SAB_raw", [p.fact("h_bull_SAi")])

    # ---- Step 3: invert h_A_bull. -------------------------------------
    p.have(
        "h_bull_A_step1: "
        "sk_bullet A = sk_bullet (App_t (App_t S_t Ai) Bi)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("Bi_eq")))
    p.have(
        "h_bull_A: sk_bullet A = "
        "          App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)"
    ).by_trans("h_bull_A_step1", "h_bull_SAB")
    # Same DSL friction as the K-case: h_A1_eq has A1 free inside
    # the A1_in / B1_in @-binders' bodies.  Use by_cong + by_eq_mp.
    p.have(
        "h_A_bull_S_eq: "
        "sk_par_step A1 (sk_bullet A) = "
        "sk_par_step (App_t (App_t S_t A1_in) B1_in) "
        "            (App_t (App_t S_t (sk_bullet Ai)) "
        "                   (sk_bullet Bi))"
    ).by_cong(sk_par_step, "h_A1_eq", "h_bull_A")
    p.have(
        "h_A_bull_S: "
        "sk_par_step (App_t (App_t S_t A1_in) B1_in) "
        "            (App_t (App_t S_t (sk_bullet Ai)) "
        "                   (sk_bullet Bi))"
    ).by_eq_mp("h_A_bull_S_eq", "h_A_bull")
    p.have(
        "h_inv_A1: ?XP:nat0. ?YP:nat0. "
        "App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi) = "
        "  App_t (App_t S_t XP) YP /\\ "
        "sk_par_step A1_in XP /\\ sk_par_step B1_in YP"
    ).by(
        PAR_STEP_S_APP_APP_INV,
        "A1_in", "B1_in",
        "App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)",
        "h_A_bull_S",
    )
    p.choose("Xp", from_="h_inv_A1")
    p.choose("Yp", from_="Xp_eq")
    p.split(
        "Yp_eq", "(h_app_eq, h_par_A1in_Xp, h_par_B1in_Yp)"
    )
    # APP_T_INJ peel outer: App_t S_t (sk_bullet Ai) = App_t S_t Xp;
    # sk_bullet Bi = Yp.
    p.have(
        "h_inj1: App_t S_t (sk_bullet Ai) = App_t S_t Xp /\\ "
        "        sk_bullet Bi = Yp"
    ).by(
        APP_T_INJ,
        "App_t S_t (sk_bullet Ai)", "sk_bullet Bi",
        "App_t S_t Xp", "Yp", "h_app_eq",
    )
    p.have(
        "h_inj1_L: App_t S_t (sk_bullet Ai) = App_t S_t Xp"
    ).by_thm(_C1(p.fact("h_inj1")))
    p.have(
        "h_Yp_eq: sk_bullet Bi = Yp"
    ).by_thm(_C2(p.fact("h_inj1")))
    # APP_T_INJ peel inner: S_t = S_t; sk_bullet Ai = Xp.
    p.have(
        "h_inj2: S_t = S_t /\\ sk_bullet Ai = Xp"
    ).by(
        APP_T_INJ,
        "S_t", "sk_bullet Ai", "S_t", "Xp", "h_inj1_L",
    )
    p.have(
        "h_Xp_eq: sk_bullet Ai = Xp"
    ).by_thm(_C2(p.fact("h_inj2")))
    p.have(
        "h_par_A1in_bullAi: sk_par_step A1_in (sk_bullet Ai)"
    ).by_rewrite_of(
        "h_par_A1in_Xp", [SYM(p.fact("h_Xp_eq"))]
    )
    p.have(
        "h_par_B1in_bullBi: sk_par_step B1_in (sk_bullet Bi)"
    ).by_rewrite_of(
        "h_par_B1in_Yp", [SYM(p.fact("h_Yp_eq"))]
    )

    # ---- Step 4: PAR_S to assemble. -----------------------------------
    p.have(
        "h_conj_3: "
        "sk_par_step A1_in (sk_bullet Ai) /\\ "
        "sk_par_step B1_in (sk_bullet Bi) /\\ "
        "sk_par_step B1 (sk_bullet B)"
    ).by_thm(
        _CONJ(
            p.fact("h_par_A1in_bullAi"),
            _CONJ(
                p.fact("h_par_B1in_bullBi"),
                p.fact("h_B_bull"),
            ),
        )
    )
    p.have(
        "h_par_PAR_S: "
        "sk_par_step "
        "  (App_t (App_t (App_t S_t A1_in) B1_in) B1) "
        "  (App_t "
        "    (App_t (sk_bullet Ai) (sk_bullet B)) "
        "    (App_t (sk_bullet Bi) (sk_bullet B)))"
    ).by(
        PAR_S,
        "A1_in", "sk_bullet Ai",
        "B1_in", "sk_bullet Bi",
        "B1", "sk_bullet B",
        "h_conj_3",
    )

    # ---- Step 5: fold to the goal form. -------------------------------
    # App_t A B = App_t (App_t (App_t S_t Ai) Bi) B (S-redex).
    p.have(
        "h_AB_eq: App_t A B = "
        "         App_t (App_t (App_t S_t Ai) Bi) B"
    ).by_cong(App_t, "Bi_eq", REFL(p._parse("B")))
    # SK_BULLET_S_REDEX: sk_bullet of S-redex collapses.
    p.have(
        "h_bull_SAB_red: "
        "sk_bullet (App_t (App_t (App_t S_t Ai) Bi) B) = "
        "App_t "
        "  (App_t (sk_bullet Ai) (sk_bullet B)) "
        "  (App_t (sk_bullet Bi) (sk_bullet B))"
    ).by(SK_BULLET_S_REDEX, "Ai", "Bi", "B")
    p.have(
        "h_bull_AB_step1: sk_bullet (App_t A B) = "
        "sk_bullet (App_t (App_t (App_t S_t Ai) Bi) B)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("h_AB_eq")))
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = "
        "App_t "
        "  (App_t (sk_bullet Ai) (sk_bullet B)) "
        "  (App_t (sk_bullet Bi) (sk_bullet B))"
    ).by_trans("h_bull_AB_step1", "h_bull_SAB_red")
    # SYM(h_A1_eq) rewrites App_t (App_t S_t A1_in) B1_in -> A1.
    # SYM(h_bull_AB) rewrites the App-of-Apps RHS -> sk_bullet (App A B).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_S",
        [SYM(p.fact("h_A1_eq")), SYM(p.fact("h_bull_AB"))],
    )


def _triangle_other_case(p):
    """App-other sub-case of _TRIANGLE_APP_CLOSURE.

    Context: ``h_nAisK : ~(?Ai. A = App_t K_t Ai)``,
             ``h_nAisSS : ~(?Ai Bi. A = App_t (App_t S_t Ai) Bi)``.

    App_t A B is then neither a K-redex (would require A = App_t K_t
    _) nor an S-redex (would require A = App_t (App_t S_t _) _).
    SK_BULLET_APP_OTHER + PAR_APP on (h_A_bull, h_B_bull) closes.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
    )

    # Lift the A-shape negations to App_t A B negations.
    with p.have(
        "h_nK_AB: ~(?a b. App_t A B = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex: ?a b. App_t A B = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                "h_inj: A = App_t K_t a /\\ B = b"
            ).by(
                APP_T_INJ, "A", "B",
                "App_t K_t a", "b", "b_eq",
            )
            p.have("h_A_eq: A = App_t K_t a").by_thm(
                _C1(p.fact("h_inj"))
            )
            p.have(
                "h_ex_Ai: ?Ai:nat0. A = App_t K_t Ai"
            ).by_exists(["a"], "h_A_eq")
            p.absurd().by_conj("h_nAisK", "h_ex_Ai")
    with p.have(
        "h_nS_AB: ~(?a b c. App_t A B = "
        "          App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "ex: ?a b c. App_t A B = "
            "    App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_inj: A = App_t (App_t S_t a) b /\\ B = c"
            ).by(
                APP_T_INJ, "A", "B",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_A_eq: A = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_ex_AiBi: "
                "?Ai:nat0. ?Bi:nat0. "
                "A = App_t (App_t S_t Ai) Bi"
            ).by_exists(["a", "b"], "h_A_eq")
            p.absurd().by_conj("h_nAisSS", "h_ex_AiBi")
    p.have(
        "h_nKnS_AB: "
        "~(?a b. App_t A B = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t A B = "
        "  App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact("h_nK_AB"), p.fact("h_nS_AB")))

    # SK_BULLET_APP_OTHER: sk_bullet (App_t A B) = App_t (sk_bullet
    # A) (sk_bullet B).
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = "
        "           App_t (sk_bullet A) (sk_bullet B)"
    ).by(SK_BULLET_APP_OTHER, "A", "B", "h_nKnS_AB")
    # PAR_APP combines the two triangle conclusions on the children.
    p.have(
        "h_conj_AB_bull: "
        "sk_par_step A1 (sk_bullet A) /\\ "
        "sk_par_step B1 (sk_bullet B)"
    ).by_thm(_CONJ(p.fact("h_A_bull"), p.fact("h_B_bull")))
    p.have(
        "h_par_PAR_APP: sk_par_step (App_t A1 B1) "
        "                          (App_t (sk_bullet A) (sk_bullet B))"
    ).by(
        PAR_APP,
        "A1", "sk_bullet A", "B1", "sk_bullet B",
        "h_conj_AB_bull",
    )
    # Fold RHS App_t (sk_bullet A) (sk_bullet B) -> sk_bullet (App_t A B).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_APP", [SYM(p.fact("h_bull_AB"))]
    )


@proof
def _TRIANGLE_APP_CLOSURE(p):
    """The APP-rule closure conjunct of TRIANGLE's P-instantiation:

    |- !A B A1 B1.
         (sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\
         (sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==>
         sk_par_step (App_t A B) (App_t A1 B1) /\\
         sk_par_step (App_t A1 B1) (sk_bullet (App_t A B)).

    Part 1 (sk_par_step (App_t A B) (App_t A1 B1)) is just PAR_APP on
    the two source par-steps.

    Part 2 is a 3-way LEM split on ``A``'s shape (which determines
    whether ``App_t A B`` is a K-redex, S-redex, or App-other):

      * A = App_t K_t Ai           -> _triangle_K_case
      * A = App_t (App_t S_t Ai) Bi -> _triangle_S_case
      * otherwise                  -> _triangle_other_case
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ

    p.goal(
        "!A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==> "
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    )
    p.fix("A B A1 B1")
    p.assume(
        "((h_A, h_A_bull), (h_B, h_B_bull)): "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B))"
    )

    # ---- Part 1: sk_par_step (App_t A B) (App_t A1 B1) ---------------
    p.have(
        "h_conj_AB: sk_par_step A A1 /\\ sk_par_step B B1"
    ).by_thm(_CONJ(p.fact("h_A"), p.fact("h_B")))
    p.have(
        "h_part1: sk_par_step (App_t A B) (App_t A1 B1)"
    ).by(
        PAR_APP, "A", "A1", "B", "B1", "h_conj_AB"
    )

    # ---- Part 2: 3-way LEM split on A's shape ------------------------
    with p.have(
        "h_part2: sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).proof():
        with p.cases_on(
            EXCLUDED_MIDDLE, "?Ai:nat0. A = App_t K_t Ai"
        ):
            with p.case("h_AisK: ?Ai:nat0. A = App_t K_t Ai"):
                # cases_on auto-binds Ai; Ai_eq: A = App_t K_t Ai.
                _triangle_K_case(p)
            with p.case(
                "h_nAisK: ~(?Ai:nat0. A = App_t K_t Ai)"
            ):
                with p.cases_on(
                    EXCLUDED_MIDDLE,
                    "?Ai:nat0. ?Bi:nat0. "
                    "A = App_t (App_t S_t Ai) Bi",
                ):
                    with p.case(
                        "h_AisSS: ?Ai:nat0. ?Bi:nat0. "
                        "A = App_t (App_t S_t Ai) Bi"
                    ):
                        # Ai auto-bound; manual choose Bi in S-case.
                        p.choose("Bi", from_="Ai_eq")
                        _triangle_S_case(p)
                    with p.case(
                        "h_nAisSS: "
                        "~(?Ai:nat0. ?Bi:nat0. "
                        "  A = App_t (App_t S_t Ai) Bi)"
                    ):
                        _triangle_other_case(p)

    p.thus(
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_thm(_CONJ(p.fact("h_part1"), p.fact("h_part2")))


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
      APP-rule -- delegated to ``_TRIANGLE_APP_CLOSURE``.

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

    # APP-rule conjunct: delegated to _TRIANGLE_APP_CLOSURE.  Its bvars
    # (A B A1 B1) do not need renaming -- this is a by_thm with a
    # stand-alone lemma; the inner !A binders stay bound, alpha-equivalent
    # to closures_beta.
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
# Diamond / confluence theorems for ``sk_par_step``, built on
# SK_BULLET_TRIANGLE:
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
# par/bullet bridge: PAR_STEPS_TRANS (composition) and
# NORMAL_STABILITY_PAR_STEPS (par-step from a normal goes nowhere).
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
def _is_normal_rec_body(t):
    """Body of IS_NORMAL_REC at term ``t``, as a parser-ready string."""
    nK = f"~(?u v. {t} = App_t (App_t K_t u) v)"
    nS = f"~(?u v w. {t} = App_t (App_t (App_t S_t u) v) w)"
    Dapp_inner = f"?a b. {t} = App_t a b /\\ is_normal a /\\ is_normal b"
    D1 = f"{t} = S_t"
    D2 = f"{t} = K_t"
    D3 = f"({nK}) /\\ ({nS}) /\\ ({Dapp_inner})"
    return D1, D2, D3


@proof
def IS_NORMAL_NOT_K_REDEX_SHAPE(p):
    """|- !M N. ~is_normal (App_t (App_t K_t M) N).

    Unfold via IS_NORMAL_REC.  D1 (t = S_t) / D2 (t = K_t) refuted by
    S_T_NEQ_APP_T / K_T_NEQ_APP_T.  D3 carries the ~K-redex guard,
    immediately contradicted by witnessing (M, N).
    """
    p.goal("!M:nat0. !N:nat0. ~is_normal (App_t (App_t K_t M) N)")
    p.fix("M N")
    t = "App_t (App_t K_t M) N"
    with p.suppose(f"h_norm: is_normal ({t})"):
        spec = SPEC(p._parse(t), IS_NORMAL_REC)
        D1, D2, D3 = _is_normal_rec_body(t)
        p.have(f"h_body: ({D1}) \\/ ({D2}) \\/ ({D3})").by_thm(
            EQ_MP(spec, p.fact("h_norm"))
        )
        with p.cases_on("h_body"):
            with p.case(f"h1: {D1}"):
                p.have(f"h_sym: S_t = {t}").by_thm(SYM(p.fact("h1")))
                p.have(f"h_neq: ~(S_t = {t})").by(
                    S_T_NEQ_APP_T, "App_t K_t M", "N"
                )
                p.absurd().by_conj("h_neq", "h_sym")
            with p.case(f"h2: {D2}"):
                p.have(f"h_sym: K_t = {t}").by_thm(SYM(p.fact("h2")))
                p.have(f"h_neq: ~(K_t = {t})").by(
                    K_T_NEQ_APP_T, "App_t K_t M", "N"
                )
                p.absurd().by_conj("h_neq", "h_sym")
            with p.case(f"h3: {D3}"):
                p.split("h3", "(h_nK, _, _)")
                p.have(
                    f"h_K: ?u v. {t} = App_t (App_t K_t u) v"
                ).by_exists(["M", "N"], REFL(p._parse(t)))
                p.absurd().by_conj("h_nK", "h_K")


@proof
def IS_NORMAL_NOT_S_REDEX_SHAPE(p):
    """|- !M N P. ~is_normal (App_t (App_t (App_t S_t M) N) P).

    Same shape as IS_NORMAL_NOT_K_REDEX_SHAPE; D3's ~S-redex guard
    contradicted by witnessing (M, N, P).
    """
    p.goal(
        "!M:nat0. !N:nat0. !P:nat0. "
        "~is_normal (App_t (App_t (App_t S_t M) N) P)"
    )
    p.fix("M N P")
    t = "App_t (App_t (App_t S_t M) N) P"
    with p.suppose(f"h_norm: is_normal ({t})"):
        spec = SPEC(p._parse(t), IS_NORMAL_REC)
        D1, D2, D3 = _is_normal_rec_body(t)
        p.have(f"h_body: ({D1}) \\/ ({D2}) \\/ ({D3})").by_thm(
            EQ_MP(spec, p.fact("h_norm"))
        )
        with p.cases_on("h_body"):
            with p.case(f"h1: {D1}"):
                p.have(f"h_sym: S_t = {t}").by_thm(SYM(p.fact("h1")))
                p.have(f"h_neq: ~(S_t = {t})").by(
                    S_T_NEQ_APP_T, "App_t (App_t S_t M) N", "P"
                )
                p.absurd().by_conj("h_neq", "h_sym")
            with p.case(f"h2: {D2}"):
                p.have(f"h_sym: K_t = {t}").by_thm(SYM(p.fact("h2")))
                p.have(f"h_neq: ~(K_t = {t})").by(
                    K_T_NEQ_APP_T, "App_t (App_t S_t M) N", "P"
                )
                p.absurd().by_conj("h_neq", "h_sym")
            with p.case(f"h3: {D3}"):
                p.split("h3", "(_, h_nS, _)")
                p.have(
                    f"h_S: ?u v w. {t} = "
                    f"      App_t (App_t (App_t S_t u) v) w"
                ).by_exists(["M", "N", "P"], REFL(p._parse(t)))
                p.absurd().by_conj("h_nS", "h_S")


@proof
def IS_NORMAL_APP_DECOMP(p):
    """|- !A B. is_normal (App_t A B) ==> is_normal A /\\ is_normal B.

    Unfold IS_NORMAL_REC at App_t A B.  Atom disjuncts refuted by
    S_T_NEQ_APP_T / K_T_NEQ_APP_T.  D3 yields witnesses a, b with
    App_t A B = App_t a b and is_normal a /\\ is_normal b; APP_T_INJ
    identifies a = A, b = B.
    """
    p.goal(
        "!A:nat0. !B:nat0. "
        "is_normal (App_t A B) ==> is_normal A /\\ is_normal B"
    )
    p.fix("A B")
    p.assume("h_norm_AB: is_normal (App_t A B)")
    t = "App_t A B"
    spec = SPEC(p._parse(t), IS_NORMAL_REC)
    D1, D2, D3 = _is_normal_rec_body(t)
    p.have(f"h_body: ({D1}) \\/ ({D2}) \\/ ({D3})").by_thm(
        EQ_MP(spec, p.fact("h_norm_AB"))
    )
    with p.cases_on("h_body"):
        with p.case(f"h1: {D1}"):
            p.have(f"h_sym: S_t = {t}").by_thm(SYM(p.fact("h1")))
            p.have(f"h_neq: ~(S_t = {t})").by(S_T_NEQ_APP_T, "A", "B")
            p.absurd().by_conj("h_neq", "h_sym")
        with p.case(f"h2: {D2}"):
            p.have(f"h_sym: K_t = {t}").by_thm(SYM(p.fact("h2")))
            p.have(f"h_neq: ~(K_t = {t})").by(K_T_NEQ_APP_T, "A", "B")
            p.absurd().by_conj("h_neq", "h_sym")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h_inner)")
            p.choose("a", from_="h_inner")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, h_norm_a, h_norm_b)")
            p.have("h_inj: A = a /\\ B = b").by(
                APP_T_INJ, "A", "B", "a", "b", "h_app"
            )
            p.split("h_inj", "(h_Aa, h_Bb)")
            p.have("h_norm_A: is_normal A").by_rewrite_of(
                "h_norm_a", [SYM(p.fact("h_Aa"))]
            )
            p.have("h_norm_B: is_normal B").by_rewrite_of(
                "h_norm_b", [SYM(p.fact("h_Bb"))]
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
# Stage 5 -- halting predicate.
#
#   bullet_iter 0        = \t. t
#   bullet_iter (SUC0 n) = \t. sk_bullet (bullet_iter n t)
#   halts_b t            := ?n. is_normal (bullet_iter n t)
#
# Takahashi-strategy halting: a term halts iff its deterministic
# parallel-development trajectory reaches normal form.  Classically
# equivalent to LMO halting (by standardization), but the bullet form
# sidesteps the standardization bridge entirely on the undecidability
# critical path.  See iter_to_bullet.md for the design history.
#
# This block ships the recursion equations for bullet_iter, the halts_b
# unfold (HALTS_B_AT), and the par-form halts_par which is bridged to
# halts_b via HALTS_B_IFF_HALTS_PAR.
# ---------------------------------------------------------------------------

from nat0 import define_unary_0  # noqa: E402

_n0_t_var = Var("t", nat0_ty)
_n0_k_var = Var("k", nat0_ty)
_n0_a_var = Var("a", parse_type("nat0 -> nat0"))

# c : nat0 -> nat0  ==  \t. t.
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
    """|- !t. bullet_iter 0 t = t."""
    from tactics import AP_THM, BETA_CONV, TRANS, GEN

    ap = AP_THM(BULLET_ITER_BASE, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. bullet_iter 0 t = t")
    p.thus("!t. bullet_iter 0 t = t").by_thm(GEN(_n0_t_var, spec_th))


@proof
def BULLET_ITER_SUC(p):
    """|- !n t. bullet_iter (SUC0 n) t = sk_bullet (bullet_iter n t).

    SPEC BULLET_ITER_STEP at n, AP_THM at t, BETA.
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

    Direct unfold of HALTS_B_DEF via AP_THM + BETA.
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
# Par-side of the bullet/par bridge HALTS_B_IFF_HALTS_PAR.
HALTS_PAR_DEF = define(
    "halts_par",
    parse_type("nat0 -> bool"),
    "\\t:nat0. ?N:nat0. sk_par_steps t N /\\ is_normal N",
)
halts_par = mk_const("halts_par", [])


@proof
def HALTS_PAR_AT(p):
    """|- !t. halts_par t = (?N. sk_par_steps t N /\\ is_normal N).

    Direct unfold of HALTS_PAR_DEF via AP_THM + BETA.
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
def _BULLET_TRAJ_PAR_STEPS(p):
    """|- !n X. sk_par_steps X (bullet_iter n X).

    The bullet trajectory rooted at X is a par-step RTC chain: each
    iterate is one par-step ahead of the previous (BULLET_REFL).
    Induction on ``n``:

      base : bullet_iter 0 X = X (BULLET_ITER_ZERO); PAR_STEPS_REFL.
      step : IH says sk_par_steps X (bullet_iter n X).  BULLET_REFL
             specialised at ``bullet_iter n X`` gives the single
             par-step to ``sk_bullet (bullet_iter n X)`` = bullet_iter
             (SUC0 n) X (BULLET_ITER_SUC); PAR_STEPS_TRANS composes.
    """
    from tactics import CONJ as _CONJ

    p.goal("!n:nat0. !X:nat0. sk_par_steps X (bullet_iter n X)")
    with p.induction("n"):
        with p.base():
            p.fix("X")
            p.have(
                "h_base: bullet_iter 0 X = X"
            ).by(BULLET_ITER_ZERO, "X")
            p.have("h_XX: sk_par_steps X X").by(PAR_STEPS_REFL, "X")
            # DSL friction: by_rewrite_of with SYM(h_base) would
            # rewrite ``X -> bullet_iter 0 X`` non-terminatingly
            # (RHS contains X).  Lift via AP_TERM at the
            # ``sk_par_steps X _`` slot and let by_eq_mp's
            # sym-tolerance pick the matching side.
            p.thus(
                "sk_par_steps X (bullet_iter 0 X)"
            ).by_eq_mp(
                AP_TERM(
                    p._parse("sk_par_steps X"),
                    p.fact("h_base"),
                ),
                "h_XX",
            )
        with p.step("IH"):
            # IH : !X. sk_par_steps X (bullet_iter n X).
            p.fix("X")
            p.have(
                "h_ih: sk_par_steps X (bullet_iter n X)"
            ).by("IH", "X")
            p.have(
                "h_unfold: bullet_iter (SUC0 n) X = "
                "          sk_bullet (bullet_iter n X)"
            ).by(BULLET_ITER_SUC, "n", "X")
            p.have(
                "h_par1: sk_par_step (bullet_iter n X) "
                "                    (sk_bullet (bullet_iter n X))"
            ).by_thm(
                SPEC(p._parse("bullet_iter n X"), BULLET_REFL)
            )
            p.have(
                "h_par1s: sk_par_steps (bullet_iter n X) "
                "                     (sk_bullet (bullet_iter n X))"
            ).by(
                PAR_STEP_TO_STEPS,
                "bullet_iter n X",
                "sk_bullet (bullet_iter n X)",
                "h_par1",
            )
            p.have(
                "h_conj: sk_par_steps X (bullet_iter n X) /\\ "
                "        sk_par_steps (bullet_iter n X) "
                "                     (sk_bullet (bullet_iter n X))"
            ).by_thm(_CONJ(p.fact("h_ih"), p.fact("h_par1s")))
            p.have(
                "h_chain: "
                "sk_par_steps X (sk_bullet (bullet_iter n X))"
            ).by(
                PAR_STEPS_TRANS,
                "X", "bullet_iter n X",
                "sk_bullet (bullet_iter n X)",
                "h_conj",
            )
            p.thus(
                "sk_par_steps X (bullet_iter (SUC0 n) X)"
            ).by_rewrite_of(
                "h_chain", [SYM(p.fact("h_unfold"))]
            )


@proof
def _BULLET_COMMUTES_PAR_STEP(p):
    """|- !X Y. sk_par_step X Y ==> sk_par_step (sk_bullet X) (sk_bullet Y).

    Two applications of SK_BULLET_TRIANGLE:
      * TRIANGLE on par_step X Y           : par_step Y (sk_bullet X).
      * TRIANGLE on par_step Y (sk_bullet X): par_step (sk_bullet X) (sk_bullet Y).
    """
    p.goal(
        "!X:nat0. !Y:nat0. sk_par_step X Y ==> "
        "sk_par_step (sk_bullet X) (sk_bullet Y)"
    )
    p.fix("X Y")
    p.assume("h_XY: sk_par_step X Y")
    p.have(
        "h_T1: sk_par_step Y (sk_bullet X)"
    ).by(SK_BULLET_TRIANGLE, "X", "Y", "h_XY")
    p.thus(
        "sk_par_step (sk_bullet X) (sk_bullet Y)"
    ).by(SK_BULLET_TRIANGLE, "Y", "sk_bullet X", "h_T1")


@proof
def _BULLET_ITER_COMMUTES_PAR_STEP(p):
    """|- !n X Y. sk_par_step X Y ==>
                   sk_par_step (bullet_iter n X) (bullet_iter n Y).

    nat0 induction on n lifts ``_BULLET_COMMUTES_PAR_STEP`` to bullet
    iterates.  Base: bullet_iter 0 _ = _ (BULLET_ITER_ZERO) + h_XY +
    congruence (by_cong + by_eq_mp).  Step: IH at (X, Y) gives the
    par-step between iterates; apply the per-step commute helper at
    that par-step; fold sk_bullet (bullet_iter n _) to bullet_iter
    (SUC0 n) _ via BULLET_ITER_SUC.
    """
    p.goal(
        "!n:nat0. !X:nat0. !Y:nat0. sk_par_step X Y ==> "
        "sk_par_step (bullet_iter n X) (bullet_iter n Y)"
    )
    with p.induction("n"):
        with p.base():
            p.fix("X Y")
            p.assume("h_XY: sk_par_step X Y")
            p.have(
                "h_z0X: bullet_iter 0 X = X"
            ).by(BULLET_ITER_ZERO, "X")
            p.have(
                "h_z0Y: bullet_iter 0 Y = Y"
            ).by(BULLET_ITER_ZERO, "Y")
            # DSL friction: by_rewrite_of with SYM(h_z0X) would
            # rewrite ``X -> bullet_iter 0 X`` non-terminatingly.
            # Use by_cong's binop shorthand to build the equation
            # ``sk_par_step (bullet_iter 0 X) (bullet_iter 0 Y) =
            # sk_par_step X Y`` then by_eq_mp's sym-tolerance closes.
            p.have(
                "h_cong: "
                "sk_par_step (bullet_iter 0 X) (bullet_iter 0 Y) = "
                "sk_par_step X Y"
            ).by_cong(sk_par_step, "h_z0X", "h_z0Y")
            p.thus(
                "sk_par_step (bullet_iter 0 X) (bullet_iter 0 Y)"
            ).by_eq_mp("h_cong", "h_XY")
        with p.step("IH"):
            # IH : !X Y. sk_par_step X Y ==>
            #             sk_par_step (bullet_iter n X) (bullet_iter n Y).
            p.fix("X Y")
            p.assume("h_XY: sk_par_step X Y")
            p.have(
                "h_ih: "
                "sk_par_step (bullet_iter n X) (bullet_iter n Y)"
            ).by("IH", "X", "Y", "h_XY")
            p.have(
                "h_step: sk_par_step "
                "(sk_bullet (bullet_iter n X)) "
                "(sk_bullet (bullet_iter n Y))"
            ).by(
                _BULLET_COMMUTES_PAR_STEP,
                "bullet_iter n X", "bullet_iter n Y", "h_ih",
            )
            p.have(
                "h_unfX: bullet_iter (SUC0 n) X = "
                "        sk_bullet (bullet_iter n X)"
            ).by(BULLET_ITER_SUC, "n", "X")
            p.have(
                "h_unfY: bullet_iter (SUC0 n) Y = "
                "        sk_bullet (bullet_iter n Y)"
            ).by(BULLET_ITER_SUC, "n", "Y")
            p.have(
                "h_cong: "
                "sk_par_step "
                "  (bullet_iter (SUC0 n) X) "
                "  (bullet_iter (SUC0 n) Y) = "
                "sk_par_step "
                "  (sk_bullet (bullet_iter n X)) "
                "  (sk_bullet (bullet_iter n Y))"
            ).by_cong(sk_par_step, "h_unfX", "h_unfY")
            p.thus(
                "sk_par_step "
                "(bullet_iter (SUC0 n) X) "
                "(bullet_iter (SUC0 n) Y)"
            ).by_eq_mp("h_cong", "h_step")


@proof
def _HALTS_PAR_TO_HALTS_B(p):
    """|- !X. halts_par X ==> halts_b X.

    Backward direction of the bullet/par bridge.  Impredicative
    induction on ``sk_par_steps X N`` with the strengthened invariant:

        P := \\A B. is_normal B ==> ?m. is_normal (bullet_iter m A).

    REFL  Z : is_normal Z ==> ?m. is_normal (bullet_iter m Z).
            Take m := 0 (BULLET_ITER_ZERO).
    STEP a -> b /\\ P b c ==> P a c : assume is_normal c; IH at b
            yields ?m_B. is_normal (bullet_iter m_B b).  Lift
            par_step a b to par_step (bullet_iter m_B a) (bullet_iter
            m_B b) via _BULLET_ITER_COMMUTES_PAR_STEP; SK_BULLET_TRIANGLE
            on that par-step gives par_step (bullet_iter m_B b)
            (sk_bullet (bullet_iter m_B a)) = par_step (bullet_iter
            m_B b) (bullet_iter (SUC0 m_B) a).  is_normal at the LHS
            of this par-step + NORMAL_STABILITY_PAR_STEP forces
            bullet_iter (SUC0 m_B) a = bullet_iter m_B b, transporting
            normality across.  Witness m := SUC0 m_B.

    With P instantiated, the closures conjunction + impredicative MP
    yields P X N; applied at is_normal N, the conclusion is
    ?m. is_normal (bullet_iter m X), which is halts_b X via HALTS_B_AT.
    """
    from tactics import BETA_RULE

    p.goal("!X. halts_par X ==> halts_b X")
    p.fix("X")
    p.assume("h_hp: halts_par X")

    # Unfold halts_par X to extract the par-chain to a normal form.
    p.have(
        "h_at_par: halts_par X = "
        "(?N. sk_par_steps X N /\\ is_normal N)"
    ).by(HALTS_PAR_AT, "X")
    p.have(
        "h_ex_par: ?N. sk_par_steps X N /\\ is_normal N"
    ).by_eq_mp("h_at_par", "h_hp")
    p.choose("N", from_="h_ex_par")
    p.split("N_eq", "(h_XN, h_norm_N)")

    # ---- Impredicative induction setup (mirrors NORMAL_STABILITY_PAR_STEPS).
    spec_XN = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("N")
    )
    h_forall = EQ_MP(spec_XN, p.fact("h_XN"))
    # h_forall : !P. closures(P) ==> P X N.

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "is_normal B ==> ?m:nat0. is_normal (bullet_iter m A)"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)
    # inst_beta : closures(P_lifted) ==> (is_normal N ==>
    #                                      ?m. is_normal (bullet_iter m X)).

    # ---- REFL closure ---------------------------------------------------
    with p.have(
        "lifted_refl: "
        "!Z:nat0. is_normal Z ==> ?m:nat0. is_normal (bullet_iter m Z)"
    ).proof():
        p.fix("Z")
        p.assume("h_norm_Z: is_normal Z")
        p.have(
            "h_z0Z: bullet_iter 0 Z = Z"
        ).by(BULLET_ITER_ZERO, "Z")
        # is_normal Z transported back to is_normal (bullet_iter 0 Z)
        # via AP_TERM (sym-tolerant by_eq_mp picks the matching side).
        p.have(
            "h_norm_0: is_normal (bullet_iter 0 Z)"
        ).by_eq_mp(
            AP_TERM(is_normal, p.fact("h_z0Z")),
            "h_norm_Z",
        )
        p.thus(
            "?m:nat0. is_normal (bullet_iter m Z)"
        ).by_witness("0", "h_norm_0")

    # ---- STEP closure ---------------------------------------------------
    with p.have(
        "lifted_step: "
        "!a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(is_normal c ==> ?m:nat0. is_normal (bullet_iter m b)) ==> "
        "(is_normal c ==> ?m:nat0. is_normal (bullet_iter m a))"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(is_normal c ==> ?m:nat0. is_normal (bullet_iter m b))"
        )
        p.assume("h_norm_c: is_normal c")

        # IH gives a bullet-normal index for b.
        p.have(
            "h_ex_b: ?m:nat0. is_normal (bullet_iter m b)"
        ).by("h_IH", "h_norm_c")
        p.choose("m_B", from_="h_ex_b")
        # m_B_eq : is_normal (bullet_iter m_B b).

        # Commute par_step a b through bullet_iter m_B on both sides.
        p.have(
            "h_par_iter: "
            "sk_par_step (bullet_iter m_B a) (bullet_iter m_B b)"
        ).by(
            _BULLET_ITER_COMMUTES_PAR_STEP,
            "m_B", "a", "b", "h_ab",
        )
        # TRIANGLE: from par_step (bullet_iter m_B a) (bullet_iter m_B b),
        # get par_step (bullet_iter m_B b) (sk_bullet (bullet_iter m_B a)).
        p.have(
            "h_T: sk_par_step "
            "  (bullet_iter m_B b) "
            "  (sk_bullet (bullet_iter m_B a))"
        ).by(
            SK_BULLET_TRIANGLE,
            "bullet_iter m_B a",
            "bullet_iter m_B b",
            "h_par_iter",
        )
        # Fold sk_bullet (bullet_iter m_B a) to bullet_iter (SUC0 m_B) a.
        p.have(
            "h_unf: bullet_iter (SUC0 m_B) a = "
            "       sk_bullet (bullet_iter m_B a)"
        ).by(BULLET_ITER_SUC, "m_B", "a")
        p.have(
            "h_T2: sk_par_step "
            "  (bullet_iter m_B b) "
            "  (bullet_iter (SUC0 m_B) a)"
        ).by_rewrite_of("h_T", [SYM(p.fact("h_unf"))])
        # NORMAL_STABILITY_PAR_STEP: is_normal LHS + par-step LHS -> RHS
        # forces RHS = LHS.
        p.have(
            "h_conj_stab: "
            "is_normal (bullet_iter m_B b) /\\ "
            "sk_par_step (bullet_iter m_B b) (bullet_iter (SUC0 m_B) a)"
        ).by_thm(CONJ(p.fact("m_B_eq"), p.fact("h_T2")))
        p.have(
            "h_eq: bullet_iter (SUC0 m_B) a = bullet_iter m_B b"
        ).by(
            NORMAL_STABILITY_PAR_STEP,
            "bullet_iter m_B b",
            "bullet_iter (SUC0 m_B) a",
            "h_conj_stab",
        )
        # Transport normality across h_eq (sym-tolerant by_eq_mp).
        p.have(
            "h_norm_SUC: is_normal (bullet_iter (SUC0 m_B) a)"
        ).by_eq_mp(
            AP_TERM(is_normal, p.fact("h_eq")),
            "m_B_eq",
        )
        p.thus(
            "?m:nat0. is_normal (bullet_iter m a)"
        ).by_witness("SUC0 m_B", "h_norm_SUC")

    # ---- Bundle closures and discharge P X N ----------------------------
    p.have(
        "lifted_cl: "
        "(!Z:nat0. is_normal Z ==> "
        "          ?m:nat0. is_normal (bullet_iter m Z)) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (is_normal c ==> "
        "        ?m:nat0. is_normal (bullet_iter m b)) ==> "
        "    (is_normal c ==> "
        "        ?m:nat0. is_normal (bullet_iter m a)))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXN: is_normal N ==> ?m:nat0. is_normal (bullet_iter m X)"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.have(
        "h_ex_bull: ?m:nat0. is_normal (bullet_iter m X)"
    ).by("h_PXN", "h_norm_N")

    # Witness halts_b X via HALTS_B_AT.
    p.have(
        "h_at_b: halts_b X = (?n. is_normal (bullet_iter n X))"
    ).by(HALTS_B_AT, "X")
    p.thus("halts_b X").by_eq_mp("h_at_b", "h_ex_bull")


@proof
def HALTS_B_IFF_HALTS_PAR(p):
    """|- !X. halts_b X = halts_par X.

    The bullet/par halt-bridge.  Iff-intro on the two directions:

    Forward (halts_b X ==> halts_par X).  Unfold halts_b X to
    ``?n. is_normal (bullet_iter n X)``; choose n; witness halts_par X
    at N := bullet_iter n X using _BULLET_TRAJ_PAR_STEPS for the
    sk_par_steps witness.

    Backward (halts_par X ==> halts_b X).  Delegated to the helper
    ``_HALTS_PAR_TO_HALTS_B``, which uses the Takahashi confluence
    argument via SK_BULLET_TRIANGLE.
    """
    p.goal("!X. halts_b X = halts_par X")
    p.fix("X")

    # ---- Forward direction ----------------------------------------------
    with p.have(
        "h_fwd: halts_b X ==> halts_par X"
    ).proof():
        p.assume("h_hb: halts_b X")
        # Unfold halts_b X.
        p.have(
            "h_at_b: halts_b X = "
            "(?n. is_normal (bullet_iter n X))"
        ).by(HALTS_B_AT, "X")
        p.have(
            "h_ex_b: ?n. is_normal (bullet_iter n X)"
        ).by_eq_mp("h_at_b", "h_hb")
        p.choose("n", from_="h_ex_b")
        # n_eq : is_normal (bullet_iter n X).

        # The bullet trajectory is itself a par-chain.
        p.have(
            "h_traj: sk_par_steps X (bullet_iter n X)"
        ).by(_BULLET_TRAJ_PAR_STEPS, "n", "X")

        # Witness halts_par X at N := bullet_iter n X.
        p.have(
            "h_at_par: halts_par X = "
            "(?N. sk_par_steps X N /\\ is_normal N)"
        ).by(HALTS_PAR_AT, "X")
        p.have(
            "h_ex_par: ?N. sk_par_steps X N /\\ is_normal N"
        ).by_exists(["bullet_iter n X"], "h_traj", "n_eq")
        p.thus("halts_par X").by_eq_mp("h_at_par", "h_ex_par")

    # ---- Backward direction ---------------------------------------------
    p.have(
        "h_bwd: halts_par X ==> halts_b X"
    ).by(_HALTS_PAR_TO_HALTS_B, "X")

    p.thus("halts_b X = halts_par X").by_iff("h_fwd", "h_bwd")


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

    Stays inside the par calculus.
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


# ---------------------------------------------------------------------------
# Stage 6 -- the diagonal.
#
# ``halts_decider H`` says H is an SK term that decides halting via the
# flipped halting-status output convention:
# ``halts_b t  iff  ~halts_b (App_t H t)``.  The flipped convention
# turns the diagonal equation ``halts_b d = halts_b (App_t H d)`` into
# a ``P = ~P`` contradiction directly, no Church-bool case-split needed.
# ---------------------------------------------------------------------------
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

    Direct unfold of HALTS_DECIDER_DEF via AP_THM + BETA.
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

    Why par and not bullet: ``PAR_REFL`` lets ``H`` stay un-reduced
    inside the residue, which is what makes the diagonal work for
    arbitrary ``is_sk_term H``.  Bullet's eager-everywhere semantics
    would reduce composite ``H`` mid-trajectory and break the equation
    (empirically falsified in ``outside/sk_par.py`` EXP 5/6).  The
    par-to-bullet bridge ``HALTS_B_IFF_HALTS_PAR`` downstream lifts
    the par chain to a ``halts_b`` equality; see
    ``DIAGONAL_TERM_EXISTS``.
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
def DIAGONAL_TERM_EXISTS(p):
    """|- !H. is_sk_term H ==>
              ?d. is_sk_term d /\\ halts_b d = halts_b (App_t H d).

    Halts-form diagonal in the bullet halting convention.  Combines:

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

    Proof (5-step contradiction):

      Assume H with halts_decider H.  Unfold the (flipped, bullet-form)
      spec via HALTS_DECIDER_DEF_THM:
        is_sk_term H  /\\  !t. is_sk_term t ==>
                              halts_b t = ~halts_b (App_t H t).

      Build the classical Curry diagonal via DIAGONAL_TERM_EXISTS at H:
        ?d. is_sk_term d /\\ halts_b d = halts_b (App_t H d).

      Specialise the decider spec at t := d:
        halts_b d = ~halts_b (App_t H d).

      Combining: halts_b (App_t H d) = ~halts_b (App_t H d).
      Discharge via EXCLUDED_MIDDLE on halts_b (App_t H d).
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


if __name__ == "__main__":
    from parser import pp_thm
    print("HALTS_DECIDER_DEF        :", pp_thm(HALTS_DECIDER_DEF))
    print("DIAG_TERM                :", pp_thm(DIAG_TERM))
    print("DIAGONAL_TERM_EXISTS     :", pp_thm(DIAGONAL_TERM_EXISTS))
    print("HALTING_UNDECIDABLE      :", pp_thm(HALTING_UNDECIDABLE))
    print("HALTS_NOT_SK_REPRESENTABLE:", pp_thm(HALTS_NOT_SK_REPRESENTABLE))


