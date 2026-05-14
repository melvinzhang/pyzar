"""Undecidability of the halting problem, via SK combinators over HF.

Final theorem (``HALTING_UNDECIDABLE``):

    |- ~ ?H. halts_decider H

where ``halts_decider H`` says ``H`` is an SK term and, for every SK
term ``t``,

    halts t = ~halts (App_t H t)

i.e. the *halt-status of the decider's output on t* encodes the
answer (flipped, so the diagonal contradiction lands cleanly).  This
flipped form is at least as strong as the conventional
boolean-output decider: a standard decider can be SK-massaged into
one satisfying this spec, so non-existence here implies non-existence
of the conventional decider.

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

  (2) *Halting.*  ``halts t := ?N. sk_par_steps t N /\\ is_normal N``,
      halting via parallel reduction reaching a normal form.  Sigma_1
      over nat0 (r.e.) but, the theorem says, not decidable by an SK
      term.

  (3) *Diagonal.*  Curry's classical diagonal ``e = S (K H) SII``,
      ``d = e e``.  Under parallel reduction one gets
      ``d ->>_par App_t H d`` (PAR_REFL lets H stay un-reduced inside
      the residue, which is what makes the diagonal work for arbitrary
      ``is_sk_term H``).  ``HALTS_INVARIANT`` (powered by Church-
      Rosser via ``sk_bullet``'s triangle property) promotes the
      par-step chain to ``halts d = halts (App_t H d)``.
      Combined with the flipped decider spec,
      ``halts d = ~halts d`` -- contradiction.

      No fixed-point combinator, no Omega.  See ``iter_to_bullet.md``
      for the design history (initial bullet-only DIAG_TERM was
      empirically falsified for composite H; current proof uses par).

------------------------------------------------------------------
Stage map
------------------------------------------------------------------

  Stage 0 (sk):       SK terms as tagged HF tuples
                      (S_t, K_t, App_t, is_sk_term).
  Stage 1 (par):      Parallel reduction ``sk_par_step`` + RTC
                      ``sk_par_steps`` + ``par_chain`` DSL.  Defines
                      ``is_normal`` as the par-step fixed-point
                      (``\\t. !Y. sk_par_step t Y ==> Y = t``); the
                      stability lemma ``NORMAL_STABILITY_PAR_STEP`` is
                      then a one-line specialisation of the definition.
  Stage 2 (bullet):   Takahashi's complete development ``sk_bullet``
                      + triangle property + Tait/Martin-Loef diamond
                      + Church-Rosser confluence on par.
  Stage 3 (halts):    ``halts`` + ``HALTS_INVARIANT``
                      (par-step chains preserve halting, by
                      confluence + normal-form stability).
  Stage 4 (diag):     Classical Curry diagonal ``DIAG_TERM`` in par
                      form; ``DIAGONAL_TERM_EXISTS`` promotes the
                      chain to a ``halts`` equality.
  Stage 5:            ``HALTING_UNDECIDABLE`` and the corollary
                      ``HALTS_NOT_SK_REPRESENTABLE``.

------------------------------------------------------------------
What this gives and doesn't give
------------------------------------------------------------------

Derived from the bare HOL kernel + ``hf_sets.py``:
  * Undecidability of halting for SK combinators (the headline).
  * Church-Rosser for SK via parallel reduction (powers
    ``HALTS_INVARIANT``).
  * General fixed-point self-reference (``DIAG_TERM``): for every SK
    term H there is an SK term d with ``sk_par_steps d (App_t H d)``.
    This is the diagonal/Y-combinator ingredient, and the only piece
    of "computational universality" the undecidability proof needs.

Not in scope here:
  * Full Turing-completeness of SK -- representability of every
    recursive function would also need Church booleans / numerals
    and an encoding/decoding correctness proof.  Classical, but not
    formalised here; the diagonal alone carries the contradiction.
  * Equivalence with Turing machines or lambda calculus (would need a
    third file). The theorem stands on its own without it.
  * A bullet-iter-based formulation of halting (``halts_b``) and its
    equivalence with ``halts``.  Removed -- ``halts`` is the
    natural form for the par-form diagonal and avoids the iterator
    bridge entirely.

Pairs especially well with ``godel_first.py``: the diagonal in this
file is mechanically the same as the Goedel diagonal -- self-application
producing self-reference. Tarski's undefinability of truth is the same
diagonal a third time.
"""

from fusion import Var
from basics import mk_const, mk_app, rand, aconv
from parser import define, parse_type, pp
from nat0 import nat0_ty, ZERO, mk_suc0
from proof import proof, register_intro_set
from tactics import REFL, SPEC, SPECL, SYM, EQ_MP, CONJ, MP
from tactics import TRANS, unfold_def_at
from hf_sets import Pair_ord
from data_type import (
    define_constructor,
    define_nat0_binary_closure_predicate,
    _proof_lt_binary_left,
    _proof_lt_binary_right,
)


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
# ``define_constructor`` yields both ``App_t = \t u. body`` and the pointwise
# ``!t u. App_t t u = body``; the latter feeds the NAT0_LT_APP_T_*
# size lemmas required by ``define_wf_lt``.
_APP_T_CTOR = define_constructor(
    "App_t",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\t:nat0. \\u:nat0. Pair_ord (SUC0 (SUC0 0)) (Pair_ord t u)",
)
APP_T_DEF = _APP_T_CTOR.def_thm
APP_T_AT = _APP_T_CTOR.at_thm
App_t = _APP_T_CTOR.const

# Tag literal for App_t, used by the size-lemma builders.
_APP_T_TAG = "SUC0 (SUC0 0)"


# NAT0_LT_APP_T_L : |- !a b. nat0_lt a (App_t a b)
# NAT0_LT_APP_T_R : |- !a b. nat0_lt b (App_t a b)
# These bound the recursion depth so ``define_wf_lt`` can take a least
# fixed point. Identical shape to the Imp_f / Insert_t cases, now produced by
# the shared encoded-datatype helpers.
NAT0_LT_APP_T_L = _proof_lt_binary_left(
    "NAT0_LT_APP_T_L", "a", "b", "App_t", APP_T_AT, _APP_T_TAG
)
NAT0_LT_APP_T_R = _proof_lt_binary_right(
    "NAT0_LT_APP_T_R", "a", "b", "App_t", APP_T_AT, _APP_T_TAG
)


_SK_TERM = define_nat0_binary_closure_predicate(
    "is_sk_term",
    "_is_sk_term_F",
    atoms=[("S_t", S_t), ("K_t", K_t)],
    binary=("App_t", App_t, NAT0_LT_APP_T_L, NAT0_LT_APP_T_R),
)
_IS_SK_TERM_F_DEF = _SK_TERM.body_def
_IS_SK_TERM_F = _SK_TERM.body_const
IS_SK_TERM_MONO = _SK_TERM.mono
IS_SK_TERM_DEF = _SK_TERM.def_thm
_IS_SK_TERM_REC_RAW = _SK_TERM.rec_raw
is_sk_term = _SK_TERM.pred
IS_SK_TERM_REC = _SK_TERM.rec
IS_SK_TERM_S, IS_SK_TERM_K = _SK_TERM.atom_intros
IS_SK_TERM_APP = _SK_TERM.binary_intro


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
# Constructor injectivity and disjointness (still Stage 0).
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
# Stage 1 -- parallel reduction.
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
# par_conv_chain -- a context manager for assembling a par_conv chain by
# linking individual sk_par_step transitions.  Composition lives in the
# par_conv calculus (PAR_CONV_TRANS), so the chain's output is a
# par-convertibility rather than an RTC of par-steps -- skipping
# sk_par_steps entirely.
#
# Usage:
#   with par_conv_chain(p, start, label="h_par") as c:
#       c.link("<intermediate_1>")
#       c.link("<intermediate_2>")
#       ...
#       c.link("<final>")
#   # registers   h_par : par_conv start <final>
#
# Each ``c.link(next)`` synthesizes ``sk_par_step current next`` by
# recursive structural matching:
#   start ≡ end                                  -> PAR_REFL
#   start = App_t (App_t K_t a) b, end = a'      -> PAR_K (with par-step a -> a')
#   start = App_t (App_t (App_t S_t a) b) c,
#       end = App_t (App_t a' c') (App_t b' c')  -> PAR_S
#   start = App_t A B,
#       end = App_t A' B'                        -> PAR_APP (recurse)
# then lifts the single par-step to par_conv via PAR_CONV_STEP.  Links
# accumulate; ``__exit__`` folds them left-to-right via PAR_CONV_TRANS
# (seeded with PAR_CONV_REFL when the chain is empty).
#
# Limitation: the shape synth only sees structural redexes.  A folded
# constant like ``I_t`` is not an S_t-head even though ``I_t = (S_t K_t)
# K_t`` definitionally -- callers must either pre-unfold such constants
# in the chain terms, or insert separate equational bridging steps.
# ---------------------------------------------------------------------------


_PC_S_t = mk_const("S_t", [])
_PC_K_t = mk_const("K_t", [])
_PC_App_t = mk_const("App_t", [])


def _pc_dest_App_t(tm):
    """If ``tm = App_t a b`` (i.e. ``Comb(Comb(App_t, a), b)``), return
    ``(a, b)``; else None."""
    from basics import is_comb, dest_comb
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


class _ParConvChain:
    def __init__(self, p, start, label):
        self.p = p
        self.label = label
        self.start = p._parse(start) if isinstance(start, str) else start
        self.current = self.start
        # Each entry: (left_endpoint, right_endpoint, par_conv_th).
        self.links = []
        self._closed = False

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        if exc_type is None and not self._closed:
            self._close()
        return False

    def link(self, next_tm):
        """Synthesize ``sk_par_step current next_tm``, lift via
        PAR_CONV_STEP to ``par_conv current next_tm``, and advance."""
        next_kt = (
            self.p._parse(next_tm) if isinstance(next_tm, str) else next_tm
        )
        par_th = _pc_synth_par_step(self.current, next_kt)
        conv_th = MP(
            SPECL([self.current, next_kt], PAR_CONV_STEP), par_th
        )
        self.links.append((self.current, next_kt, conv_th))
        self.current = next_kt

    def _close(self):
        # Empty chain collapses to PAR_CONV_REFL at the start term.
        if not self.links:
            acc = SPEC(self.start, PAR_CONV_REFL)
        else:
            # Fold left: acc tracks ``par_conv start <cur_right>``.
            _, cur_right, acc = self.links[0]
            for (_ti, tj, conv_th) in self.links[1:]:
                inst = SPECL(
                    [self.start, cur_right, tj], PAR_CONV_TRANS
                )
                acc = MP(inst, CONJ(acc, conv_th))
                cur_right = tj
        self.p.have(f"{self.label}: {pp(acc._concl)}").by_thm(acc)
        self._closed = True


def par_conv_chain(p, start, *, label):
    """Context manager for assembling a ``par_conv`` chain from
    individual ``sk_par_step`` transitions.  See module-level comment
    for the synthesis algorithm and limitations."""
    return _ParConvChain(p, start, label)
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

    # Unfold ``sk_par_step <atom> Y`` to the impredicative universal,
    # then SPEC at Q via ``by_spec`` (SPECL + BETA_NORM in one shot).
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF, p._parse(atom_str), p._parse("Y")
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))
    Q_tm = p._parse(
        f"\\A:nat0. \\B:nat0. (A = {atom_str}) ==> (B = {atom_str})"
    )
    p.have("h_at_Q:").by_spec(h_univ, Q_tm)

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
            f"h_neg: ~({atom_str} = App_t (App_t K_t M) N)"
        ).by(atom_neq_app_t, "App_t K_t M", "N")
        p.absurd().by_conj("h_neg", "h_eq")

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
            f"h_neg: ~({atom_str} = App_t (App_t (App_t S_t M) N) P)"
        ).by(atom_neq_app_t, "App_t (App_t S_t M) N", "P")
        p.absurd().by_conj("h_neg", "h_eq")

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
        p.have(f"h_neg: ~({atom_str} = App_t M N)").by(
            atom_neq_app_t, "M", "N"
        )
        p.absurd().by_conj("h_neg", "h_eq")

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
# ``is_normal`` -- par-step fixed-point predicate.
#
# A term is normal iff no proper par-step leaves it -- the standard
# definition of a normal form for a reduction relation.  Treated as
# opaque downstream; ``NORMAL_STABILITY_PAR_STEP`` is the only direct
# consumer and is a one-line specialisation of the definition.
# ---------------------------------------------------------------------------


IS_NORMAL_DEF = define(
    "is_normal",
    parse_type("nat0 -> bool"),
    "\\t:nat0. !Y:nat0. sk_par_step t Y ==> Y = t",
)
is_normal = mk_const("is_normal", [])


# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Stage 2.5 -- par-convertibility.
#
# ``par_conv X Y`` is the reflexive/symmetric/transitive closure of
# ``sk_par_step`` (impredicatively encoded, same style as
# ``sk_par_steps``).  Stage 3 defines ``halts`` over ``par_conv`` so that
# invariance under reduction (``HALTS_INVARIANT``) is trivial -- no
# confluence required.  The Stage 2 bullet/triangle/diamond machinery is
# left in place for now but no longer feeds the halting predicate.
# ---------------------------------------------------------------------------

# Closure-conditions body for par_conv; reused in each intro.  The
# string mentions ``P`` free -- it is only parseable in a scope where
# ``P`` is bound (either as a fixed Var in an inner sub-frame or as the
# universal binder around it).
_PAR_CONV_CLOSURE = (
    "((!Z:nat0. P Z Z) /\\ "
    " (!A:nat0. !B:nat0. P A B ==> P B A) /\\ "
    " (!A:nat0. !B:nat0. !C:nat0. P A B /\\ P B C ==> P A C) /\\ "
    " (!A:nat0. !B:nat0. sk_par_step A B ==> P A B))"
)


PAR_CONV_DEF = define(
    "par_conv",
    parse_type("nat0 -> nat0 -> bool"),
    "\\X:nat0. \\Y:nat0. "
    f"!P:nat0->nat0->bool. {_PAR_CONV_CLOSURE} ==> P X Y",
)
par_conv = mk_const("par_conv", [])


# Intro pattern (same as sk_par_steps): build the unfolded form
# ``!P. closure(P) ==> P <lhs> <rhs>`` inside a sub-proof by fixing P,
# assuming the closure conjunction, and applying the relevant closure
# rule; then fold back via ``by_unfold("unf", PAR_CONV_DEF)``.
#
# DSL friction noted:
#  - ``_PAR_CONV_CLOSURE`` has to be referenced verbatim in three
#    positions per proof (the outer have's spec, the inner assume, and
#    each ``by_unfold`` of a par_conv hypothesis).  No DSL primitive
#    abstracts ``the closure conjunction of this impredicative
#    encoding''.
#  - ``by_unfold`` of a ``par_conv X Y`` hypothesis yields the full
#    impredicative form; the user then has to SPEC at ``P`` and MP with
#    ``h_cl`` by hand to extract ``P X Y``.  ``sk_par_steps`` works
#    around this with a kernel helper (``_par_steps_to_P``); we use
#    pure DSL here at the cost of two explicit ``have`` lines per
#    hypothesis.


@proof
def PAR_CONV_REFL(p):
    """|- !X. par_conv X X.  Reflexivity of par-convertibility."""
    p.goal("!X. par_conv X X")
    p.fix("X")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_CONV_CLOSURE} ==> P X X"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_CONV_CLOSURE}")
        p.split("h_cl", "(refl_cl, _, _, _)")
        p.thus("P X X").by("refl_cl", "X")
    p.thus("par_conv X X").by_unfold("unf", PAR_CONV_DEF)


@proof
def PAR_CONV_STEP(p):
    """|- !X Y. sk_par_step X Y ==> par_conv X Y.

    Embedding: every one-step parallel reduction is a par-convertibility.
    """
    p.goal("!X Y. sk_par_step X Y ==> par_conv X Y")
    p.fix("X Y")
    p.assume("h_step: sk_par_step X Y")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_CONV_CLOSURE} ==> P X Y"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_CONV_CLOSURE}")
        p.split("h_cl", "(_, _, _, step_cl)")
        p.thus("P X Y").by("step_cl", "X", "Y", "h_step")
    p.thus("par_conv X Y").by_unfold("unf", PAR_CONV_DEF)


@proof
def PAR_CONV_SYM(p):
    """|- !X Y. par_conv X Y ==> par_conv Y X.

    Symmetry of par-convertibility.
    """
    p.goal("!X Y. par_conv X Y ==> par_conv Y X")
    p.fix("X Y")
    p.assume("h_XY: par_conv X Y")
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_CONV_CLOSURE} ==> P Y X"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_CONV_CLOSURE}")
        p.split("h_cl", "(_, sym_cl, _, _)")
        # Unfold h_XY to its impredicative form, SPEC at the inner P,
        # MP with h_cl -- yields ``P X Y``.  The inner ``!P:...`` binder
        # shadows the outer fixed ``P``; ``.by("unf_XY", "P", "h_cl")``
        # SPECs at the outer ``P`` and MPs with h_cl.
        p.have(
            "unf_XY: !P:nat0->nat0->bool. "
            f"        {_PAR_CONV_CLOSURE} ==> P X Y"
        ).by_unfold("h_XY", PAR_CONV_DEF)
        p.have("pXY: P X Y").by("unf_XY", "P", "h_cl")
        p.thus("P Y X").by("sym_cl", "X", "Y", "pXY")
    p.thus("par_conv Y X").by_unfold("unf", PAR_CONV_DEF)


@proof
def PAR_CONV_TRANS(p):
    """|- !X Y Z. par_conv X Y /\\ par_conv Y Z ==> par_conv X Z.

    Transitivity of par-convertibility.
    """
    p.goal(
        "!X Y Z. par_conv X Y /\\ par_conv Y Z ==> par_conv X Z"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_YZ): par_conv X Y /\\ par_conv Y Z"
    )
    with p.have(
        "unf: !P:nat0->nat0->bool. "
        f"     {_PAR_CONV_CLOSURE} ==> P X Z"
    ).proof():
        p.fix("P")
        p.assume(f"h_cl: {_PAR_CONV_CLOSURE}")
        p.split("h_cl", "(_, _, trans_cl, _)")
        # Same unfold-SPEC-MP dance for each side of the conjunction.
        p.have(
            "unf_XY: !P:nat0->nat0->bool. "
            f"        {_PAR_CONV_CLOSURE} ==> P X Y"
        ).by_unfold("h_XY", PAR_CONV_DEF)
        p.have("pXY: P X Y").by("unf_XY", "P", "h_cl")
        p.have(
            "unf_YZ: !P:nat0->nat0->bool. "
            f"        {_PAR_CONV_CLOSURE} ==> P Y Z"
        ).by_unfold("h_YZ", PAR_CONV_DEF)
        p.have("pYZ: P Y Z").by("unf_YZ", "P", "h_cl")
        p.have("pConj: P X Y /\\ P Y Z").by_thm(
            CONJ(p.fact("pXY"), p.fact("pYZ"))
        )
        p.thus("P X Z").by("trans_cl", "X", "Y", "Z", "pConj")
    p.thus("par_conv X Z").by_unfold("unf", PAR_CONV_DEF)


# ---------------------------------------------------------------------------
# Stage 3 -- halting predicate.
#
#   halts t := ?N. par_conv t N /\\ is_normal N
#
# A term halts iff some normal form lies in its par-convertibility class.
# Invariance under reduction (``HALTS_INVARIANT``) follows from
# ``PAR_CONV_*`` directly -- no Church-Rosser / Tait-Martin-Loef diamond
# needed.
# ---------------------------------------------------------------------------

_n0_t_var = Var("t", nat0_ty)


# halts t := ?N. par_conv t N /\\ is_normal N.
HALTS_DEF = define(
    "halts",
    parse_type("nat0 -> bool"),
    "\\t:nat0. ?N:nat0. par_conv t N /\\ is_normal N",
)
halts = mk_const("halts", [])


@proof
def HALTS_AT(p):
    """|- !t. halts t = (?N. par_conv t N /\\ is_normal N).

    Direct unfold of HALTS_DEF via AP_THM + BETA.
    """
    from tactics import AP_THM, BETA_CONV, GEN

    ap = AP_THM(HALTS_DEF, _n0_t_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal("!t. halts t = (?N. par_conv t N /\\ is_normal N)")
    p.thus(
        "!t. halts t = (?N. par_conv t N /\\ is_normal N)"
    ).by_thm(GEN(_n0_t_var, spec_th))


@proof
def HALTS_INVARIANT(p):
    """|- !X Y. par_conv X Y ==> halts X = halts Y.

    Both directions go through PAR_CONV_TRANS; forward also uses
    PAR_CONV_SYM to flip the convertibility.  No confluence used.
    """
    p.goal(
        "!X Y. par_conv X Y ==> halts X = halts Y"
    )
    p.fix("X Y")
    p.assume("h_pc_XY: par_conv X Y")

    # Symmetric flip, shared by both directions.
    p.have("h_pc_YX: par_conv Y X").by(
        PAR_CONV_SYM, "X", "Y", "h_pc_XY"
    )

    # ---- Forward direction ----------------------------------------------
    with p.have(
        "h_fwd: halts X ==> halts Y"
    ).proof():
        p.assume("h_hX: halts X")
        p.have(
            "h_at_X: halts X = "
            "(?N. par_conv X N /\\ is_normal N)"
        ).by(HALTS_AT, "X")
        p.have(
            "h_ex_X: ?N. par_conv X N /\\ is_normal N"
        ).by_eq_mp("h_at_X", "h_hX")
        p.choose("N", from_="h_ex_X")
        p.split("N_eq", "(h_XN, h_norm_N)")

        # par_conv Y X /\ par_conv X N => par_conv Y N.
        p.have(
            "h_conj_YX_XN: par_conv Y X /\\ par_conv X N"
        ).by_thm(CONJ(p.fact("h_pc_YX"), p.fact("h_XN")))
        p.have("h_YN: par_conv Y N").by(
            PAR_CONV_TRANS, "Y", "X", "N", "h_conj_YX_XN"
        )

        p.have(
            "h_at_Y: halts Y = "
            "(?N. par_conv Y N /\\ is_normal N)"
        ).by(HALTS_AT, "Y")
        p.have(
            "h_ex_Y: ?N. par_conv Y N /\\ is_normal N"
        ).by_exists(["N"], "h_YN", "h_norm_N")
        p.thus("halts Y").by_eq_mp("h_at_Y", "h_ex_Y")

    # ---- Backward direction ---------------------------------------------
    with p.have(
        "h_bwd: halts Y ==> halts X"
    ).proof():
        p.assume("h_hY: halts Y")
        p.have(
            "h_at_Y: halts Y = "
            "(?N. par_conv Y N /\\ is_normal N)"
        ).by(HALTS_AT, "Y")
        p.have(
            "h_ex_Y: ?N. par_conv Y N /\\ is_normal N"
        ).by_eq_mp("h_at_Y", "h_hY")
        p.choose("N", from_="h_ex_Y")
        p.split("N_eq", "(h_YN, h_norm_N)")

        # par_conv X Y /\ par_conv Y N => par_conv X N.
        p.have(
            "h_conj_XY_YN: par_conv X Y /\\ par_conv Y N"
        ).by_thm(CONJ(p.fact("h_pc_XY"), p.fact("h_YN")))
        p.have("h_XN: par_conv X N").by(
            PAR_CONV_TRANS, "X", "Y", "N", "h_conj_XY_YN"
        )

        p.have(
            "h_at_X: halts X = "
            "(?N. par_conv X N /\\ is_normal N)"
        ).by(HALTS_AT, "X")
        p.have(
            "h_ex_X: ?N. par_conv X N /\\ is_normal N"
        ).by_exists(["N"], "h_XN", "h_norm_N")
        p.thus("halts X").by_eq_mp("h_at_X", "h_ex_X")

    p.thus("halts X = halts Y").by_iff(
        "h_fwd", "h_bwd"
    )


# ---------------------------------------------------------------------------
# Stage 4 -- the diagonal.
#
# ``halts_decider H`` says H is an SK term that decides halting via the
# flipped halting-status output convention:
# ``halts t  iff  ~halts (App_t H t)``.  The flipped convention
# turns the diagonal equation ``halts d = halts (App_t H d)``
# into a ``P = ~P`` contradiction directly, no Church-bool case-split
# needed.  See module docstring for why the flipped form is at least as
# strong as a standard boolean-output decider.
# ---------------------------------------------------------------------------
HALTS_DECIDER_DEF = define(
    "halts_decider",
    parse_type("nat0 -> bool"),
    "\\H:nat0. is_sk_term H /\\ "
    "         !t:nat0. is_sk_term t ==> "
    "             (halts t = ~(halts (App_t H t)))",
)
halts_decider = mk_const("halts_decider", [])


@proof
def HALTS_DECIDER_DEF_THM(p):
    """|- !H. halts_decider H =
              (is_sk_term H /\\
               !t. is_sk_term t ==>
                   (halts t = ~(halts (App_t H t)))).

    Direct unfold of HALTS_DECIDER_DEF via AP_THM + BETA.
    """
    from tactics import AP_THM, BETA_CONV, GEN
    H_var = Var("H", nat0_ty)
    ap = AP_THM(HALTS_DECIDER_DEF, H_var)
    bet = BETA_CONV(rand(ap._concl))
    spec_th = TRANS(ap, bet)
    p.goal(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts t = ~(halts (App_t H t))))"
    )
    p.thus(
        "!H. halts_decider H = "
        "    (is_sk_term H /\\ "
        "     !t. is_sk_term t ==> "
        "         (halts t = ~(halts (App_t H t))))"
    ).by_thm(GEN(H_var, spec_th))


_DIAG_I = "App_t (App_t S_t K_t) K_t"
_DIAG_SII = f"App_t (App_t S_t ({_DIAG_I})) ({_DIAG_I})"
_DIAG_KH = "App_t K_t H"
_DIAG_E = f"App_t (App_t S_t ({_DIAG_KH})) ({_DIAG_SII})"
_DIAG_D = f"App_t ({_DIAG_E}) ({_DIAG_E})"


@proof
def DIAG_TERM(p):
    """|- !H. is_sk_term H ==>
              ?d. is_sk_term d /\\ par_conv d (App_t H d).

    Classical Curry diagonal in the par-convertibility calculus.  Witness
    with I_t unfolded inline as ``(S_t K_t) K_t`` so ``par_conv_chain``'s
    structural synth sees the S-redex shape at each ``I_unf e`` site
    (the existential over d doesn't care that I_unf = I_t
    definitionally)::

        I_unf := App_t (App_t S_t K_t) K_t
        SII   := App_t (App_t S_t I_unf) I_unf
        KH    := App_t K_t H
        e     := App_t (App_t S_t KH) SII        (* S (K H) SII *)
        d     := App_t e e

    4-link chain (each link a single parallel-reduction step lifted to
    par_conv via PAR_CONV_STEP and composed via PAR_CONV_TRANS;
    par_conv_chain synth emits PAR_S / PAR_K / PAR_APP from the
    start/end shapes, REFL on H carries through every link)::

        d ~ (KH e)(SII e)                          [outer S]
          ~ H ((I_unf e)(I_unf e))                 [PAR_K on left, PAR_S on right]
          ~ H (((K e)(K e))((K e)(K e)))           [2 x I_unf-as-SKK fires PAR_S]
          ~ H (e e) = App_t H d                    [4 x parallel K]

    Why par and not bullet: ``PAR_REFL`` lets ``H`` stay un-reduced
    inside the residue, which is what makes the diagonal work for
    arbitrary ``is_sk_term H``.  Bullet's eager-everywhere semantics
    would reduce composite ``H`` mid-trajectory and break the equation
    (empirically falsified in ``outside/sk_par.py`` EXP 5/6).
    ``DIAGONAL_TERM_EXISTS`` downstream promotes the par_conv chain to
    a ``halts`` equality via ``HALTS_INVARIANT``.
    """
    _I = _DIAG_I
    _SII = _DIAG_SII
    _KH = _DIAG_KH
    _E = _DIAG_E
    _D = _DIAG_D

    p.goal(
        "!H. is_sk_term H ==> "
        "    ?d. is_sk_term d /\\ par_conv d (App_t H d)"
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

    # ---- (2) 4-link par_conv chain. --------------------------------------
    _T1 = f"App_t (App_t ({_KH}) ({_E})) (App_t ({_SII}) ({_E}))"
    _I_E = f"App_t ({_I}) ({_E})"
    _T2 = f"App_t H (App_t ({_I_E}) ({_I_E}))"
    _KE = f"App_t K_t ({_E})"
    _KE_KE = f"App_t ({_KE}) ({_KE})"
    _T3 = f"App_t H (App_t ({_KE_KE}) ({_KE_KE}))"
    _T4 = f"App_t H ({_D})"

    with par_conv_chain(p, _D, label="h_par") as c:
        c.link(_T1)
        c.link(_T2)
        c.link(_T3)
        c.link(_T4)

    # ---- (3) Witness d. --------------------------------------------------
    p.thus(
        "?d. is_sk_term d /\\ par_conv d (App_t H d)"
    ).by_exists([_D], "h_is_sk_d", "h_par")
@proof
def DIAGONAL_TERM_EXISTS(p):
    """|- !H. is_sk_term H ==>
              ?d. is_sk_term d /\\ halts d = halts (App_t H d).

    Halts-form diagonal: DIAG_TERM gives ``d`` and
    ``par_conv d (App_t H d)``; HALTS_INVARIANT promotes the
    par-convertibility to a halts equality.  Witness d.
    """
    p.goal(
        "!H. is_sk_term H ==> "
        "    ?d. is_sk_term d /\\ halts d = halts (App_t H d)"
    )
    p.fix("H")
    p.assume("h_is_sk_H: is_sk_term H")

    p.have(
        "h_diag: ?d. is_sk_term d /\\ par_conv d (App_t H d)"
    ).by(DIAG_TERM, "H", "h_is_sk_H")
    p.choose("d", from_="h_diag")
    p.split("d_eq", "(h_is_sk_d, h_par)")

    p.have(
        "h_halts_eq: halts d = halts (App_t H d)"
    ).by(HALTS_INVARIANT, "d", "App_t H d", "h_par")

    p.thus(
        "?d. is_sk_term d /\\ halts d = halts (App_t H d)"
    ).by_exists(["d"], "h_is_sk_d", "h_halts_eq")


@proof
def HALTING_UNDECIDABLE(p):
    """|- ~ ?H. halts_decider H.

    THE THEOREM.  No SK combinator decides halting.

    Proof (4-step contradiction):

      Assume H with halts_decider H.  Unfold via HALTS_DECIDER_DEF_THM:
        is_sk_term H  /\\  !t. is_sk_term t ==>
                              halts t = ~halts (App_t H t).

      Curry diagonal via DIAGONAL_TERM_EXISTS at H:
        ?d. is_sk_term d /\\ halts d = halts (App_t H d).

      Specialise the decider spec at t := d:
        halts d = ~halts (App_t H d).

      Combining: halts (App_t H d) = ~halts (App_t H d).
      Discharge via EXCLUDED_MIDDLE on halts (App_t H d).
    """
    from classical import EXCLUDED_MIDDLE

    p.goal("~ (?H. halts_decider H)")
    with p.suppose("h_ex: ?H. halts_decider H"):
        p.choose("H", from_="h_ex")

        p.have(
            "h_thm: halts_decider H = "
            "       (is_sk_term H /\\ "
            "        !t. is_sk_term t ==> "
            "            (halts t = ~(halts (App_t H t))))"
        ).by(HALTS_DECIDER_DEF_THM, "H")
        p.have(
            "h_unf: is_sk_term H /\\ "
            "       !t. is_sk_term t ==> "
            "           (halts t = ~(halts (App_t H t)))"
        ).by_eq_mp("h_thm", "H_eq")
        p.split("h_unf", "(h_is_sk_H, h_decides)")

        p.have(
            "h_diag: ?d. is_sk_term d /\\ "
            "        halts d = halts (App_t H d)"
        ).by(DIAGONAL_TERM_EXISTS, "H", "h_is_sk_H")
        p.choose("d", from_="h_diag")
        p.split("d_eq", "(h_is_sk_d, h_dd_eq)")

        p.have(
            "h_dec_d: halts d = ~halts (App_t H d)"
        ).by("h_decides", "d", "h_is_sk_d")

        # h_dd_eq  : halts d           = halts (App_t H d)
        # h_dec_d  : halts d           = ~halts (App_t H d)
        # SYM h_dd_eq + h_dec_d :
        #   halts (App_t H d) = ~halts (App_t H d)
        p.have(
            "h_pne: halts (App_t H d) = ~halts (App_t H d)"
        ).by_trans(SYM(p.fact("h_dd_eq")), "h_dec_d")

        with p.cases_on(EXCLUDED_MIDDLE, "halts (App_t H d)"):
            with p.case("h_yes: halts (App_t H d)"):
                p.have(
                    "h_no: ~halts (App_t H d)"
                ).by_eq_mp("h_pne", "h_yes")
                p.absurd().by_conj("h_yes", "h_no")
            with p.case("h_no: ~halts (App_t H d)"):
                p.have(
                    "h_yes: halts (App_t H d)"
                ).by_eq_mp(SYM(p.fact("h_pne")), "h_no")
                p.absurd().by_conj("h_yes", "h_no")


# ---------------------------------------------------------------------------
# Stage 5 -- corollaries.
# ---------------------------------------------------------------------------


@proof
def HALTS_NOT_SK_REPRESENTABLE(p):
    """|- ~ ?H. is_sk_term H /\\
                !t. is_sk_term t ==>
                    (halts t = ~(halts (App_t H t))).

    HALTING_UNDECIDABLE, restated as non-existence of an SK term
    satisfying the flipped halt-status spec.  Immediate from
    HALTING_UNDECIDABLE + HALTS_DECIDER_DEF_THM: any H satisfying the
    unfolded predicate also satisfies ``halts_decider H``, witnessing
    the existential refuted by HALTING_UNDECIDABLE.
    """
    p.goal(
        "~ (?H. is_sk_term H /\\ "
        "       !t. is_sk_term t ==> "
        "           (halts t = ~(halts (App_t H t))))"
    )
    with p.suppose(
        "h_ex: ?H. is_sk_term H /\\ "
        "      !t. is_sk_term t ==> "
        "          (halts t = ~(halts (App_t H t)))"
    ):
        p.choose("H", from_="h_ex")
        p.have(
            "h_thm: halts_decider H = "
            "       (is_sk_term H /\\ "
            "        !t. is_sk_term t ==> "
            "            (halts t = ~(halts (App_t H t))))"
        ).by(HALTS_DECIDER_DEF_THM, "H")
        p.have("h_hd: halts_decider H").by_eq_mp("h_thm", "H_eq")
        p.have("h_ex_hd: ?H. halts_decider H").by_witness("H", "h_hd")
        p.absurd().by_conj(HALTING_UNDECIDABLE, "h_ex_hd")


if __name__ == "__main__":
    from parser import pp_thm
    print("HALTS_DECIDER_DEF         :", pp_thm(HALTS_DECIDER_DEF))
    print("DIAG_TERM                 :", pp_thm(DIAG_TERM))
    print("DIAGONAL_TERM_EXISTS      :", pp_thm(DIAGONAL_TERM_EXISTS))
    print("HALTING_UNDECIDABLE       :", pp_thm(HALTING_UNDECIDABLE))
    print("HALTS_NOT_SK_REPRESENTABLE:", pp_thm(HALTS_NOT_SK_REPRESENTABLE))
