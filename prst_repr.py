# ---------------------------------------------------------------------------
# Stage 3 (PRST) -- representability is (almost) free.
# ---------------------------------------------------------------------------
#
# In HF, "representability of a PR predicate P : nat0 -> bool" means
# exhibiting an HF-formula F(x) and proving
#
#     |- !n. P n      ==> Prov_HF (substitute F (numeral n) var_x).
#     |- !n. ~ P n    ==> Prov_HF (Not_f (substitute F (numeral n) var_x)).
#
# The witnessing F(x) was always a Sigma_1 trace-existence formula, and
# the proofs required machinery to evaluate the trace inside HF (~3000
# lines for substitute alone).
#
# In PRST, every PR predicate P : nat0 -> bool that is decidable comes
# with a PR function symbol p_sym whose application returns a boolean
# value (encoded as Empty_pt for false, Insert_pt Empty_pt Empty_pt for
# true). The representing formula is:
#
#     F_P(x) := Eq_pf (App_pt p_sym (cons_l x nil_l)) (encoded_true).
#
# The representability theorem reduces to a single defining-equation
# lookup plus equality reasoning:
#
#     |- !n. P n   ==> Prov_PRST (substitute_p F_P (numeral n) var_x).
#
# Proof: substitute_p computes F_P(numeral n) = Eq_pf (App_pt p_sym
# (cons_l (numeral n) nil_l)) encoded_true. The defining equation of
# p_sym (an axiom) gives App_pt p_sym (cons_l (numeral n) nil_l) =
# encoded_true (when P n holds at the meta level). Equality and modus
# ponens close the goal.
#
# This is what the move BUYS us: a 3000-line trace argument collapses
# to ~5 lines.
# ---------------------------------------------------------------------------


from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from prst_syntax import (
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    App_pt,
    Empty_pt,  # noqa: F401  -- "encoded false" sentinel
    Insert_pt,  # noqa: F401  -- "encoded true" sentinel = Insert Empty Empty
    substitute_p,  # noqa: F401  -- parser alias
)
from prst_pr import (
    substitute_pr,
    numeral_pr,
    diag_pr,
    Proof_HF_pr,
    is_pr_sym,  # noqa: F401
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
)


# ---------------------------------------------------------------------------
# Stage 3 (a) -- the boolean encoding.
#
#   T_pt := Insert_pt Empty_pt Empty_pt   ("encoded true")
#   F_pt := Empty_pt                       ("encoded false")
#
# Distinct nat0 by Pair_ord encoding -- T_pt has tag 9, F_pt is 0.
# ---------------------------------------------------------------------------


T_PT_DEF = define("T_pt", parse_type("nat0"), "Insert_pt Empty_pt Empty_pt")
T_pt = mk_const("T_pt", [])


F_PT_DEF = define("F_pt", parse_type("nat0"), "Empty_pt")
F_pt = mk_const("F_pt", [])


@proof
def T_PT_NEQ_F_PT(p):
    """|- ~(T_pt = F_pt). STUB (tag disjointness through Pair_ord)."""
    p.goal("~(T_pt = F_pt)")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3 (b) -- representability of an arbitrary PR predicate.
#
# Given any HOL predicate P : nat0 -> bool *that is realised by a PR
# function symbol p_sym* (meaning: HOL proves P n = Prov_PRST (Eq_pf
# (App_pt p_sym (cons_l n nil_l)) T_pt)), the predicate is represented
# by F_P(x) := Eq_pf (App_pt p_sym (cons_l x nil_l)) T_pt.
#
# We expose a *parametric* theorem schema: the user supplies p_sym
# (a closed PR symbol) and the realisation hypothesis, and gets the
# representability conclusion.
# ---------------------------------------------------------------------------


# represents_pred_prst p_sym P  iff for every n, P n is reflected by p_sym at n.
represents_pred_prst_def = define(
    "represents_pred_prst",
    parse_type("nat0 -> (nat0 -> bool) -> bool"),
    "\\p_sym:nat0. \\P:nat0->bool. "
    "!n:nat0. (P n = Prov_PRST (Eq_pf (App_pt p_sym (cons_l n nil_l)) T_pt)) "
    "      /\\ (~P n = Prov_PRST (Eq_pf (App_pt p_sym (cons_l n nil_l)) F_pt))",
)
represents_pred_prst = mk_const("represents_pred_prst", [])


@proof
def REPRESENTABILITY_POSITIVE(p):
    """|- !p_sym P n.
            represents_pred_prst p_sym P /\\ P n
            ==> Prov_PRST (substitute_p
                            (Eq_pf (App_pt p_sym (cons_l var_x nil_l)) T_pt)
                            (numeral n)
                            var_x).

    Proof (~5 lines once filled in):
      * Unfold substitute_p via SUBSTITUTE_P_AT_APP / _AT_VAR_HIT to
        reduce to Eq_pf (App_pt p_sym (cons_l (numeral n) nil_l)) T_pt.
      * From represents_pred_prst's positive branch + P n, this is exactly
        what Prov_PRST entails.

    STUB.
    """
    p.goal(
        "!p_sym P n. (represents_pred_prst p_sym P /\\ P n) ==> "
        "Prov_PRST (substitute_p "
        "  (Eq_pf (App_pt p_sym (cons_l var_x nil_l)) T_pt) "
        "  (numeral n) var_x)",
        types={"p_sym": nat0_ty, "P": parse_type("nat0 -> bool"), "n": nat0_ty},
    )
    p.sorry()


@proof
def REPRESENTABILITY_NEGATIVE(p):
    """|- !p_sym P n.
            represents_pred_prst p_sym P /\\ ~P n
            ==> Prov_PRST (Not_pf
                  (substitute_p
                    (Eq_pf (App_pt p_sym (cons_l var_x nil_l)) T_pt)
                    (numeral n)
                    var_x)).

    Proof: similar to POSITIVE but uses F_pt branch + T_PT_NEQ_F_PT
    plus PRST equality reasoning. STUB.
    """
    p.goal(
        "!p_sym P n. (represents_pred_prst p_sym P /\\ ~P n) ==> "
        "Prov_PRST (Not_pf (substitute_p "
        "  (Eq_pf (App_pt p_sym (cons_l var_x nil_l)) T_pt) "
        "  (numeral n) var_x))",
        types={"p_sym": nat0_ty, "P": parse_type("nat0 -> bool"), "n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3 (c) -- the four headline representations.
#
# Each of substitute, numeral, diag, Proof_HF gets its representability
# theorem as an instance of REPRESENTABILITY_POSITIVE / _NEGATIVE
# applied to the corresponding PR symbol and the realisation lemma
# (PROV_PRST_SUBSTITUTE_EVAL / PROV_PRST_NUMERAL_EVAL / ...).
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_REPRESENTS_PRST(p):
    """|- !F t v. Prov_PRST (Eq_pf (App_pt substitute_pr
                                     (cons_l (numeral F)
                                       (cons_l (numeral t)
                                         (cons_l (numeral v) nil_l))))
                                   (numeral (substitute F t v))).

    The PRST analog of SUBSTITUTE_REPRESENTS (~3000 lines in HF). Here
    it's one PROV_PRST_SUBSTITUTE_EVAL specialisation plus
    PROV_PRST_NUMERAL_EVAL on each argument, chained by PRST equality.
    STUB. Estimate: ~30 lines.
    """
    p.goal(
        "!F t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (cons_l (numeral F) (cons_l (numeral t) (cons_l (numeral v) nil_l)))) "
        "  (numeral (substitute F t v)))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def DIAG_REPRESENTS_PRST(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (cons_l (numeral n) nil_l))
                                (numeral (diag n))).

    The PRST analog of DIAG_REPRESENTS (axiom in godel_first.py, ~80
    lines once fully discharged). Here: PROV_PRST_DIAG_EVAL +
    PROV_PRST_NUMERAL_EVAL. STUB. Estimate: ~10 lines.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf "
        "      (App_pt diag_pr (cons_l (numeral n) nil_l)) "
        "      (numeral (diag n)))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_HF_REPRESENTS_PRST_POS(p):
    """|- !p n. Proof_HF p n ==>
              Prov_PRST (Eq_pf
                (App_pt Proof_HF_pr (cons_l (numeral p) (cons_l (numeral n) nil_l)))
                T_pt).

    Positive branch of representability of the (decidable) Proof_HF
    predicate. STUB.

    PRST analog of the IS_*_REPRESENTS chain (~2000 lines in HF via
    traces). Here: one PROOF_HF_PR_DEFINING specialisation per branch.
    Estimate: ~20 lines for both branches combined.
    """
    p.goal(
        "!pf n. Proof_HF pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_HF_pr (cons_l (numeral pf) (cons_l (numeral n) nil_l))) "
        "  T_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_HF_REPRESENTS_PRST_NEG(p):
    """|- !p n. ~Proof_HF p n ==>
              Prov_PRST (Eq_pf
                (App_pt Proof_HF_pr (cons_l (numeral p) (cons_l (numeral n) nil_l)))
                F_pt). STUB."""
    p.goal(
        "!pf n. ~Proof_HF pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_HF_pr (cons_l (numeral pf) (cons_l (numeral n) nil_l))) "
        "  F_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Module size estimate
# ---------------------------------------------------------------------------
#
# Filled in: ~150 lines.
#
# Comparison to the HF representability chain:
#   hf_repr_core.py + hf_repr_thms.py = ~7900 lines.
#   prst_pr.py (~600) + prst_proof.py (~400) + prst_repr.py (~150)
#                                              = ~1150 lines total.
#
# Net saving: ~6750 lines, just from making PR symbols first-class
# terms instead of represented relations.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3 (PRST) -- representability is (almost) free.")
    print("    T_PT_DEF                       :", pp_thm(T_PT_DEF))
    print("    F_PT_DEF                       :", pp_thm(F_PT_DEF))
    print("    T_PT_NEQ_F_PT                  :", pp_thm(T_PT_NEQ_F_PT))
    print()
    print("    REPRESENTABILITY_POSITIVE      :", pp_thm(REPRESENTABILITY_POSITIVE))
    print("    REPRESENTABILITY_NEGATIVE      :", pp_thm(REPRESENTABILITY_NEGATIVE))
    print()
    print("    SUBSTITUTE_REPRESENTS_PRST     :", pp_thm(SUBSTITUTE_REPRESENTS_PRST))
    print("    DIAG_REPRESENTS_PRST           :", pp_thm(DIAG_REPRESENTS_PRST))
    print("    PROOF_HF_REPRESENTS_PRST_POS   :", pp_thm(PROOF_HF_REPRESENTS_PRST_POS))
    print("    PROOF_HF_REPRESENTS_PRST_NEG   :", pp_thm(PROOF_HF_REPRESENTS_PRST_NEG))
