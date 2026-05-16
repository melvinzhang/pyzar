# ---------------------------------------------------------------------------
# Stage 3 (PRST) -- representability is (almost) free.
# ---------------------------------------------------------------------------
#
# Representability of a PR predicate P : nat0 -> bool in PRST means
# exhibiting a PRST formula F(x) and proving
#
#     |- !n. P n      ==> Prov_PRST (substitute_p F (quote_hf n) var_x).
#     |- !n. ~ P n    ==> Prov_PRST (Not_pf (substitute_p F (quote_hf n) var_x)).
#
# Every decidable PR predicate P comes with a PR function symbol p_sym
# whose application returns a boolean value (encoded as Empty_pt for
# false, Adj_pt Empty_pt Empty_pt for true). The representing formula
# is:
#
#     F_P(x) := Eq_pf (App_pt p_sym (Tup_pt x Empty_pt)) (encoded_true).
#
# The representability theorem reduces to a single defining-equation
# lookup plus equality reasoning:
#
#     |- !n. P n   ==> Prov_PRST (substitute_p F_P (quote_hf n) var_x).
#
# Proof: substitute_p computes F_P(quote_hf n) = Eq_pf (App_pt p_sym
# (Tup_pt (quote_hf n) Empty_pt)) encoded_true. The defining equation of
# p_sym (an axiom) gives App_pt p_sym (Tup_pt (quote_hf n) Empty_pt) =
# encoded_true (when P n holds at the meta level). Equality and modus
# ponens close the goal.
#
# Making PR symbols first-class terms collapses representability to
# a defining-equation lookup -- no trace sets, no functionality proofs.
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
    substitute_p,  # noqa: F401  -- parser alias
)
from prst_pr import (
    substitute_pr,
    numeral_pr,
    diag_pr,
    Proof_PRST_pr,
    Adj_pt,  # noqa: F401  -- "encoded true" sentinel = Adj_pt Empty_pt Empty_pt
    T_pt,  # noqa: F401  -- parser alias
    F_pt,  # noqa: F401  -- parser alias
    is_pr_sym,  # noqa: F401
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
    Proof_PRST,  # noqa: F401  -- parser alias for PROOF_PRST_REPRESENTS_*
)
from hf_repr_core import quote_hf  # noqa: F401  -- parser alias


# T_pt / F_pt -- the boolean encoding -- live in prst_pr.py so they're
# shared with prst_proof (MU_CORRECTNESS uses T_pt). Re-exported here
# for the parser via the imports at the top of this module.


@proof
def T_PT_NEQ_F_PT(p):
    """|- ~(T_pt = F_pt)."""
    from tactics import TRANS
    from prst_pr import T_PT_DEF, F_PT_DEF, ADJ_PT_DEF
    from prst_syntax import APP_PT_NEQ_EMPTY_PT

    p.goal("~(T_pt = F_pt)")
    adj_at = p.unfold(ADJ_PT_DEF, "Empty_pt", "Empty_pt")
    t_at = TRANS(T_PT_DEF, adj_at)
    p.have(
        "h_app_neq: "
        "~(App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)) = Empty_pt)"
    ).by(
        APP_PT_NEQ_EMPTY_PT,
        "adj_sym",
        "Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)",
    )
    p.thus("~(T_pt = F_pt)").by_rewrite_of("h_app_neq", [t_at, F_PT_DEF])


# ---------------------------------------------------------------------------
# Stage 3 (b) -- representability of an arbitrary PR predicate.
#
# Given any HOL predicate P : nat0 -> bool *that is realised by a PR
# function symbol p_sym* (meaning: HOL proves P n = Prov_PRST (Eq_pf
# (App_pt p_sym (Tup_pt n Empty_pt)) T_pt)), the predicate is represented
# by F_P(x) := Eq_pf (App_pt p_sym (Tup_pt x Empty_pt)) T_pt.
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
    "!n:nat0. (P n = Prov_PRST (Eq_pf (App_pt p_sym (Tup_pt n Empty_pt)) T_pt)) "
    "      /\\ (~P n = Prov_PRST (Eq_pf (App_pt p_sym (Tup_pt n Empty_pt)) F_pt))",
)
represents_pred_prst = mk_const("represents_pred_prst", [])


@proof
def REPRESENTABILITY_POSITIVE(p):
    """|- !p_sym P n.
            represents_pred_prst p_sym P /\\ P n
            ==> Prov_PRST (substitute_p
                            (Eq_pf (App_pt p_sym (Tup_pt var_x Empty_pt)) T_pt)
                            (quote_hf n)
                            var_x).

    Proof (~5 lines once filled in):
      * Unfold substitute_p via SUBSTITUTE_P_AT_APP / _AT_VAR_HIT to
        reduce to Eq_pf (App_pt p_sym (Tup_pt (quote_hf n) Empty_pt)) T_pt.
      * From represents_pred_prst's positive branch + P n, this is exactly
        what Prov_PRST entails.

    STUB.
    """
    p.goal(
        "!p_sym P n. (represents_pred_prst p_sym P /\\ P n) ==> "
        "Prov_PRST (substitute_p "
        "  (Eq_pf (App_pt p_sym (Tup_pt var_x Empty_pt)) T_pt) "
        "  (quote_hf n) var_x)",
        types={"p_sym": nat0_ty, "P": parse_type("nat0 -> bool"), "n": nat0_ty},
    )
    p.sorry()


@proof
def REPRESENTABILITY_NEGATIVE(p):
    """|- !p_sym P n.
            represents_pred_prst p_sym P /\\ ~P n
            ==> Prov_PRST (Not_pf
                  (substitute_p
                    (Eq_pf (App_pt p_sym (Tup_pt var_x Empty_pt)) T_pt)
                    (quote_hf n)
                    var_x)).

    Proof: similar to POSITIVE but uses F_pt branch + T_PT_NEQ_F_PT
    plus PRST equality reasoning. STUB.
    """
    p.goal(
        "!p_sym P n. (represents_pred_prst p_sym P /\\ ~P n) ==> "
        "Prov_PRST (Not_pf (substitute_p "
        "  (Eq_pf (App_pt p_sym (Tup_pt var_x Empty_pt)) T_pt) "
        "  (quote_hf n) var_x))",
        types={"p_sym": nat0_ty, "P": parse_type("nat0 -> bool"), "n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 3 (c) -- the four headline representations.
#
# Each of substitute, quote_hf, diag, Proof_PRST gets its
# representability theorem as an instance of REPRESENTABILITY_POSITIVE
# / _NEGATIVE applied to the corresponding PR symbol and the realisation
# lemma (PROV_PRST_SUBSTITUTE_EVAL / PROV_PRST_NUMERAL_EVAL / ...).
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_REPRESENTS_PRST(p):
    """|- !F t v. Prov_PRST (Eq_pf (App_pt substitute_pr
                                     (Tup_pt (quote_hf F)
                                       (Tup_pt (quote_hf t)
                                         (Tup_pt (quote_hf v) Empty_pt))))
                                   (quote_hf (substitute F t v))).

    Representability of substitute as a PRST claim. One
    PROV_PRST_SUBSTITUTE_EVAL specialisation plus PROV_PRST_NUMERAL_EVAL
    on each argument, chained by PRST equality. STUB. Estimate: ~30
    lines.
    """
    p.goal(
        "!F t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (quote_hf F) (Tup_pt (quote_hf t) (Tup_pt (quote_hf v) Empty_pt)))) "
        "  (quote_hf (substitute F t v)))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def DIAG_REPRESENTS_PRST(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt (quote_hf n) Empty_pt))
                                (quote_hf (diag n))).

    Representability of diag as a PRST claim: PROV_PRST_DIAG_EVAL +
    PROV_PRST_NUMERAL_EVAL. STUB. Estimate: ~10 lines.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf "
        "      (App_pt diag_pr (Tup_pt (quote_hf n) Empty_pt)) "
        "      (quote_hf (diag n)))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_REPRESENTS_POS(p):
    """|- !p n. Proof_PRST p n ==>
              Prov_PRST (Eq_pf
                (App_pt Proof_PRST_pr (Tup_pt (quote_hf p) (Tup_pt (quote_hf n) Empty_pt)))
                T_pt).

    Positive branch of representability of the (decidable) Proof_PRST
    predicate. STUB.

    Here: one PROOF_PRST_PR_DEFINING specialisation per branch.
    Estimate: ~20 lines for both branches combined.
    """
    p.goal(
        "!pf n. Proof_PRST pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_PRST_pr (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt))) "
        "  T_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_REPRESENTS_NEG(p):
    """|- !p n. ~Proof_PRST p n ==>
              Prov_PRST (Eq_pf
                (App_pt Proof_PRST_pr (Tup_pt (quote_hf p) (Tup_pt (quote_hf n) Empty_pt)))
                F_pt). STUB."""
    p.goal(
        "!pf n. ~Proof_PRST pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_PRST_pr (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt))) "
        "  F_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3 (PRST) -- representability is (almost) free.")
    print("    T_PT_NEQ_F_PT                  :", pp_thm(T_PT_NEQ_F_PT))
    print()
    print("    REPRESENTABILITY_POSITIVE      :", pp_thm(REPRESENTABILITY_POSITIVE))
    print("    REPRESENTABILITY_NEGATIVE      :", pp_thm(REPRESENTABILITY_NEGATIVE))
    print()
    print("    SUBSTITUTE_REPRESENTS_PRST     :", pp_thm(SUBSTITUTE_REPRESENTS_PRST))
    print("    DIAG_REPRESENTS_PRST           :", pp_thm(DIAG_REPRESENTS_PRST))
    print("    PROOF_PRST_REPRESENTS_POS      :", pp_thm(PROOF_PRST_REPRESENTS_POS))
    print("    PROOF_PRST_REPRESENTS_NEG      :", pp_thm(PROOF_PRST_REPRESENTS_NEG))
