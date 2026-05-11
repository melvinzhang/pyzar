"""First incompleteness theorem, formalised over PRST.

Headline theorem:

    |- ~ Prov_PRST G_PRST  /\\  ~ Prov_PRST (Not_pf G_PRST).

Strategy: diagonal lemma + Goedel sentence + consistency via the
standard nat0 HOL model. Stage breakdown:

  * Diagonal lemma: built on ``DIAG_REPRESENTS_PRST`` (~10 lines from
    ``PROV_PRST_DIAG_EVAL``) plus the standard substitution
    bookkeeping. The diag term is syntactically a PR-symbol
    application, so the representability step is a single defining
    equation.

  * Goedel sentence: fixed-point of ``Not_pf Prov_PRST_internal``.

  * Main theorem: two implications, each derived from the diagonal
    equivalence + representability + consistency / Sigma_1-soundness.

  * Consistency (stage 6): PRST has no set-theoretic axioms, so the
    consistency obligation is just one HOL-soundness theorem per
    registered PR-defining equation. Each obligation is uniform: the
    defining equation is a HOL theorem on nat0 by construction, since
    the PR symbol's value is a HOL function computed by HOL primitive
    recursion. Estimate ~80 lines.

  * Sigma_1-soundness: the represented predicates are PR-evaluated by
    symbol unfolding, so the soundness step "Prov_PRST F ==> F" for
    Sigma_1 F reduces to induction on the proof witness with no trace
    set to peel apart. Estimate ~80 lines.

Total: ~400 lines. Stubs throughout.
"""


from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty, ZERO, mk_suc0
from proof import proof, define_with_at
from prst_syntax import (
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    Imp_pf,  # noqa: F401  -- parser alias
    Empty_pt,  # noqa: F401
    App_pt,
    substitute_p,  # noqa: F401  -- parser alias
    is_pterm,  # noqa: F401
    is_pform,  # noqa: F401
    free_in_p,  # noqa: F401  -- parser alias
)
from prst_connectives import (
    And_pf,  # noqa: F401
    Iff_pf,
)
from prst_pr import (
    diag_pr,
    numeral_pr,  # noqa: F401
    Proof_PRST_pr,  # noqa: F401
    Adj_pt,  # noqa: F401  -- parser alias; "1" = Adj_pt Empty_pt Empty_pt
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
    Prov_PRST_internal,
    IS_PFORM_PROV_PRST_INTERNAL,
    FREE_IN_PROV_PRST_INTERNAL,
    PROV_PRST_REPRESENTS,
)
from prst_repr import (
    DIAG_REPRESENTS_PRST,  # noqa: F401
)
from hf_proof import var_x  # PRST re-uses the var_x constant from the encoding


# ---------------------------------------------------------------------------
# Stage 4 (PRST) -- the diagonal lemma.
#
# Goedel-Carnap construction in quantifier-free form:
#
#   theta_of_phi_p(phi) := substitute_p phi
#                                       (App_pt diag_pr (Tup_pt var_x Empty_pt))
#                                       var_x.
#
# psi := substitute_p theta_of_phi_p(phi) (numeral (theta_of_phi_p phi)) var_x.
#
# Since ``diag_pr`` is a PR function symbol, the term
# ``App_pt diag_pr (Tup_pt var_x Empty_pt)`` IS the value diag(x) at the
# syntactic level. The construction is binder-free: substitute the
# diag-term in for var_x directly, no existential quantifier needed.
# ---------------------------------------------------------------------------


_phi_n0 = Var("phi", nat0_ty)


# theta_of_phi_p(phi) := substitute_p phi (App_pt diag_pr (Tup_pt var_x Empty_pt)) var_x
THETA_OF_PHI_P_DEF = define(
    "theta_of_phi_p",
    parse_type("nat0 -> nat0"),
    "\\phi:nat0. substitute_p phi "
    "             (App_pt diag_pr (Tup_pt var_x Empty_pt)) "
    "             var_x",
)
theta_of_phi_p = mk_const("theta_of_phi_p", [])


@proof
def DIAGONAL_LEMMA_PRST(p):
    """|- !phi. is_pform phi
              /\\ (!v. free_in_p phi v ==> v = var_x)
              ==> is_pform (diag (theta_of_phi_p phi))
                /\\ Prov_PRST (Iff_pf (diag (theta_of_phi_p phi))
                                     (substitute_p phi
                                                   (numeral
                                                     (diag (theta_of_phi_p phi)))
                                                   var_x)).

    The quantifier-free diagonal lemma. Because diag is a PR function
    symbol, ``App_pt diag_pr (Tup_pt (numeral n) Empty_pt) = numeral
    (diag n)`` is one defining-equation step (DIAG_REPRESENTS_PRST):
    no functionality lemma, no existential elimination, no D-formula
    bookkeeping.

    Sketch: theta_of_phi_p(phi) is phi with var_x replaced by the
    diag-term. Substituting (numeral (theta_of_phi_p phi)) for var_x
    in theta_of_phi_p(phi) gives phi with var_x replaced by
    App_pt diag_pr (Tup_pt (numeral (theta_of_phi_p phi)) Empty_pt). By
    DIAG_REPRESENTS_PRST that App_pt term equals
    numeral (diag (theta_of_phi_p phi)), and substituting that into
    phi gives the right-hand side. The Iff is then closed by PRST
    equality reasoning.

    STUB. Estimate filled in: ~80 lines.
    """
    p.goal(
        "!phi. (is_pform phi /\\ (!v. free_in_p phi v ==> v = var_x)) ==> "
        "is_pform (diag (theta_of_phi_p phi)) /\\ "
        "Prov_PRST (Iff_pf (diag (theta_of_phi_p phi)) "
        "                  (substitute_p phi "
        "                                (numeral (diag (theta_of_phi_p phi))) "
        "                                var_x))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 5 (PRST) -- the Goedel sentence and the main theorem.
# ---------------------------------------------------------------------------
#
# G_PRST := diagonal-fixed-point of (Not_pf Prov_PRST_internal).
#
# Equivalently: G_PRST = diag (theta_of_phi_p (Not_pf Prov_PRST_internal)),
# and DIAGONAL_LEMMA_PRST at phi := Not_pf Prov_PRST_internal yields
#
#   Prov_PRST (Iff_pf G_PRST
#                     (Not_pf (substitute_p Prov_PRST_internal
#                                          (numeral G_PRST)
#                                          var_x))).
# ---------------------------------------------------------------------------


G_PRST_DEF = define(
    "G_PRST",
    parse_type("nat0"),
    "diag (theta_of_phi_p (Not_pf Prov_PRST_internal))",
)
G_PRST = mk_const("G_PRST", [])


@proof
def G_PRST_DIAGONAL_EQ(p):
    """|- Prov_PRST (Iff_pf G_PRST
                            (Not_pf (substitute_p Prov_PRST_internal
                                                  (numeral G_PRST)
                                                  var_x))).

    Specialisation of DIAGONAL_LEMMA_PRST at phi = Not_pf
    Prov_PRST_internal. Side conditions discharged by
    IS_PFORM_PROV_PRST_INTERNAL + FREE_IN_PROV_PRST_INTERNAL +
    closure of is_pform under Not_pf.

    STUB.
    """
    p.goal(
        "Prov_PRST (Iff_pf G_PRST "
        "                  (Not_pf (substitute_p Prov_PRST_internal "
        "                                        (numeral G_PRST) "
        "                                        var_x)))"
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 6 (PRST) -- consistency and Sigma_1-soundness.
#
# Consistency of PRST: standard nat0 HOL model, with one HOL soundness
# theorem per registered PR-symbol defining equation. Each defining
# equation is, by construction, a HOL theorem on nat0 (the PR symbol's
# value is a HOL function with the same recursion equations). PRST has
# no set-theoretic axioms, so there are no further model obligations
# beyond the PR-symbol layer. Estimate ~80 lines.
#
# Sigma_1-soundness: induction on the Prov_PRST witness; atomic case
# dispatches to PR-symbol defining equations. ~80 lines.
# ---------------------------------------------------------------------------


@proof
def PRST_CONSISTENT(p):
    """|- ~ Prov_PRST (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)).

    Consistency: PRST does not prove ``0 = 1``. Proof via the standard
    nat0 HOL model -- the model interprets every PRST term as its HOL
    value (each PR symbol's value is given by its HOL-side definition
    in prst_pr); each defining equation is true in the model by
    HOL-side primitive recursion; logical axioms by tautological
    correctness. STUB.
    """
    p.goal("~ Prov_PRST (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt))")
    p.sorry()


# Placeholders for the Sigma_1 vocabulary used in the soundness theorem.
# Real definitions would identify the Sigma_1 fragment + its standard
# interpretation in the HOL model.
IS_SIGMA1_DEF = define("is_sigma1", parse_type("nat0 -> bool"), "\\phi:nat0. T")
is_sigma1 = mk_const("is_sigma1", [])

SIGMA1_HOLDS_DEF = define(
    "sigma1_holds", parse_type("nat0 -> bool"), "\\phi:nat0. T"
)
sigma1_holds = mk_const("sigma1_holds", [])


@proof
def PRST_SIGMA1_SOUND(p):
    """|- !phi. is_sigma1 phi /\\ Prov_PRST phi ==> sigma1_holds phi.

    Sigma_1-soundness: any provable Sigma_1 PRST-sentence is true in
    the standard nat0 HOL model. Proof: induction on Prov_PRST witness;
    atomic case dispatches to the PR symbol's defining equation. STUB.
    """
    p.goal(
        "!phi. is_sigma1 phi /\\ Prov_PRST phi ==> sigma1_holds phi",
        types={"phi": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Main theorem.
# ---------------------------------------------------------------------------


@proof
def GODEL_FIRST_PRST(p):
    """|- ~ Prov_PRST G_PRST /\\ ~ Prov_PRST (Not_pf G_PRST).

    First incompleteness for PRST. Proof structure: standard Gödel
    argument with every step a Prov_PRST inference.

      First conjunct (PRST does not prove G_PRST):
        Suppose Prov_PRST G_PRST.
        By PROV_PRST_REPRESENTS,
            Prov_PRST (substitute_p Prov_PRST_internal (numeral G_PRST) var_x).
        By G_PRST_DIAGONAL_EQ,
            Prov_PRST (Not_pf G_PRST).
        Combined: Prov_PRST is inconsistent, contradicting PRST_CONSISTENT.

      Second conjunct (PRST does not prove Not_pf G_PRST):
        Suppose Prov_PRST (Not_pf G_PRST).
        By G_PRST_DIAGONAL_EQ,
            Prov_PRST (substitute_p Prov_PRST_internal (numeral G_PRST) var_x).
        By PRST_SIGMA1_SOUND, Prov_PRST G_PRST holds (in HOL).
        Combined with the assumption, PRST inconsistent.

    STUB. Estimate filled in: ~80 lines.
    """
    p.goal("~ Prov_PRST G_PRST /\\ ~ Prov_PRST (Not_pf G_PRST)")
    p.sorry()


# ---------------------------------------------------------------------------
# Corollary: essential undecidability.
# ---------------------------------------------------------------------------


@proof
def PRST_ESSENTIALLY_UNDECIDABLE(p):
    """|- !T. (!n. Prov_PRST n ==> T n)
            /\\ (~ T (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)))
            ==> ?S. ~ T S /\\ ~ T (Not_pf S).

    Essential undecidability: any consistent extension T of PRST (in
    the same language) is incomplete. Witness S = the diagonal-fixed
    point of (Not_pf Prov_T_internal) for T's own provability predicate;
    the same diagonal argument carries over. STUB.

    This is how PA, ZFC, HOL itself inherit incompleteness for free --
    each interprets PRST and is consistent, so each is incomplete.
    """
    p.goal(
        "!T. ((!n. Prov_PRST n ==> T n) "
        "    /\\ (~ T (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)))) "
        "    ==> ?S. ~ T S /\\ ~ T (Not_pf S)",
        types={"T": parse_type("nat0 -> bool")},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Summary -- module size estimates.
# ---------------------------------------------------------------------------
#
#   Stage 1 (syntax, prst_syntax.py)             ~500
#       App_pt constructor + the four recognisers' App_pt cases.
#
#   Stage 2 (proof system, prst_pr/prst_proof)   ~1000
#       is_logical_axiom re-used; is_pr_def + 6 base-layer defining
#       equations; Prov_PRST + closure rules.
#
#   Stage 3 (representability, prst_repr.py)      ~150
#       PR symbols are first-class terms; representability collapses
#       to a defining-equation lookup.
#
#   Stage 4 (diagonal lemma)                      ~150
#       App_pt-of-diag_pr is syntactically functional; no
#       DIAG_FUNCTIONAL needed.
#
#   Stage 5 (Goedel sentence + main theorem)      ~100
#
#   Stage 6 (consistency + Sigma_1-soundness)     ~250
#       One HOL-theorem per PR-defining equation.
#
#   TOTAL                                       ~2150
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 4 (PRST) -- diagonal lemma.")
    print("    THETA_OF_PHI_P_DEF      :", pp_thm(THETA_OF_PHI_P_DEF))
    print("    DIAGONAL_LEMMA_PRST     :", pp_thm(DIAGONAL_LEMMA_PRST))
    print()
    print("Stage 5 (PRST) -- Goedel sentence.")
    print("    G_PRST_DEF              :", pp_thm(G_PRST_DEF))
    print("    G_PRST_DIAGONAL_EQ      :", pp_thm(G_PRST_DIAGONAL_EQ))
    print()
    print("Stage 6 (PRST) -- consistency / soundness.")
    print("    PRST_CONSISTENT         :", pp_thm(PRST_CONSISTENT))
    print("    PRST_SIGMA1_SOUND       :", pp_thm(PRST_SIGMA1_SOUND))
    print()
    print("Main theorem.")
    print("    GODEL_FIRST_PRST        :", pp_thm(GODEL_FIRST_PRST))
    print("    PRST_ESSENTIALLY_UNDECIDABLE :", pp_thm(PRST_ESSENTIALLY_UNDECIDABLE))
