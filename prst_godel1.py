"""First incompleteness theorem, formalised over PRST.

This file is the PRST analog of ``godel_first.py``. The headline
theorem is identical:

    |- ~ Prov_PRST G_PRST  /\\  ~ Prov_PRST (Not_pf G_PRST).

The strategy is unchanged from the HF version (diagonal lemma + Goedel
sentence + consistency via the standard model). What changes is the
*cost*:

  * Diagonal lemma: HF uses ``DIAG_REPRESENTS`` (an axiom in
    godel_first.py, ~80 lines to discharge in HF) plus substantial
    substitution-pushing. PRST uses ``DIAG_REPRESENTS_PRST`` (~10
    lines from ``PROV_PRST_DIAG_EVAL``) plus the SAME substitution
    bookkeeping -- the diagonal lemma is structurally identical, only
    the representability step at the heart is cheaper.

  * Goedel sentence: identical -- a fixed-point of ``Not_pf
    Prov_PRST_internal``.

  * Main theorem: identical -- two implications, each derived from
    the diagonal equivalence + representability + consistency /
    Sigma_1-soundness.

  * Consistency (stage 6): different from HF. PRST has no HF1-HF5
    axioms (set-theoretic content lives only in the standard HF
    model, Jensen-Karp style), so the consistency obligation is just
    one HOL-soundness theorem per registered PR-defining equation.
    Each obligation is uniform: the defining equation is a HOL
    theorem on nat0 by construction, since the PR symbol's value is
    a HOL function computed by HOL primitive recursion. Estimate
    ~80 lines (smaller than HF's ~120 because there are no
    HF-axiom soundness obligations).

  * Sigma_1-soundness: arguably cheaper -- because the represented
    predicates are PR-evaluated by symbol unfolding rather than
    by trace existence, the soundness step "Prov_PRST F ==> F" for
    Sigma_1 F reduces to the same induction on the proof witness,
    but the atomic case no longer has to peel a trace set apart.

Total: ~400 lines, of which ~300 are shared verbatim with the HF
version. Stubs throughout.
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
    Proof_HF_pr,  # noqa: F401
    Adj_pt,  # noqa: F401  -- parser alias; "1" = Adj_pt Empty_pt Empty_pt
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
    Prov_PRST_internal,
    IS_PFORM_PROV_PRST_INTERNAL,
    FREE_IN_PROV_PRST_INTERNAL,
    PROV_PRST_REPRESENTS,
    PROV_HF_TO_PROV_PRST,  # noqa: F401  -- bridge for HF logic toolkit
)
from prst_repr import (
    DIAG_REPRESENTS_PRST,  # noqa: F401  -- replaces godel_first.DIAG_REPRESENTS
)
from hf_proof import var_x  # PRST re-uses HF variable choices


# ---------------------------------------------------------------------------
# Stage 4 (PRST) -- the diagonal lemma.
#
# Goedel-Carnap construction in quantifier-free form:
#
#   theta_of_phi_p(phi) := substitute_p phi
#                                       (App_pt diag_pr (cons_l var_x nil_l))
#                                       var_x.
#
# psi := substitute_p theta_of_phi_p(phi) (numeral (theta_of_phi_p phi)) var_x.
#
# Compare with the HF version (godel_first.py L582-589):
#   * HF used ``Exists_f var_y (And_f diag_internal (substitute phi var_y
#     var_x))``, where ``diag_internal`` was an axiomatized HF formula
#     representing the diag relation. The existential was needed because
#     diag was only available as a Sigma_1 relation, not a function.
#   * PRST collapses the existential entirely: since ``diag_pr`` is a
#     PR function symbol, the term ``App_pt diag_pr (cons_l var_x
#     nil_l)`` IS the value diag(x) at the syntactic level. There is
#     nothing to existentially quantify over; we just substitute the
#     diag-term in for var_x directly.
#
# This is the key payoff of moving from HF to PRST: the diagonal lemma
# requires no quantifiers at the object level, and ``diag_internal``
# (4 axiomatic stubs in godel_first.py: DIAG_REPRESENTS,
# IS_FORM_DIAG_INTERNAL, FREE_IN_DIAG_INTERNAL, DIAG_FUNCTIONAL)
# collapses to ZERO axiomatic stubs in PRST.
# ---------------------------------------------------------------------------


_phi_n0 = Var("phi", nat0_ty)


# theta_of_phi_p(phi) := substitute_p phi (App_pt diag_pr (cons_l var_x nil_l)) var_x
THETA_OF_PHI_P_DEF = define(
    "theta_of_phi_p",
    parse_type("nat0 -> nat0"),
    "\\phi:nat0. substitute_p phi "
    "             (App_pt diag_pr (cons_l var_x nil_l)) "
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

    PRST analog of DIAGONAL_LEMMA from godel_first.py. The proof is
    much shorter than the HF version because diag is a PR function
    symbol, so ``App_pt diag_pr (cons_l (numeral n) nil_l) = numeral
    (diag n)`` is one defining-equation step (DIAG_REPRESENTS_PRST).
    No DIAG_FUNCTIONAL, no existential elimination, no D-formula
    bookkeeping.

    Sketch: theta_of_phi_p(phi) is phi with var_x replaced by the
    diag-term. Substituting (numeral (theta_of_phi_p phi)) for var_x
    in theta_of_phi_p(phi) gives phi with var_x replaced by
    App_pt diag_pr (cons_l (numeral (theta_of_phi_p phi)) nil_l). By
    DIAG_REPRESENTS_PRST that App_pt term equals
    numeral (diag (theta_of_phi_p phi)), and substituting that into
    phi gives the right-hand side. The Iff is then closed by PRST
    equality reasoning.

    STUB. Estimate filled in: ~80 lines (vs ~400 in HF) -- the
    quantifier-free formulation eliminates the existential-elim
    bookkeeping entirely.
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
# Consistency of PRST: standard HF model on nat0, with one HOL
# soundness theorem per registered PR-symbol defining equation. Each
# defining equation is, by construction, a HOL theorem on nat0 (the
# PR symbol's value is a HOL function with the same recursion
# equations). No HF1-HF5 obligations (PRST has no set-theoretic
# axioms; their truth in the model is inherited from the HF carrier
# but not needed to certify any PRST axiom). Estimate ~80 lines.
#
# Sigma_1-soundness: same structure as for HF. ~80 lines.
# ---------------------------------------------------------------------------


@proof
def PRST_CONSISTENT(p):
    """|- ~ Prov_PRST (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)).

    Consistency: PRST does not prove ``0 = 1``. Proof via the standard
    HOL-level model on nat0 -- the model interprets every PRST term as
    its HOL value (each PR symbol's value is given by its HOL-side
    definition in prst_pr); each defining equation is true in the
    model by HOL-side primitive recursion; logical axioms by
    tautological correctness. STUB.
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
    the standard HOL model. Proof: induction on Prov_PRST witness,
    atomic case dispatches to the PR symbol's defining equation
    (cheaper than HF's trace-evaluation case). STUB.
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

    First incompleteness for PRST. Proof structure (identical to the
    HF version, but every Prov_HF step is now a Prov_PRST step):

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
    each extends PRST (via the standard HF embedding) and is
    consistent, so each is incomplete.
    """
    p.goal(
        "!T. ((!n. Prov_PRST n ==> T n) "
        "    /\\ (~ T (Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)))) "
        "    ==> ?S. ~ T S /\\ ~ T (Not_pf S)",
        types={"T": parse_type("nat0 -> bool")},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Summary -- the PRST vs HF accounting.
# ---------------------------------------------------------------------------
#
#                                            HF estimate     PRST estimate
#   Stage 1 (syntax)                            ~3500             ~500
#       (PRST inherits HF's; only adds App_pt clause + the four
#        recursive recognisers' App_pt cases.)
#
#   Stage 2 (proof system)                       ~900             ~400
#       (PRST inherits is_logical_axiom verbatim, drops HF1-HF5
#        entirely, adds is_pr_def + 6 base-layer defining equations.)
#
#   Stage 3 (representability)                  ~7900            ~1150
#       (PR symbols are first-class terms; no trace sets, no
#        functionality proofs, no quote_hf machinery.)
#
#   Stage 4 (diagonal lemma)                     ~400             ~150
#       (Same construction; DIAG_FUNCTIONAL goes away because
#        App_pt-of-diag_pr is syntactically functional.)
#
#   Stage 5 (Goedel sentence + main theorem)     ~200             ~100
#       (Identical proof; cheaper representability step.)
#
#   Stage 6 (consistency + Sigma_1-soundness)    ~200             ~250
#       (One extra HOL-theorem per PR-defining equation; modest
#        increase relative to the HF model construction.)
#
#   TOTAL                                      ~13100            ~2550
#
# Estimated 5x reduction in line count, with the bulk of the saving
# concentrated in Stage 3 (representability), which is exactly where
# the HF route is currently most painful.
#
# The tax: ~80 extra lines in Stage 6 for PR-symbol soundness, and
# a more involved Stage 1 syntax module if we want bullet-proof
# is_pterm / is_pform recognisers for App_pt. Both are uniform and
# mechanical.
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
