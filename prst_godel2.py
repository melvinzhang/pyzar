# ---------------------------------------------------------------------------
# Stage 7 (PRST) -- Second incompleteness theorem.
# ---------------------------------------------------------------------------
"""Second incompleteness theorem, formalised over PRST.

Headline theorem:

    |- ~ Prov_PRST Con_PRST.

Where ``Con_PRST`` is the PRST formula stating PRST's own consistency:

    Con_PRST := Not_pf (substitute_p Prov_PRST_internal
                                     (numeral falsity_witness)
                                     var_x)

and ``falsity_witness`` is some canonical PRST-refutable closed
formula -- we use ``Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)`` (the
"0 = 1" sentence already used in ``PRST_CONSISTENT``).

Proof outline (Hilbert-Bernays-Loeb derivability conditions):

  (D1) From PRST |- phi, conclude PRST |- Prov_internal(numeral phi).
       Already available as PROV_PRST_REPRESENTS (the forward
       direction of the iff). Re-stated here under the standard name
       for the G2 argument.

  (D2) PRST proves the internalised modus ponens schema:
           Prov_internal(numeral (Imp_pf phi psi))
             -> Prov_internal(numeral phi)
             -> Prov_internal(numeral psi).
       Derived in the quantifier-free setting from:
         * a Pi_1 PR-side lemma MP_COMBINE_PR_CORRECT that combines two
           proof-witness terms p1, p2 into a single proof-witness term
           mp_combine_pr(p1, p2), and
         * MU_CORRECTNESS at f = Proof_PRST_pr, q = mp_combine_pr(...),
           args = [numeral psi].
       The witness extraction that an Exists-elim rule would do is
       replaced by applying MU_CORRECTNESS at the explicit combined
       witness.

  (D3) PRST proves the internalised Sigma_1-completeness for its own
       provability predicate:
           Prov_internal(numeral phi) -> Prov_internal(numeral
                                                       Prov_internal[phi]).
       Hardest derivability condition. Reduces to a Pi_1 structural
       induction on the formula encoding: PRST verifies each formula
       constructor case (Eq_pf, In_pa, Not_pf, Imp_pf, App_pt) under
       the assumption that subterms satisfy D3, then closes via
       MU_CORRECTNESS for the existential conclusion. ~200 lines once
       filled in -- the bulk of the G2 cost lives here.

  (Loeb) For any closed PRST formula psi:
           PRST |- (Prov_internal(numeral psi) -> psi)  ==>  PRST |- psi.
         Derived from D1-D3 via the Loeb diagonal construction (fixed
         point of (phi |-> Prov_internal(numeral phi) -> psi)). G2 is
         the special case psi = falsity_witness.

  (G2)   Apply Loeb at psi = falsity_witness. ``Prov_internal(num fw)
         -> fw`` is provably equivalent to ``Not_pf Prov_internal(num
         fw)`` (since fw is refutable in any consistent extension of
         logic), i.e. to Con_PRST. So if PRST proves Con_PRST then
         PRST proves fw -- contradicting consistency.

The G2 stack rests on:
  * G1 infrastructure (DIAGONAL_LEMMA_PRST, PROV_PRST_REPRESENTS).
  * MU_CORRECTNESS (the sole non-strict-PR axiom; cf. prst_proof).
  * One Pi_1 combinator lemma per derivability condition:
        D2: MP_COMBINE_PR_CORRECT.
        D3: a structural induction over formula shape -- written as
            a single closed PR-symbol theorem with parameters covering
            every Eq/In/Not/Imp/App branch.

Stubs throughout. Estimate filled in: ~350 lines total
(D1: trivial; D2: ~50; D3: ~200; Loeb + G2: ~100).
"""


from basics import mk_const
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from prst_syntax import (
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    Imp_pf,  # noqa: F401  -- parser alias
    Empty_pt,  # noqa: F401  -- parser alias
    App_pt,  # noqa: F401  -- parser alias
    substitute_p,  # noqa: F401  -- parser alias
    is_pform,  # noqa: F401  -- parser alias
)
from prst_pr import (
    Adj_pt,  # noqa: F401  -- parser alias
    Proof_PRST_pr,  # noqa: F401  -- parser alias
    find_proof_pr,  # noqa: F401  -- parser alias
    T_pt,  # noqa: F401  -- parser alias
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
    Prov_PRST_internal,
    PROV_PRST_REPRESENTS,  # noqa: F401  -- D1 backing
    MU_CORRECTNESS,  # noqa: F401  -- D2/D3 backing
)
from prst_godel1 import (
    DIAGONAL_LEMMA_PRST,  # noqa: F401  -- Loeb construction needs the diagonal
)
from hf_repr_core import (
    numeral,  # noqa: F401  -- parser alias
)
from hf_proof import (
    var_x,  # noqa: F401  -- parser alias
)


# ---------------------------------------------------------------------------
# Stage 7 (a) -- canonical falsity witness and the consistency formula.
# ---------------------------------------------------------------------------


# falsity_witness := the encoded formula "Empty_pt = Adj_pt Empty_pt
# Empty_pt", i.e. "0 = 1". A canonical PRST-refutable closed formula;
# any other would do (the choice doesn't affect the argument).
FALSITY_WITNESS_DEF = define(
    "falsity_witness",
    parse_type("nat0"),
    "Eq_pf Empty_pt (Adj_pt Empty_pt Empty_pt)",
)
falsity_witness = mk_const("falsity_witness", [])


# Con_PRST := PRST's internal consistency statement.
#   "PRST does not prove falsity_witness."
CON_PRST_DEF = define(
    "Con_PRST",
    parse_type("nat0"),
    "Not_pf (substitute_p Prov_PRST_internal (numeral falsity_witness) var_x)",
)
Con_PRST = mk_const("Con_PRST", [])


@proof
def IS_PFORM_CON_PRST(p):
    """|- is_pform Con_PRST. STUB.

    Closure of is_pform under substitute_p + Not_pf, applied to
    IS_PFORM_PROV_PRST_INTERNAL.
    """
    p.goal("is_pform Con_PRST")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 (b) -- Hilbert-Bernays-Loeb derivability conditions.
#
# D1 is a meta-rule (from a Prov_PRST proof of phi, conclude Prov_PRST
# of the internal-provability statement at phi). D2 and D3 are
# theorems *of* PRST -- single closed Prov_PRST claims expressing the
# corresponding implications.
# ---------------------------------------------------------------------------


@proof
def DERIV_D1(p):
    """|- !phi. Prov_PRST phi
              ==> Prov_PRST (substitute_p Prov_PRST_internal (numeral phi) var_x).

    The first derivability condition, stated as a meta-rule (the
    Prov_PRST in the hypothesis is the HOL-level provability
    predicate). One direction of PROV_PRST_REPRESENTS; restated here
    under the standard derivability-condition name.

    Proof: forward direction of PROV_PRST_REPRESENTS, ~5 lines. STUB.
    """
    p.goal(
        "!phi. Prov_PRST phi ==> "
        "Prov_PRST (substitute_p Prov_PRST_internal (numeral phi) var_x)",
        types={"phi": nat0_ty},
    )
    p.sorry()


# Π_1 PR-side lemma: combining two proof witnesses for (phi -> psi)
# and (phi) into one for (psi). Provable in PRST by definitional
# unfolding of mp_combine_pr (a PR symbol defined in prst_pr).
# Stub placeholder.
MP_COMBINE_PR_DEF = define(
    "mp_combine_pr",
    parse_type("nat0"),
    "0",  # stub; real body composes the two proof-list witnesses
)
mp_combine_pr = mk_const("mp_combine_pr", [])


@proof
def MP_COMBINE_PR_CORRECT(p):
    """|- !p1 p2 phi psi.
            App_pt Proof_PRST_pr (cons_l p1 (cons_l (Imp_pf phi psi) nil_l)) = T_pt
            /\\ App_pt Proof_PRST_pr (cons_l p2 (cons_l phi nil_l)) = T_pt
            ==> App_pt Proof_PRST_pr
                  (cons_l (App_pt mp_combine_pr (cons_l p1 (cons_l p2 nil_l)))
                          (cons_l psi nil_l)) = T_pt.

    The PR-side correctness of the proof-combinator: given proof lists
    p1 of (phi -> psi) and p2 of phi, mp_combine_pr appends one
    modus-ponens step and yields a proof of psi. Quantifier-free Pi_1;
    discharged by definitional unfolding of mp_combine_pr + structural
    case analysis on Proof_PRST_pr's cons_l recursion. ~30 lines. STUB.
    """
    p.goal(
        "!p1 p2 phi psi. "
        "  (App_pt Proof_PRST_pr (cons_l p1 (cons_l (Imp_pf phi psi) nil_l)) = T_pt "
        "   /\\ App_pt Proof_PRST_pr (cons_l p2 (cons_l phi nil_l)) = T_pt) "
        "  ==> App_pt Proof_PRST_pr "
        "        (cons_l (App_pt mp_combine_pr (cons_l p1 (cons_l p2 nil_l))) "
        "                (cons_l psi nil_l)) = T_pt",
        types={"p1": nat0_ty, "p2": nat0_ty, "phi": nat0_ty, "psi": nat0_ty},
    )
    p.sorry()


@proof
def DERIV_D2(p):
    """|- !phi psi. Prov_PRST (Imp_pf
                                (substitute_p Prov_PRST_internal
                                              (numeral (Imp_pf phi psi)) var_x)
                                (Imp_pf
                                  (substitute_p Prov_PRST_internal
                                                (numeral phi) var_x)
                                  (substitute_p Prov_PRST_internal
                                                (numeral psi) var_x))).

    The second derivability condition: PRST internally proves
    modus ponens for its own provability predicate. PRST-formula
    statement.

    Proof sketch (entirely quantifier-free, the key win of the
    mu_sym design):
      1. Reduce the substituted forms: substitute_p
         Prov_PRST_internal (numeral phi) var_x evaluates to
             Eq_pf (App_pt Proof_PRST_pr
                     (cons_l (App_pt find_proof_pr (cons_l (numeral phi) nil_l))
                       (cons_l (numeral phi) nil_l))) T_pt.
         (one substitute_p step under each App_pt / Eq_pf clause)
      2. Under the antecedents we have two witnesses
            p1 := App_pt find_proof_pr [numeral (Imp_pf phi psi)],
            p2 := App_pt find_proof_pr [numeral phi]
         certifying Proof_PRST_pr at (numeral (Imp_pf phi psi)) and
         (numeral phi) respectively.
      3. By MP_COMBINE_PR_CORRECT, mp_combine_pr(p1, p2) certifies
         Proof_PRST_pr at (numeral psi).
      4. By MU_CORRECTNESS at f = Proof_PRST_pr, q = mp_combine_pr(p1,
         p2), args = [numeral psi]: the mu-witness also certifies, i.e.
         App_pt Proof_PRST_pr
           (cons_l (App_pt find_proof_pr (cons_l (numeral psi) nil_l))
             (cons_l (numeral psi) nil_l)) = T_pt.
      5. Repackaging via Eq_pf gives the substituted-internal form,
         and Imp_pf-introduction closes the goal.

    Estimate ~50 lines. STUB.
    """
    p.goal(
        "!phi psi. Prov_PRST (Imp_pf "
        "  (substitute_p Prov_PRST_internal (numeral (Imp_pf phi psi)) var_x) "
        "  (Imp_pf "
        "    (substitute_p Prov_PRST_internal (numeral phi) var_x) "
        "    (substitute_p Prov_PRST_internal (numeral psi) var_x)))",
        types={"phi": nat0_ty, "psi": nat0_ty},
    )
    p.sorry()


@proof
def DERIV_D3(p):
    """|- !phi. Prov_PRST (Imp_pf
                            (substitute_p Prov_PRST_internal
                                          (numeral phi) var_x)
                            (substitute_p Prov_PRST_internal
                                          (numeral
                                            (substitute_p Prov_PRST_internal
                                                          (numeral phi) var_x))
                                          var_x)).

    The third derivability condition: PRST internally proves
    Sigma_1-completeness for its own provability predicate -- "if x
    is provable, then 'x is provable' is provable".

    Proof sketch:
      Internal Sigma_1-completeness is a Pi_1 structural induction on
      the formula encoding of phi. PRST proves, by cases on the head
      constructor of phi, that the "there is a proof" claim is itself
      provable. The atomic case dispatches to the PR symbol's defining
      equation (or, for Prov_internal, recursively via the mu-witness
      reflection lemma). Each case closes by:
        * exhibiting a concrete PR term computing a proof of the inner
          provability statement, via reflect_pr (a PR symbol that maps
          (phi, witness-for-phi) -> witness-for-Prov_internal(phi));
        * applying MU_CORRECTNESS to lift the explicit witness to the
          find_proof_pr form needed by Prov_PRST_internal.

      The reflection symbol reflect_pr is the analog of the
      "BProof" function in Buss / Boolos' G2 expositions: definable
      by primitive recursion on phi's syntax (Eq_pf, In_pa, Not_pf,
      Imp_pf, App_pt cases).

    Hardest derivability condition -- ~200 lines once filled in
    (structural induction over five formula constructors plus the
    reflect_pr boilerplate). STUB.
    """
    p.goal(
        "!phi. Prov_PRST (Imp_pf "
        "  (substitute_p Prov_PRST_internal (numeral phi) var_x) "
        "  (substitute_p Prov_PRST_internal "
        "    (numeral (substitute_p Prov_PRST_internal (numeral phi) var_x)) "
        "    var_x))",
        types={"phi": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 (c) -- Loeb's theorem.
#
# Loeb generalises G2. For any closed PRST formula psi:
#
#     |- (Prov_PRST (Imp_pf (substitute_p Prov_PRST_internal
#                                         (numeral psi) var_x) psi))
#        ==> Prov_PRST psi.
#
# G2 is recovered at psi = falsity_witness.
# ---------------------------------------------------------------------------


@proof
def LOEB_PRST(p):
    """|- !psi. is_pform psi
              /\\ Prov_PRST (Imp_pf (substitute_p Prov_PRST_internal
                                                  (numeral psi) var_x)
                                    psi)
              ==> Prov_PRST psi.

    Loeb's theorem. Proof via the diagonal lemma applied to the
    formula
        chi(x) := Imp_pf (substitute_p Prov_PRST_internal
                                       (Var_pt var_x) var_x) psi
    (where psi is closed). DIAGONAL_LEMMA_PRST gives a fixed point
    H with
        Prov_PRST (Iff_pf H (Imp_pf
                              (substitute_p Prov_PRST_internal
                                            (numeral H) var_x)
                              psi)).
    Then D1, D2, D3 chain (each one MP step) to derive Prov_PRST psi.

    Estimate ~60 lines once D1-D3 are real theorems. STUB.
    """
    p.goal(
        "!psi. (is_pform psi /\\ "
        "       Prov_PRST (Imp_pf (substitute_p Prov_PRST_internal "
        "                                       (numeral psi) var_x) psi)) "
        "      ==> Prov_PRST psi",
        types={"psi": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 (d) -- Second incompleteness.
# ---------------------------------------------------------------------------


@proof
def GODEL_SECOND_PRST(p):
    """|- ~ Prov_PRST Con_PRST.

    Second incompleteness for PRST: a consistent PRST does not prove
    its own consistency.

    Proof:
      Suppose Prov_PRST Con_PRST, i.e. Prov_PRST of
            Not_pf (substitute_p Prov_PRST_internal
                                 (numeral falsity_witness) var_x).
      This is propositionally equivalent (inside PRST, via
      propositional logic and the standard "Not_pf phi = (phi ->
      falsity_witness)" encoding modulo the choice of falsity_witness)
      to
            Prov_PRST (Imp_pf (substitute_p Prov_PRST_internal
                                            (numeral falsity_witness) var_x)
                              falsity_witness).
      By LOEB_PRST at psi = falsity_witness, this yields
            Prov_PRST falsity_witness.
      But that contradicts PRST_CONSISTENT.

      ~20 lines. STUB.
    """
    p.goal("~ Prov_PRST Con_PRST")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 (e) -- Corollaries.
# ---------------------------------------------------------------------------


@proof
def PRST_CANNOT_PROVE_OWN_CONSISTENCY(p):
    """|- Prov_PRST Con_PRST ==> Prov_PRST falsity_witness.

    Conditional restatement of G2: any PRST-proof of Con_PRST would
    yield a PRST-proof of inconsistency. Strictly weaker than
    GODEL_SECOND_PRST (which is the unconditional negation), but
    sometimes the form needed by downstream consumers.

    Proof: Loeb at falsity_witness applied to the conversion
    Con_PRST -> (Prov_internal(num falsity) -> falsity). STUB.
    """
    p.goal("Prov_PRST Con_PRST ==> Prov_PRST falsity_witness")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 7 (f) -- Module size estimate.
# ---------------------------------------------------------------------------
#
#   D1 (already in prst_proof.py)              ~5
#   D2 (mp_combine_pr correctness +
#       mu-correctness chain)                  ~50
#   D3 (Sigma_1 completeness; structural
#       induction over formula constructors)   ~200
#   Loeb's theorem                             ~60
#   G2 main theorem                            ~20
#   ----                                       ----
#   TOTAL                                      ~335
#
# PR symbols are first-class terms, so there are no trace sets and no
# functionality lemmas. Existential-elimination steps that would
# otherwise bloat D2/D3 are replaced by single applications of
# MU_CORRECTNESS at concrete witnesses.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 7 (PRST) -- second incompleteness.")
    print()
    print("Stage 7 (a) -- consistency formula.")
    print("    FALSITY_WITNESS_DEF      :", pp_thm(FALSITY_WITNESS_DEF))
    print("    CON_PRST_DEF             :", pp_thm(CON_PRST_DEF))
    print("    IS_PFORM_CON_PRST        :", pp_thm(IS_PFORM_CON_PRST))
    print()
    print("Stage 7 (b) -- Hilbert-Bernays-Loeb derivability conditions.")
    print("    DERIV_D1                 :", pp_thm(DERIV_D1))
    print("    MP_COMBINE_PR_CORRECT    :", pp_thm(MP_COMBINE_PR_CORRECT))
    print("    DERIV_D2                 :", pp_thm(DERIV_D2))
    print("    DERIV_D3                 :", pp_thm(DERIV_D3))
    print()
    print("Stage 7 (c) -- Loeb's theorem.")
    print("    LOEB_PRST                :", pp_thm(LOEB_PRST))
    print()
    print("Stage 7 (d) -- main theorem.")
    print("    GODEL_SECOND_PRST              :", pp_thm(GODEL_SECOND_PRST))
    print("    PRST_CANNOT_PROVE_OWN_CONSISTENCY :",
          pp_thm(PRST_CANNOT_PROVE_OWN_CONSISTENCY))
