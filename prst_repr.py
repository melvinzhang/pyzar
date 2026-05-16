# ---------------------------------------------------------------------------
# Stage 3 (PRST) -- representability is (almost) free.
# ---------------------------------------------------------------------------
#
# This file keeps only the concrete representation bridges used downstream.
# ---------------------------------------------------------------------------


from nat0 import nat0_ty
from proof import proof
from prst_syntax import (
    Eq_pf,  # noqa: F401  -- parser alias
    Not_pf,  # noqa: F401  -- parser alias
    App_pt,
    Empty_pt,  # noqa: F401  -- "encoded false" sentinel
    substitute_p,  # noqa: F401  -- parser alias
)
from prst_pr import (
    substitute_pr,
    diag_pr,
    Proof_PRST_pr,
    T_pt,  # noqa: F401  -- parser alias
    F_pt,  # noqa: F401  -- parser alias
    T_PT_NEQ_F_PT,  # noqa: F401  -- re-export; hoisted to prst_pr
)
from prst_proof import (
    Prov_PRST,  # noqa: F401  -- parser alias
    Proof_PRST,  # noqa: F401  -- parser alias
)
from hf_repr_core import quote_hf  # noqa: F401  -- parser alias


# T_pt / F_pt -- the boolean encoding -- live in prst_pr.py so they're
# shared with prst_proof (MU_CORRECTNESS uses T_pt). Re-exported here
# for the parser via the imports at the top of this module.


# T_PT_NEQ_F_PT is hoisted to prst_pr.py so prst_proof can use it without
# a downstream-to-upstream import. Re-exported via the prst_pr import above
# for backwards compatibility with callers that already import it from here.


# ---------------------------------------------------------------------------
# Stage 3 (b) -- concrete representation bridges.
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
def PROOF_PRST_PR_BOOLEAN_VALUE(p):
    r"""|- !pf n. App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt
            \/ App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = F_pt.

    G1 role: dichotomy that drives every case-split routing a HOL fact
    about ``Proof_PRST`` to the PR side. Direct prerequisite of
    PROOF_PRST_PR_SEMANTIC_NEG and PROOF_PRST_PR_QUOTED_FALSE_EVAL, and
    therefore on the critical path for both the irrefutability conjunct
    and the consistency proof.

    Proof sketch:
      * Unfold the checker body via ``PROOF_PRST_PR_BOOL_VIEW``: the
        body is an ``and_bool_pr`` chain over
            ``is_tup_pr (Tup_pt pf (Tup_pt n Empty_pt))``,
            ``eq_nat_pr (tup_head_pr ...) ...``,
            ``valid_proof_list_pr pf n``.
      * Each leaf returns ``T_pt`` or ``F_pt`` by its own evaluator
        spec (``is_tup_pr`` shape spec, ``eq_nat_pr`` from Design 1,
        ``valid_proof_list_pr`` by structural induction on ``pf``).
      * Conclude with the ``and_bool_pr`` boolean-input identity:
        under boolean inputs the connective is itself
        ``{T_pt,F_pt}``-valued.

    No HOL <-> PR structural bridge: every step is a PR-side equation.
    """
    p.goal(
        "!pf n. "
        "App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt "
        "\\/ App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = F_pt",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_PR_SEMANTIC_NEG(p):
    """|- !pf n. ~Proof_PRST pf n ==>
            App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = F_pt.

    G1 role: the negative bridge that turns external HOL
    ``~ Proof_PRST pf n`` into the PR-side ``F_pt`` value. Consumed
    by ``PROOF_PRST_PR_QUOTED_FALSE_EVAL`` (irrefutability conjunct
    of ``GODEL_FIRST_PRST``) and by the ``PRST_CONSISTENT`` chain.

    Proof sketch:
      * By ``PROOF_PRST_PR_BOOLEAN_VALUE``, the App_pt value is
        either ``T_pt`` or ``F_pt``.
      * Suppose ``= T_pt``. By ``PRST_INTERNALIZES_TRUE_PR_EVAL``,
        PRST internally proves ``Eq_pf (App_pt ...) T_pt``, hence
        the internal ``Proof_PRST_internal[pf, n]`` proposition is
        Prov_PRST. By ``PRST_SIGMA1_SOUND`` applied to that Sigma_1
        formula, ``Proof_PRST pf n`` holds externally. Contradicts
        the hypothesis.
      * Therefore the result must be ``F_pt``.

    No structural HOL <-> PR body bridge: the ``T_pt`` branch is
    closed via PRST soundness, not by inspecting the checker body.
    """
    p.goal(
        "!pf n. ~Proof_PRST pf n ==> "
        "App_pt Proof_PRST_pr "
        "  (Tup_pt pf (Tup_pt n Empty_pt)) = F_pt",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_PR_QUOTED_TRUE_EVAL(p):
    """|- !pf n. Proof_PRST pf n ==>
            Prov_PRST (Eq_pf
              (App_pt Proof_PRST_pr
                (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt)))
              T_pt).

    G1 role: D1 quoted-input lift. The forward direction of
    ``PROV_PRST_REPRESENTS`` reaches the diagonal-lemma payload through
    this evaluator at quoted ``pf``, ``n``. Without it the forward
    representability path -- and therefore the unprovability conjunct of
    ``GODEL_FIRST_PRST`` -- cannot close.

    Intentional non-claim: this does *not* assert that raw checker
    inputs and ``quote_hf`` images coincide as HOL values. The bridge
    runs through PR-level numeral evaluation.

    Proof sketch:
      * From ``Proof_PRST pf n`` and the PR checker's specification,
        compute ``App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt))
        = T_pt`` at the raw inputs.
      * Apply ``PRST_INTERNALIZES_TRUE_PR_EVAL`` to obtain
        ``Prov_PRST (Eq_pf (App_pt ... raw inputs) T_pt)``.
      * Substitute raw inputs by their quote_hf images via
        ``PROV_PRST_NUMERAL_EVAL`` and equality congruence inside
        Prov_PRST. This re-targets the equality to the quoted-input
        application without depending on a raw-vs-quoted value
        identity.

    Dependencies: ``PRST_INTERNALIZES_TRUE_PR_EVAL``,
    ``PROV_PRST_NUMERAL_EVAL``, PRST equality congruence.
    """
    p.goal(
        "!pf n. Proof_PRST pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_PRST_pr "
        "    (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt))) "
        "  T_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_PR_QUOTED_FALSE_EVAL(p):
    """|- !pf n. ~Proof_PRST pf n ==>
            Prov_PRST (Eq_pf
              (App_pt Proof_PRST_pr
                (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt)))
              F_pt).

    G1 role: quoted-input form of the negative bridge. The
    irrefutability conjunct of ``GODEL_FIRST_PRST`` reasons under
    consistency that no quoted-proof-list certifies ``G_PRST``;
    this stub is what packages that fact as a Prov_PRST equality.

    Proof sketch:
      * Apply ``PROOF_PRST_PR_SEMANTIC_NEG`` to ``~ Proof_PRST pf n``
        to obtain ``App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n
        Empty_pt)) = F_pt`` at raw inputs (this is where the
        boolean-valuedness theorem and PRST soundness do their work).
      * Apply ``PRST_INTERNALIZES_FALSE_PR_EVAL`` to lift the raw-
        input equation into ``Prov_PRST (Eq_pf (App_pt ... raw) F_pt)``.
      * Substitute raw inputs by their ``quote_hf`` images via
        ``PROV_PRST_NUMERAL_EVAL`` and equality congruence inside
        Prov_PRST. As in the TRUE branch, no raw-vs-quoted value
        identity is required.

    Dependencies: ``PROOF_PRST_PR_SEMANTIC_NEG``,
    ``PRST_INTERNALIZES_FALSE_PR_EVAL``, ``PROV_PRST_NUMERAL_EVAL``,
    PRST equality congruence.
    """
    p.goal(
        "!pf n. ~Proof_PRST pf n ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt Proof_PRST_pr "
        "    (Tup_pt (quote_hf pf) (Tup_pt (quote_hf n) Empty_pt))) "
        "  F_pt)",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3 (PRST) -- representability is (almost) free.")
    print("    T_PT_NEQ_F_PT                  :", pp_thm(T_PT_NEQ_F_PT))
    print()
    print("    SUBSTITUTE_REPRESENTS_PRST     :", pp_thm(SUBSTITUTE_REPRESENTS_PRST))
    print("    DIAG_REPRESENTS_PRST           :", pp_thm(DIAG_REPRESENTS_PRST))
    print("    PROOF_PRST_PR_BOOLEAN_VALUE      :", pp_thm(PROOF_PRST_PR_BOOLEAN_VALUE))
    print("    PROOF_PRST_PR_SEMANTIC_NEG       :", pp_thm(PROOF_PRST_PR_SEMANTIC_NEG))
    print("    PROOF_PRST_PR_QUOTED_TRUE_EVAL   :", pp_thm(PROOF_PRST_PR_QUOTED_TRUE_EVAL))
    print("    PROOF_PRST_PR_QUOTED_FALSE_EVAL  :", pp_thm(PROOF_PRST_PR_QUOTED_FALSE_EVAL))
