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


# PROOF_PRST_PR_BOOLEAN_VALUE / _SEMANTIC_NEG / _QUOTED_TRUE_EVAL /
# _QUOTED_FALSE_EVAL are not stubbed as named theorems. They are
# call-site instantiations of ``PROOF_PRST_PR_REPRESENTS`` (the
# structural HOL<->PR bridge in prst_proof.py), composed where needed
# with ``PROV_PRST_PR_EVAL`` at ``r := T_pt`` / ``r := F_pt`` plus the
# ``quote_hf`` numeral interface for the quoted-input forms. If a
# downstream caller invokes one of these patterns often enough that a
# named lemma earns its keep, introduce it then as a real (non-sorry)
# theorem.


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3 (PRST) -- representability is (almost) free.")
    print("    T_PT_NEQ_F_PT              :", pp_thm(T_PT_NEQ_F_PT))
    print()
    print("    SUBSTITUTE_REPRESENTS_PRST :", pp_thm(SUBSTITUTE_REPRESENTS_PRST))
    print("    DIAG_REPRESENTS_PRST       :", pp_thm(DIAG_REPRESENTS_PRST))
