"""Derived PRST-formula connectives on godelnums.

Mirrors ``hf_connectives.py`` -- since PRST shares HF's propositional
constructors (Not_pf = Not_f, Imp_pf = Imp_f), the derived connectives
``And_pf`` / ``Or_pf`` / ``Iff_pf`` are literally the same as their HF
counterparts. We re-export them under PRST-flavoured names so downstream
PRST modules (diagonal lemma, godel_first_prst) have a uniform naming
convention, and re-state their substitute-distribution lemmas at the
PRST ``substitute_p`` level.

PRST is quantifier-free, so HF's ``Exists_f`` (which is built from
``Forall_f``) has no PRST counterpart; consumers express "there exists"
in the meta-theory or via PR-function evaluation instead.

Stubs: the substitute-distribution lemmas at ``substitute_p`` are
sorried; their proofs are the same as the hf_connectives versions,
extended to the App_pt case (which is irrelevant for these lemmas
because the connectives don't contain App_pt at their outer layer --
substitution distributes through them without seeing any App).
"""

from basics import mk_const
from parser import define, parse_type
from proof import proof
from hf_connectives import (
    And_f,  # noqa: F401  -- body of And_pf
    Or_f,  # noqa: F401  -- body of Or_pf
    Iff_f,  # noqa: F401  -- body of Iff_pf
    AND_F_AT,  # noqa: F401  -- re-exported
    OR_F_AT,  # noqa: F401  -- re-exported
    IFF_F_AT,  # noqa: F401  -- re-exported
)
from prst_syntax import (
    Not_pf,  # noqa: F401  -- parser alias in connective bodies
    Imp_pf,  # noqa: F401  -- parser alias
    substitute_p,  # noqa: F401  -- parser alias
    free_in_p,  # noqa: F401  -- parser alias for capture-avoidance
)
from nat0 import nat0_ty


# ---------------------------------------------------------------------------
# Stage 1' (PRST) -- derived connectives.
#
# Each PRST connective is defined as an alias of the corresponding HF
# connective so that parse-strings can refer to them.
# ---------------------------------------------------------------------------

AND_PF_DEF = define("And_pf", parse_type("nat0 -> nat0 -> nat0"), "And_f")
And_pf = mk_const("And_pf", [])

OR_PF_DEF = define("Or_pf", parse_type("nat0 -> nat0 -> nat0"), "Or_f")
Or_pf = mk_const("Or_pf", [])

IFF_PF_DEF = define("Iff_pf", parse_type("nat0 -> nat0 -> nat0"), "Iff_f")
Iff_pf = mk_const("Iff_pf", [])


# ---------------------------------------------------------------------------
# Stage 1' (a) -- substitute_p distribution for the derived connectives.
#
# Same shape as SUBSTITUTE_AT_AND / _OR / _IFF in hf_connectives, but
# stated at substitute_p (the PRST substitute). Proofs proceed by
# unfolding the connective via *_F_AT, then applying the PRST
# AT-equations for Not_pf / Imp_pf (which agree with the HF versions
# by re-export).
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_P_AT_AND(p):
    """|- !a b t v. substitute_p (And_pf a b) t v
                    = And_pf (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (And_pf a b) t v "
        "          = And_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_OR(p):
    """|- !a b t v. substitute_p (Or_pf a b) t v
                    = Or_pf (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (Or_pf a b) t v "
        "          = Or_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def SUBSTITUTE_P_AT_IFF(p):
    """|- !a b t v. substitute_p (Iff_pf a b) t v
                    = Iff_pf (substitute_p a t v) (substitute_p b t v). STUB."""
    p.goal(
        "!a b t v. substitute_p (Iff_pf a b) t v "
        "          = Iff_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1' (PRST) -- derived connectives and their substitute_p lemmas.")
    print("    SUBSTITUTE_P_AT_AND          :", pp_thm(SUBSTITUTE_P_AT_AND))
    print("    SUBSTITUTE_P_AT_OR           :", pp_thm(SUBSTITUTE_P_AT_OR))
    print("    SUBSTITUTE_P_AT_IFF          :", pp_thm(SUBSTITUTE_P_AT_IFF))
