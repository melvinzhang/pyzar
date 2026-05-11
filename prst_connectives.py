"""Derived PRST-formula connectives on godelnums.

PRST shares the propositional constructors from the nat0 encoding
(Not_pf = Not_f, Imp_pf = Imp_f), so the derived connectives
``And_pf`` / ``Or_pf`` / ``Iff_pf`` are aliases of the existing
``hf_connectives`` definitions. We re-export them under PRST-flavoured
names so downstream PRST modules (diagonal lemma, godel_first_prst)
have a uniform naming convention, and re-state their
substitute-distribution lemmas at the PRST ``substitute_p`` level.

PRST is quantifier-free; there is no existential connective at the
object level. Consumers express "there exists" in the meta-theory or
via PR-function evaluation instead.

Stubs: the substitute-distribution lemmas at ``substitute_p`` are
sorried; their proofs are the same shape as the hf_connectives
versions, extended to the App_pt case (which is irrelevant for these
lemmas because the connectives don't contain App_pt at their outer
layer -- substitution distributes through them without seeing any App).
"""

from basics import mk_const
from parser import define, parse_type
from proof import proof
from tactics import SYM
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
    NOT_PF_DEF,
    IMP_PF_DEF,
    SUBSTITUTE_P_AT_NOT,
    SUBSTITUTE_P_AT_IMP,
)
from nat0 import nat0_ty


# ---------------------------------------------------------------------------
# Stage 1' (PRST) -- derived connectives.
#
# Each PRST connective is defined as an alias of the corresponding
# constant from hf_connectives so that parse-strings can refer to them.
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
# AT-equations for Not_pf / Imp_pf (which agree with the hf_connectives
# versions by re-export).
# ---------------------------------------------------------------------------


# DSL friction: the PRST aliases (And_pf, Or_pf, Iff_pf, Not_pf, Imp_pf)
# are fresh constants distinct from their hf_connectives bodies, and
# SUBSTITUTE_P_AT_NOT / _IMP are stated at Not_pf / Imp_pf. The hf-side
# *_F_AT unfolders produce Not_f / Imp_f, so we use SYM(NOT_PF_DEF) /
# SYM(IMP_PF_DEF) to fold those back to Not_pf / Imp_pf before the
# substitute_p AT-equations can fire. by_rewrite normalises rules
# left-to-right, so feeding both unfold-the-And_pf-alias forward and
# fold-Not_f/Imp_f-via-SYM in the same call avoids a loop because the
# only Not_pf / Imp_pf producers are the SYM rules and the only Not_pf
# / Imp_pf consumers are the substitute_p AT-equations.
@proof
def SUBSTITUTE_P_AT_AND(p):
    """|- !a b t v. substitute_p (And_pf a b) t v
                    = And_pf (substitute_p a t v) (substitute_p b t v)."""
    p.goal(
        "!a b t v. substitute_p (And_pf a b) t v "
        "          = And_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.fix("a b t v")
    p.thus(
        "substitute_p (And_pf a b) t v "
        "= And_pf (substitute_p a t v) (substitute_p b t v)"
    ).by_rewrite(
        [
            AND_PF_DEF,
            AND_F_AT,
            SYM(NOT_PF_DEF),
            SYM(IMP_PF_DEF),
            SUBSTITUTE_P_AT_NOT,
            SUBSTITUTE_P_AT_IMP,
        ]
    )


@proof
def SUBSTITUTE_P_AT_OR(p):
    """|- !a b t v. substitute_p (Or_pf a b) t v
                    = Or_pf (substitute_p a t v) (substitute_p b t v)."""
    p.goal(
        "!a b t v. substitute_p (Or_pf a b) t v "
        "          = Or_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.fix("a b t v")
    p.thus(
        "substitute_p (Or_pf a b) t v "
        "= Or_pf (substitute_p a t v) (substitute_p b t v)"
    ).by_rewrite(
        [
            OR_PF_DEF,
            OR_F_AT,
            SYM(NOT_PF_DEF),
            SYM(IMP_PF_DEF),
            SUBSTITUTE_P_AT_NOT,
            SUBSTITUTE_P_AT_IMP,
        ]
    )


@proof
def SUBSTITUTE_P_AT_IFF(p):
    """|- !a b t v. substitute_p (Iff_pf a b) t v
                    = Iff_pf (substitute_p a t v) (substitute_p b t v)."""
    p.goal(
        "!a b t v. substitute_p (Iff_pf a b) t v "
        "          = Iff_pf (substitute_p a t v) (substitute_p b t v)",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.fix("a b t v")
    # Iff unfolds via And, so we also need AND_F_AT to reach Not_f / Imp_f.
    p.thus(
        "substitute_p (Iff_pf a b) t v "
        "= Iff_pf (substitute_p a t v) (substitute_p b t v)"
    ).by_rewrite(
        [
            IFF_PF_DEF,
            IFF_F_AT,
            AND_F_AT,
            SYM(NOT_PF_DEF),
            SYM(IMP_PF_DEF),
            SUBSTITUTE_P_AT_NOT,
            SUBSTITUTE_P_AT_IMP,
        ]
    )


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 1' (PRST) -- derived connectives and their substitute_p lemmas.")
    print("    SUBSTITUTE_P_AT_AND          :", pp_thm(SUBSTITUTE_P_AT_AND))
    print("    SUBSTITUTE_P_AT_OR           :", pp_thm(SUBSTITUTE_P_AT_OR))
    print("    SUBSTITUTE_P_AT_IFF          :", pp_thm(SUBSTITUTE_P_AT_IFF))
