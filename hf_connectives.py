"""Derived HF-formula connectives on godelnums.

HF's primitive logical apparatus is ``Imp_f`` / ``Not_f`` plus ``Forall_f``
for the quantifier and ``Eq_f`` / ``In_a`` for the atoms. The remaining
boolean connectives and the existential are HOL-side abbreviations:

  And_f a b    := Not_f (Imp_f a (Not_f b))
  Or_f a b     := Imp_f (Not_f a) b
  Iff_f a b    := And_f (Imp_f a b) (Imp_f b a)
  Exists_f v f := Not_f (Forall_f v (Not_f f))

Lifted out of ``godel_first.py`` so that the Stage-3 representability
proofs in ``hf_repr_thms`` (which need ``And_f`` / ``Or_f`` / ``Exists_f``
inside the bodies of ``is_substitute_step_internal`` etc.) can refer to
them without circular imports.

Each connective ships:
  * a defining equation theorem (``AND_F_DEF`` etc.);
  * an applied form usable as a rewrite rule (``AND_F_AT`` etc., shaped
    ``|- !args. C args = unfolded``);
  * a substitute-distribution lemma (``SUBSTITUTE_AT_AND`` etc.); for
    ``Exists_f`` the distribution carries the same ``~(v = bvar)``
    capture-avoidance side condition as ``Forall_f``.
"""

from basics import mk_const
from parser import parse_type
from proof import proof, define_with_at
from tactics import SPECL, MP
from hf_syntax import (
    Not_f,  # noqa: F401  -- parser alias inside connective bodies
    Imp_f,  # noqa: F401  -- parser alias inside connective bodies
    Forall_f,  # noqa: F401  -- parser alias inside Exists_f body
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_FORALL_MISS,
)


# |- And_f = \a b. Not_f (Imp_f a (Not_f b))   /   |- !a b. And_f a b = ...
AND_F_DEF, AND_F_AT = define_with_at(
    "And_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. Not_f (Imp_f a (Not_f b))",
)
And_f = mk_const("And_f", [])


OR_F_DEF, OR_F_AT = define_with_at(
    "Or_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. Imp_f (Not_f a) b",
)
Or_f = mk_const("Or_f", [])


IFF_F_DEF, IFF_F_AT = define_with_at(
    "Iff_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\a:nat0. \\b:nat0. And_f (Imp_f a b) (Imp_f b a)",
)
Iff_f = mk_const("Iff_f", [])


EXISTS_F_DEF, EXISTS_F_AT = define_with_at(
    "Exists_f",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\v:nat0. \\f:nat0. Not_f (Forall_f v (Not_f f))",
)
Exists_f = mk_const("Exists_f", [])


# ---------------------------------------------------------------------------
# substitution-pushing lemmas for derived connectives.
#
# substitute distributes over And_f / Or_f / Iff_f unconditionally and over
# Exists_f under the side condition ``~(v = bvar)`` (mirroring Forall_f).
# ---------------------------------------------------------------------------


@proof
def SUBSTITUTE_AT_AND(p):
    """|- !a b t v. substitute (And_f a b) t v
    = And_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (And_f a b) t v = "
        "And_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (And_f a b) t v = And_f (substitute a t v) (substitute b t v)"
    ).by_rewrite([AND_F_AT, SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_AT_OR(p):
    """|- !a b t v. substitute (Or_f a b) t v
    = Or_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (Or_f a b) t v = "
        "Or_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (Or_f a b) t v = Or_f (substitute a t v) (substitute b t v)"
    ).by_rewrite([OR_F_AT, SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IMP])


@proof
def SUBSTITUTE_AT_IFF(p):
    """|- !a b t v. substitute (Iff_f a b) t v
    = Iff_f (substitute a t v) (substitute b t v)."""
    p.goal(
        "!a b t v. substitute (Iff_f a b) t v = "
        "Iff_f (substitute a t v) (substitute b t v)"
    )
    p.fix("a b t v")
    p.thus(
        "substitute (Iff_f a b) t v = Iff_f (substitute a t v) (substitute b t v)"
    ).by_rewrite(
        [
            IFF_F_AT,
            AND_F_AT,
            SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_IMP,
        ]
    )


@proof
def SUBSTITUTE_AT_EXISTS_MISS(p):
    """|- !w body t v. ~(v = w) ==>
            substitute (Exists_f w body) t v
            = Exists_f w (substitute body t v).

    Capture-avoidance side condition: the bound variable index ``w`` of
    the existential must not be the variable being substituted.
    """
    p.goal(
        "!w body t v. ~(v = w) ==> "
        "substitute (Exists_f w body) t v = "
        "Exists_f w (substitute body t v)"
    )
    p.fix("w body t v")
    p.assume("hne: ~(v = w)")
    forall_miss_at = SPECL(
        [p._parse("w"), p._parse("Not_f body"), p._parse("t"), p._parse("v")],
        SUBSTITUTE_AT_FORALL_MISS,
    )
    forall_miss_app = MP(forall_miss_at, p.fact("hne"))
    p.thus(
        "substitute (Exists_f w body) t v = Exists_f w (substitute body t v)"
    ).by_rewrite([EXISTS_F_AT, SUBSTITUTE_AT_NOT, forall_miss_app])


if __name__ == "__main__":
    from parser import pp_thm

    print("HF derived connectives:")
    print("    AND_F_DEF                :", pp_thm(AND_F_DEF))
    print("    AND_F_AT                 :", pp_thm(AND_F_AT))
    print("    OR_F_DEF                 :", pp_thm(OR_F_DEF))
    print("    OR_F_AT                  :", pp_thm(OR_F_AT))
    print("    IFF_F_DEF                :", pp_thm(IFF_F_DEF))
    print("    IFF_F_AT                 :", pp_thm(IFF_F_AT))
    print("    EXISTS_F_DEF             :", pp_thm(EXISTS_F_DEF))
    print("    EXISTS_F_AT              :", pp_thm(EXISTS_F_AT))
    print("    SUBSTITUTE_AT_AND        :", pp_thm(SUBSTITUTE_AT_AND))
    print("    SUBSTITUTE_AT_OR         :", pp_thm(SUBSTITUTE_AT_OR))
    print("    SUBSTITUTE_AT_IFF        :", pp_thm(SUBSTITUTE_AT_IFF))
    print("    SUBSTITUTE_AT_EXISTS_MISS:", pp_thm(SUBSTITUTE_AT_EXISTS_MISS))
