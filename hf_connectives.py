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

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof
from tactics import SPECL, MP, AP_THM, BETA_CONV, TRANS, GENL
from hf_syntax import (
    Not_f,
    Imp_f,
    Forall_f,  # noqa: F401  -- parser alias inside Exists_f body
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_FORALL_MISS,
)


_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)
_v_n0 = Var("v", nat0_ty)
_f_n0 = Var("f", nat0_ty)


AND_F_DEF = define(
    "And_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _a_n0,
        mk_abs(_b_n0, mk_app(Not_f, mk_app(Imp_f, _a_n0, mk_app(Not_f, _b_n0)))),
    ),
)
And_f = mk_const("And_f", [])


OR_F_DEF = define(
    "Or_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(_a_n0, mk_abs(_b_n0, mk_app(Imp_f, mk_app(Not_f, _a_n0), _b_n0))),
)
Or_f = mk_const("Or_f", [])


IFF_F_DEF = define(
    "Iff_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _a_n0,
        mk_abs(
            _b_n0,
            mk_app(And_f, mk_app(Imp_f, _a_n0, _b_n0), mk_app(Imp_f, _b_n0, _a_n0)),
        ),
    ),
)
Iff_f = mk_const("Iff_f", [])


EXISTS_F_DEF = define(
    "Exists_f",
    parse_type("nat0 -> nat0 -> nat0"),
    mk_abs(
        _v_n0,
        mk_abs(_f_n0, mk_app(Not_f, mk_app(Forall_f, _v_n0, mk_app(Not_f, _f_n0)))),
    ),
)
Exists_f = mk_const("Exists_f", [])


# Pointwise-applied form: usable as a rewrite rule.  REWRITE_PROVE doesn't
# beta-reduce, so the bare DEF theorems don't fire under an applied head.
def _at2(def_th, x, y):
    th_x = AP_THM(def_th, x)
    th_x = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x, y)
    th_xy = TRANS(th_xy, BETA_CONV(rand(th_xy._concl)))
    return GENL([x, y], th_xy)


# |- !a b. And_f a b = Not_f (Imp_f a (Not_f b)).
AND_F_AT = _at2(AND_F_DEF, _a_n0, _b_n0)
# |- !a b. Or_f a b = Imp_f (Not_f a) b.
OR_F_AT = _at2(OR_F_DEF, _a_n0, _b_n0)
# |- !a b. Iff_f a b = And_f (Imp_f a b) (Imp_f b a).
IFF_F_AT = _at2(IFF_F_DEF, _a_n0, _b_n0)
# |- !v f. Exists_f v f = Not_f (Forall_f v (Not_f f)).
EXISTS_F_AT = _at2(EXISTS_F_DEF, _v_n0, _f_n0)


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
