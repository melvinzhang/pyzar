"""Formalisation of Landau's *Foundations of Analysis*, Chapter 2 (Brüche).

A fraction ``x1/x2`` is the pair of natural numbers ``(x1, x2)``; we don't
introduce a separate fraction *type* — instead, the equivalence, order,
addition and multiplication of fractions are 4-ary predicates / functions
on natural numbers (matching Landau's surface syntax exactly).

  Definition 8 (equivalence)   feq x1 x2 y1 y2  :=  x1*y2 = y1*x2
  Definition 9 (greater than)  fgt x1 x2 y1 y2  :=  x1*y2 > y1*x2
  Definition 10 (less than)    flt x1 x2 y1 y2  :=  x1*y2 < y1*x2
  Definition 11/12 (>=, <=)    derived from the above
  Definition 13 (sum)          (x1 y2 + y1 x2) / (x2 y2)
  Definition 15 (product)      (x1 y1) / (x2 y2)

Each Satz is checked by running ``uv run frac.py``.
"""
from fusion import (
    Var, Comb, mk_app, mk_const, mk_eq, mk_fun_ty,
    bool_ty, dest_eq, type_of, rator, rand,
    REFL, TRANS, INST, MK_COMB,
)
from nat import (
    num_ty, ONE, mk_add, mk_mul, PLUS, TIMES,
    x as _xnat,
    SATZ_5, SATZ_6, SATZ_7, SATZ_9, SATZ_10, SATZ_29, SATZ_30, SATZ_31, RIGHT_DISTRIB,
    SATZ_32A, SATZ_32B, SATZ_32C, SATZ_33A, SATZ_33B, SATZ_33C,
    SATZ_15, SATZ_16A, SATZ_16B, SATZ_17, SATZ_18,
    SATZ_19A, SATZ_19B, SATZ_19C, SATZ_21, SATZ_22A, SATZ_22B, SATZ_23,
    SATZ_11, SATZ_12, SATZ_13, SATZ_14,
    GT_TO_GE, EQ_TO_GE, LT_TO_LE, EQ_TO_LE,
)
from tactics import (
    AP_TERM, AP_THM, SYM, SPEC, SPECL, GEN, GENL,
    CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP,
    DISJ1, DISJ2, NOT_ELIM,
    REWRITE_RULE, REWRITE_PROVE, AC_PROVE, TRANS_CHAIN,
    UNFOLD,
)
from parser import define, parse, pp_thm, DEFAULT_SIG
from proof import proof


# Standard Landau variable names for fraction components, all of type num.
x1 = Var("x1", num_ty); x2 = Var("x2", num_ty)
y1 = Var("y1", num_ty); y2 = Var("y2", num_ty)
z1 = Var("z1", num_ty); z2 = Var("z2", num_ty)
u1 = Var("u1", num_ty); u2 = Var("u2", num_ty)
v1 = Var("v1", num_ty); v2 = Var("v2", num_ty)
w1 = Var("w1", num_ty); w2 = Var("w2", num_ty)


_n4b = mk_fun_ty(num_ty,
        mk_fun_ty(num_ty,
          mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))))


# ---------------------------------------------------------------------------
# §1. Definition and Equivalence.
# ---------------------------------------------------------------------------

# Definition 8.   feq x1 x2 y1 y2  ≡  x1*y2 = y1*x2.
FEQ_DEF = define("feq", _n4b, "\\a b c d. a*d = c*b")
FEQ = mk_const("feq", [])

def mk_feq(a, b, c, d):
    return mk_app(FEQ, a, b, c, d)


# Satz 37:  feq x1 x2 x1 x2.    ("x1/x2 ~ x1/x2".)
@proof
def SATZ_37(p):
    p.goal("!x1 x2. feq x1 x2 x1 x2")
    p.fix("x1 x2")
    p.thus("feq x1 x2 x1 x2").by_unfold(REFL(mk_mul(x1, x2)), FEQ_DEF)


# Satz 38:  feq x1 x2 y1 y2  ==>  feq y1 y2 x1 x2.
@proof
def SATZ_38(p):
    p.goal("!x1 x2 y1 y2. feq x1 x2 y1 y2 ==> feq y1 y2 x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: feq x1 x2 y1 y2")
    p.have("eq: x1*y2 = y1*x2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, x1, x2, y1, y2), "h")
    p.have("sym: y1*x2 = x1*y2").by(SYM, "eq")
    p.thus("feq y1 y2 x1 x2").by_unfold("sym", FEQ_DEF)


# Satz 39 (transitivity of equivalence):
#   feq x1 x2 y1 y2  /\  feq y1 y2 z1 z2  ==>  feq x1 x2 z1 z2.
# Landau: multiply the two equations (x1 y2 = y1 x2) and (y1 z2 = z1 y2),
# AC-rearrange to (x1 z2)(y1 y2) = (z1 x2)(y1 y2), then cancel y1 y2
# (Satz 33B in Kapitel 1).
@proof
def SATZ_39(p):
    p.goal("!x1 x2 y1 y2 z1 z2. feq x1 x2 y1 y2 ==> feq y1 y2 z1 z2 "
           "==> feq x1 x2 z1 z2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h1: feq x1 x2 y1 y2", "h2: feq y1 y2 z1 z2")
    p.have("e1: x1*y2 = y1*x2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, x1, x2, y1, y2), "h1")
    p.have("e2: y1*z2 = z1*y2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, y1, y2, z1, z2), "h2")
    # (x1*y2)*(y1*z2) = (y1*x2)*(z1*y2).
    prod = MK_COMB(AP_TERM(TIMES, p.fact("e1")), p.fact("e2"))
    # Rearrange both sides via AC over (TIMES, SATZ_31, SATZ_29).
    p.have("ac_l: (x1*y2)*(y1*z2) = (x1*z2)*(y1*y2)") \
        .by_ac(TIMES, SATZ_31, SATZ_29)
    p.have("ac_r: (y1*x2)*(z1*y2) = (z1*x2)*(y1*y2)") \
        .by_ac(TIMES, SATZ_31, SATZ_29)
    p.have("can: (x1*z2)*(y1*y2) = (z1*x2)*(y1*y2)") \
        .by_thm(TRANS_CHAIN([SYM(p.fact("ac_l")), prod, p.fact("ac_r")]))
    p.have("res: x1*z2 = z1*x2") \
        .by(SATZ_33B, "x1*z2", "z1*x2", "y1*y2", "can")
    p.thus("feq x1 x2 z1 z2").by_unfold("res", FEQ_DEF)


# Satz 40:  feq x1 x2 (x1*x) (x2*x).    (Landau: x1*(x2*x) = (x1*x)*x2.)
@proof
def SATZ_40(p):
    p.goal("!x1 x2 x. feq x1 x2 (x1*x) (x2*x)")
    p.fix("x1 x2 x")
    p.have("eq: x1*(x2*x) = (x1*x)*x2").by_ac(TIMES, SATZ_31, SATZ_29)
    p.thus("feq x1 x2 (x1*x) (x2*x)").by_unfold("eq", FEQ_DEF)


# ---------------------------------------------------------------------------
# §2. Order.
# ---------------------------------------------------------------------------

# Definition 9.   fgt x1 x2 y1 y2  ≡  x1*y2 > y1*x2.
# Definition 10.  flt x1 x2 y1 y2  ≡  x1*y2 < y1*x2.
FGT_DEF = define("fgt", _n4b, "\\a b c d. a*d > c*b")
FLT_DEF = define("flt", _n4b, "\\a b c d. a*d < c*b")
FGT = mk_const("fgt", [])
FLT = mk_const("flt", [])


# Satz 41 (trichotomy):  feq \/ fgt \/ flt.   Reduces to SATZ_10 over num.
@proof
def SATZ_41(p):
    p.goal("!x1 x2 y1 y2. feq x1 x2 y1 y2 \\/ fgt x1 x2 y1 y2 "
           "\\/ flt x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2")
    p.thus("feq x1 x2 y1 y2 \\/ fgt x1 x2 y1 y2 \\/ flt x1 x2 y1 y2") \
        .by_unfold(SPECL([mk_mul(x1, y2), mk_mul(y1, x2)], SATZ_10),
                   FEQ_DEF, FGT_DEF, FLT_DEF)


# Satz 42:  fgt x1 x2 y1 y2 ==> flt y1 y2 x1 x2.   (Reduces to SATZ_11.)
@proof
def SATZ_42(p):
    p.goal("!x1 x2 y1 y2. fgt x1 x2 y1 y2 ==> flt y1 y2 x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: fgt x1 x2 y1 y2")
    p.have("g: x1*y2 > y1*x2") \
        .by_eq_mp(UNFOLD(FGT_DEF, x1, x2, y1, y2), "h")
    p.have("l: y1*x2 < x1*y2").by(SATZ_11, "x1*y2", "y1*x2", "g")
    p.thus("flt y1 y2 x1 x2").by_unfold("l", FLT_DEF)


# Satz 43:  flt x1 x2 y1 y2 ==> fgt y1 y2 x1 x2.   (Reduces to SATZ_12.)
@proof
def SATZ_43(p):
    p.goal("!x1 x2 y1 y2. flt x1 x2 y1 y2 ==> fgt y1 y2 x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: flt x1 x2 y1 y2")
    p.have("l: x1*y2 < y1*x2") \
        .by_eq_mp(UNFOLD(FLT_DEF, x1, x2, y1, y2), "h")
    p.have("g: y1*x2 > x1*y2").by(SATZ_12, "x1*y2", "y1*x2", "l")
    p.thus("fgt y1 y2 x1 x2").by_unfold("g", FGT_DEF)


# Satz 44:  fgt x1 x2 y1 y2, feq x1 x2 z1 z2, feq y1 y2 u1 u2  ==>  fgt z1 z2 u1 u2.
# Landau: multiply (y1 u2 = u1 y2) and (z1 x2 = x1 z2); rearrange to
#         (y1 x2)(z1 u2) = (u1 z2)(x1 y2).
#         Multiply (x1 y2 > y1 x2) by (u1 z2):  (u1 z2)(x1 y2) > (u1 z2)(y1 x2).
#         Combine and cancel y1*x2 (Satz 33).
@proof
def SATZ_44(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fgt x1 x2 y1 y2 ==> "
           "feq x1 x2 z1 z2 ==> feq y1 y2 u1 u2 ==> fgt z1 z2 u1 u2")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hgt: fgt x1 x2 y1 y2",
             "h1: feq x1 x2 z1 z2",
             "h2: feq y1 y2 u1 u2")
    p.have("g: x1*y2 > y1*x2") \
        .by_eq_mp(UNFOLD(FGT_DEF, x1, x2, y1, y2), "hgt")
    p.have("e1: x1*z2 = z1*x2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, x1, x2, z1, z2), "h1")
    p.have("e2: y1*u2 = u1*y2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, y1, y2, u1, u2), "h2")
    # (y1*u2)*(z1*x2) = (u1*y2)*(x1*z2).
    e_mul = MK_COMB(AP_TERM(TIMES, p.fact("e2")), SYM(p.fact("e1")))
    # AC-bridge each side: same multiset, different surface structure.
    ac_l = AC_PROVE(TIMES, SATZ_31, SATZ_29,
                    mk_eq(mk_mul(mk_mul(z1, u2), mk_mul(y1, x2)),
                          mk_mul(mk_mul(y1, u2), mk_mul(z1, x2))))
    ac_r = AC_PROVE(TIMES, SATZ_31, SATZ_29,
                    mk_eq(mk_mul(mk_mul(u1, y2), mk_mul(x1, z2)),
                          mk_mul(mk_mul(u1, z2), mk_mul(x1, y2))))
    p.have("eq: (z1*u2)*(y1*x2) = (u1*z2)*(x1*y2)") \
        .by_thm(TRANS_CHAIN([ac_l, e_mul, ac_r]))
    # (x1*y2)*(u1*z2) > (y1*x2)*(u1*z2)  via Satz 32A.
    p.have("ineq: (x1*y2)*(u1*z2) > (y1*x2)*(u1*z2)") \
        .by(SATZ_32A, "x1*y2", "y1*x2", "u1*z2", "g")
    # AC swap on both sides.
    p.have("ineq2: (u1*z2)*(x1*y2) > (u1*z2)*(y1*x2)") \
        .by_rewrite_of("ineq",
                       [SPECL([mk_mul(x1, y2), mk_mul(u1, z2)], SATZ_29),
                        SPECL([mk_mul(y1, x2), mk_mul(u1, z2)], SATZ_29)])
    # Splice eq into ineq2 LHS.
    p.have("final_ineq: (z1*u2)*(y1*x2) > (u1*z2)*(y1*x2)") \
        .by_rewrite_of("ineq2", [SYM(p.fact("eq"))])
    # Cancel y1*x2.
    p.have("res: z1*u2 > u1*z2") \
        .by(SATZ_33A, "z1*u2", "u1*z2", "y1*x2", "final_ineq")
    p.thus("fgt z1 z2 u1 u2").by_unfold("res", FGT_DEF)


# Satz 45:  flt x1 x2 y1 y2, feq x1 x2 z1 z2, feq y1 y2 u1 u2  ==>  flt z1 z2 u1 u2.
# Landau: chain through Satz 43, 44, 42.
@proof
def SATZ_45(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. flt x1 x2 y1 y2 ==> "
           "feq x1 x2 z1 z2 ==> feq y1 y2 u1 u2 ==> flt z1 z2 u1 u2")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hlt: flt x1 x2 y1 y2",
             "h1: feq x1 x2 z1 z2",
             "h2: feq y1 y2 u1 u2")
    p.have("yx_gt: fgt y1 y2 x1 x2").by(SATZ_43, "x1", "x2", "y1", "y2", "hlt")
    p.have("uz_gt: fgt u1 u2 z1 z2") \
        .by(SATZ_44, "y1", "y2", "x1", "x2", "u1", "u2", "z1", "z2",
            "yx_gt", "h2", "h1")
    p.thus("flt z1 z2 u1 u2").by(SATZ_42, "u1", "u2", "z1", "z2", "uz_gt")


# Definition 11.   fge x1 x2 y1 y2  ≡  fgt x1 x2 y1 y2 \/ feq x1 x2 y1 y2.
# Definition 12.   fle x1 x2 y1 y2  ≡  flt x1 x2 y1 y2 \/ feq x1 x2 y1 y2.
FGE_DEF = define("fge", _n4b, "\\a b c d. fgt a b c d \\/ feq a b c d")
FLE_DEF = define("fle", _n4b, "\\a b c d. flt a b c d \\/ feq a b c d")
FGE = mk_const("fge", [])
FLE = mk_const("fle", [])


# Satz 46:  fge x1 x2 y1 y2, feq x1 x2 z1 z2, feq y1 y2 u1 u2  ==>  fge z1 z2 u1 u2.
@proof
def SATZ_46(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fge x1 x2 y1 y2 ==> "
           "feq x1 x2 z1 z2 ==> feq y1 y2 u1 u2 ==> fge z1 z2 u1 u2")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hge: fge x1 x2 y1 y2",
             "h1: feq x1 x2 z1 z2",
             "h2: feq y1 y2 u1 u2")
    p.have("disj: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "hge")
    with p.thus("fge z1 z2 u1 u2").by_cases("disj"):
        with p.case("g: fgt x1 x2 y1 y2"):
            p.have("g_zu: fgt z1 z2 u1 u2") \
                .by(SATZ_44, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "g", "h1", "h2")
            p.have("orL: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
                .by(DISJ1, "g_zu", "feq z1 z2 u1 u2")
            p.thus("fge z1 z2 u1 u2").by_unfold("orL", FGE_DEF)
        with p.case("e: feq x1 x2 y1 y2"):
            # z1/z2 ~ x1/x2 ~ y1/y2 ~ u1/u2.
            p.have("zx: feq z1 z2 x1 x2") \
                .by(SATZ_38, "x1", "x2", "z1", "z2", "h1")
            p.have("zy: feq z1 z2 y1 y2") \
                .by(SATZ_39, "z1", "z2", "x1", "x2", "y1", "y2", "zx", "e")
            p.have("zu: feq z1 z2 u1 u2") \
                .by(SATZ_39, "z1", "z2", "y1", "y2", "u1", "u2", "zy", "h2")
            p.have("orR: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
                .by(DISJ2, "fgt z1 z2 u1 u2", "zu")
            p.thus("fge z1 z2 u1 u2").by_unfold("orR", FGE_DEF)


# Satz 47:  fle x1 x2 y1 y2, feq x1 x2 z1 z2, feq y1 y2 u1 u2  ==>  fle z1 z2 u1 u2.
@proof
def SATZ_47(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fle x1 x2 y1 y2 ==> "
           "feq x1 x2 z1 z2 ==> feq y1 y2 u1 u2 ==> fle z1 z2 u1 u2")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hle: fle x1 x2 y1 y2",
             "h1: feq x1 x2 z1 z2",
             "h2: feq y1 y2 u1 u2")
    p.have("disj: flt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FLE_DEF, x1, x2, y1, y2), "hle")
    with p.thus("fle z1 z2 u1 u2").by_cases("disj"):
        with p.case("l: flt x1 x2 y1 y2"):
            p.have("l_zu: flt z1 z2 u1 u2") \
                .by(SATZ_45, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "l", "h1", "h2")
            p.have("orL: flt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
                .by(DISJ1, "l_zu", "feq z1 z2 u1 u2")
            p.thus("fle z1 z2 u1 u2").by_unfold("orL", FLE_DEF)
        with p.case("e: feq x1 x2 y1 y2"):
            p.have("zx: feq z1 z2 x1 x2") \
                .by(SATZ_38, "x1", "x2", "z1", "z2", "h1")
            p.have("zy: feq z1 z2 y1 y2") \
                .by(SATZ_39, "z1", "z2", "x1", "x2", "y1", "y2", "zx", "e")
            p.have("zu: feq z1 z2 u1 u2") \
                .by(SATZ_39, "z1", "z2", "y1", "y2", "u1", "u2", "zy", "h2")
            p.have("orR: flt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
                .by(DISJ2, "flt z1 z2 u1 u2", "zu")
            p.thus("fle z1 z2 u1 u2").by_unfold("orR", FLE_DEF)


# Satz 48:  fge x1 x2 y1 y2  ==>  fle y1 y2 x1 x2.
@proof
def SATZ_48(p):
    p.goal("!x1 x2 y1 y2. fge x1 x2 y1 y2 ==> fle y1 y2 x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: fge x1 x2 y1 y2")
    p.have("disj: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "h")
    with p.thus("fle y1 y2 x1 x2").by_cases("disj"):
        with p.case("g: fgt x1 x2 y1 y2"):
            p.have("l: flt y1 y2 x1 x2").by(SATZ_42, "x1", "x2", "y1", "y2", "g")
            p.have("orL: flt y1 y2 x1 x2 \\/ feq y1 y2 x1 x2") \
                .by(DISJ1, "l", "feq y1 y2 x1 x2")
            p.thus("fle y1 y2 x1 x2").by_unfold("orL", FLE_DEF)
        with p.case("e: feq x1 x2 y1 y2"):
            p.have("e_sym: feq y1 y2 x1 x2").by(SATZ_38, "x1", "x2", "y1", "y2", "e")
            p.have("orR: flt y1 y2 x1 x2 \\/ feq y1 y2 x1 x2") \
                .by(DISJ2, "flt y1 y2 x1 x2", "e_sym")
            p.thus("fle y1 y2 x1 x2").by_unfold("orR", FLE_DEF)


# Satz 49:  fle x1 x2 y1 y2  ==>  fge y1 y2 x1 x2.
@proof
def SATZ_49(p):
    p.goal("!x1 x2 y1 y2. fle x1 x2 y1 y2 ==> fge y1 y2 x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: fle x1 x2 y1 y2")
    p.have("disj: flt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FLE_DEF, x1, x2, y1, y2), "h")
    with p.thus("fge y1 y2 x1 x2").by_cases("disj"):
        with p.case("l: flt x1 x2 y1 y2"):
            p.have("g: fgt y1 y2 x1 x2").by(SATZ_43, "x1", "x2", "y1", "y2", "l")
            p.have("orL: fgt y1 y2 x1 x2 \\/ feq y1 y2 x1 x2") \
                .by(DISJ1, "g", "feq y1 y2 x1 x2")
            p.thus("fge y1 y2 x1 x2").by_unfold("orL", FGE_DEF)
        with p.case("e: feq x1 x2 y1 y2"):
            p.have("e_sym: feq y1 y2 x1 x2").by(SATZ_38, "x1", "x2", "y1", "y2", "e")
            p.have("orR: fgt y1 y2 x1 x2 \\/ feq y1 y2 x1 x2") \
                .by(DISJ2, "fgt y1 y2 x1 x2", "e_sym")
            p.thus("fge y1 y2 x1 x2").by_unfold("orR", FGE_DEF)


# Satz 50 (transitivity of <):
#   flt x1 x2 y1 y2,  flt y1 y2 z1 z2  ==>  flt x1 x2 z1 z2.
@proof
def SATZ_50(p):
    p.goal("!x1 x2 y1 y2 z1 z2. flt x1 x2 y1 y2 ==> flt y1 y2 z1 z2 "
           "==> flt x1 x2 z1 z2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h1: flt x1 x2 y1 y2", "h2: flt y1 y2 z1 z2")
    p.have("l1: x1*y2 < y1*x2") \
        .by_eq_mp(UNFOLD(FLT_DEF, x1, x2, y1, y2), "h1")
    p.have("l2: y1*z2 < z1*y2") \
        .by_eq_mp(UNFOLD(FLT_DEF, y1, y2, z1, z2), "h2")
    # Multiply (x1*y2 < y1*x2) by (y1*z2):  (x1*y2)*(y1*z2) < (y1*x2)*(y1*z2).
    p.have("m1: (x1*y2)*(y1*z2) < (y1*x2)*(y1*z2)") \
        .by(SATZ_32C, "x1*y2", "y1*x2", "y1*z2", "l1")
    # Multiply (y1*z2 < z1*y2) by (y1*x2):  (y1*x2)*(y1*z2) < (y1*x2)*(z1*y2).
    p.have("m2_raw: (y1*z2)*(y1*x2) < (z1*y2)*(y1*x2)") \
        .by(SATZ_32C, "y1*z2", "z1*y2", "y1*x2", "l2")
    p.have("m2: (y1*x2)*(y1*z2) < (y1*x2)*(z1*y2)") \
        .by_rewrite_of("m2_raw",
                       [SPECL([mk_mul(y1, z2), mk_mul(y1, x2)], SATZ_29),
                        SPECL([mk_mul(z1, y2), mk_mul(y1, x2)], SATZ_29)])
    # Transitivity: (x1*y2)*(y1*z2) < (y1*x2)*(z1*y2).
    p.have("m: (x1*y2)*(y1*z2) < (y1*x2)*(z1*y2)") \
        .by(SATZ_15, "(x1*y2)*(y1*z2)", "(y1*x2)*(y1*z2)", "(y1*x2)*(z1*y2)",
            "m1", "m2")
    # AC bridge to (x1*z2)*(y1*y2) < (z1*x2)*(y1*y2).
    ac_l = AC_PROVE(TIMES, SATZ_31, SATZ_29,
                    mk_eq(mk_mul(mk_mul(x1, y2), mk_mul(y1, z2)),
                          mk_mul(mk_mul(x1, z2), mk_mul(y1, y2))))
    ac_r = AC_PROVE(TIMES, SATZ_31, SATZ_29,
                    mk_eq(mk_mul(mk_mul(y1, x2), mk_mul(z1, y2)),
                          mk_mul(mk_mul(z1, x2), mk_mul(y1, y2))))
    p.have("m_can: (x1*z2)*(y1*y2) < (z1*x2)*(y1*y2)") \
        .by_rewrite_of("m", [ac_l, ac_r])
    # Cancel y1*y2 (Satz 33C).
    p.have("res: x1*z2 < z1*x2") \
        .by(SATZ_33C, "x1*z2", "z1*x2", "y1*y2", "m_can")
    p.thus("flt x1 x2 z1 z2").by_unfold("res", FLT_DEF)


# Satz 51:  fle x1 x2 y1 y2 /\ flt y1 y2 z1 z2  -or-  flt x1 x2 y1 y2 /\ fle y1 y2 z1 z2
#           ==>  flt x1 x2 z1 z2.
@proof
def SATZ_51A(p):
    p.goal("!x1 x2 y1 y2 z1 z2. fle x1 x2 y1 y2 ==> flt y1 y2 z1 z2 "
           "==> flt x1 x2 z1 z2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("hle: fle x1 x2 y1 y2", "hlt: flt y1 y2 z1 z2")
    p.have("disj: flt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FLE_DEF, x1, x2, y1, y2), "hle")
    with p.thus("flt x1 x2 z1 z2").by_cases("disj"):
        with p.case("l: flt x1 x2 y1 y2"):
            p.thus("flt x1 x2 z1 z2") \
                .by(SATZ_50, "x1", "x2", "y1", "y2", "z1", "z2", "l", "hlt")
        with p.case("e: feq x1 x2 y1 y2"):
            # Use Satz 45 with z1/z2 = x1/x2 and u1/u2 = z1/z2.
            p.have("e_sym: feq y1 y2 x1 x2").by(SATZ_38, "x1", "x2", "y1", "y2", "e")
            p.have("e_id: feq z1 z2 z1 z2").by(SATZ_37, "z1", "z2")
            p.thus("flt x1 x2 z1 z2") \
                .by(SATZ_45, "y1", "y2", "z1", "z2", "x1", "x2", "z1", "z2",
                    "hlt", "e_sym", "e_id")


@proof
def SATZ_51B(p):
    p.goal("!x1 x2 y1 y2 z1 z2. flt x1 x2 y1 y2 ==> fle y1 y2 z1 z2 "
           "==> flt x1 x2 z1 z2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("hlt: flt x1 x2 y1 y2", "hle: fle y1 y2 z1 z2")
    p.have("disj: flt y1 y2 z1 z2 \\/ feq y1 y2 z1 z2") \
        .by_eq_mp(UNFOLD(FLE_DEF, y1, y2, z1, z2), "hle")
    with p.thus("flt x1 x2 z1 z2").by_cases("disj"):
        with p.case("l: flt y1 y2 z1 z2"):
            p.thus("flt x1 x2 z1 z2") \
                .by(SATZ_50, "x1", "x2", "y1", "y2", "z1", "z2", "hlt", "l")
        with p.case("e: feq y1 y2 z1 z2"):
            p.have("e_id: feq x1 x2 x1 x2").by(SATZ_37, "x1", "x2")
            p.thus("flt x1 x2 z1 z2") \
                .by(SATZ_45, "x1", "x2", "y1", "y2", "x1", "x2", "z1", "z2",
                    "hlt", "e_id", "e")


# Satz 52:  fle x1 x2 y1 y2,  fle y1 y2 z1 z2  ==>  fle x1 x2 z1 z2.
@proof
def SATZ_52(p):
    p.goal("!x1 x2 y1 y2 z1 z2. fle x1 x2 y1 y2 ==> fle y1 y2 z1 z2 "
           "==> fle x1 x2 z1 z2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h1: fle x1 x2 y1 y2", "h2: fle y1 y2 z1 z2")
    p.have("d1: flt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FLE_DEF, x1, x2, y1, y2), "h1")
    p.have("d2: flt y1 y2 z1 z2 \\/ feq y1 y2 z1 z2") \
        .by_eq_mp(UNFOLD(FLE_DEF, y1, y2, z1, z2), "h2")
    with p.thus("fle x1 x2 z1 z2").by_cases("d1"):
        with p.case("l1: flt x1 x2 y1 y2"):
            p.have("lt: flt x1 x2 z1 z2") \
                .by(SATZ_51B, "x1", "x2", "y1", "y2", "z1", "z2", "l1", "h2")
            p.have("orL: flt x1 x2 z1 z2 \\/ feq x1 x2 z1 z2") \
                .by(DISJ1, "lt", "feq x1 x2 z1 z2")
            p.thus("fle x1 x2 z1 z2").by_unfold("orL", FLE_DEF)
        with p.case("e1: feq x1 x2 y1 y2"):
            with p.thus("fle x1 x2 z1 z2").by_cases("d2"):
                with p.case("l2: flt y1 y2 z1 z2"):
                    p.have("e_id: feq z1 z2 z1 z2").by(SATZ_37, "z1", "z2")
                    p.have("e1_sym: feq y1 y2 x1 x2") \
                        .by(SATZ_38, "x1", "x2", "y1", "y2", "e1")
                    p.have("lt: flt x1 x2 z1 z2") \
                        .by(SATZ_45, "y1", "y2", "z1", "z2", "x1", "x2", "z1", "z2",
                            "l2", "e1_sym", "e_id")
                    p.have("orL: flt x1 x2 z1 z2 \\/ feq x1 x2 z1 z2") \
                        .by(DISJ1, "lt", "feq x1 x2 z1 z2")
                    p.thus("fle x1 x2 z1 z2").by_unfold("orL", FLE_DEF)
                with p.case("e2: feq y1 y2 z1 z2"):
                    p.have("eq: feq x1 x2 z1 z2") \
                        .by(SATZ_39, "x1", "x2", "y1", "y2", "z1", "z2", "e1", "e2")
                    p.have("orR: flt x1 x2 z1 z2 \\/ feq x1 x2 z1 z2") \
                        .by(DISJ2, "flt x1 x2 z1 z2", "eq")
                    p.thus("fle x1 x2 z1 z2").by_unfold("orR", FLE_DEF)


# Satz 53:  there is a fraction > x1/x2; witness (x1+x1)/x2.
@proof
def SATZ_53(p):
    p.goal("!x1 x2. fgt (x1 + x1) x2 x1 x2")
    p.fix("x1 x2")
    # (x1+x1)*x2 = x1*x2 + x1*x2.
    p.have("eq: (x1+x1)*x2 = x1*x2 + x1*x2").by(RIGHT_DISTRIB, "x1", "x1", "x2")
    # x1*x2 + x1*x2 > x1*x2.
    p.have("gt0: x1*x2 + x1*x2 > x1*x2").by(SATZ_18, "x1*x2", "x1*x2")
    p.have("res: (x1+x1)*x2 > x1*x2").by_rewrite_of("gt0", [SYM(p.fact("eq"))])
    p.thus("fgt (x1 + x1) x2 x1 x2").by_unfold("res", FGT_DEF)


# Satz 54:  there is a fraction < x1/x2; witness x1/(x2+x2).
@proof
def SATZ_54(p):
    p.goal("!x1 x2. flt x1 (x2 + x2) x1 x2")
    p.fix("x1 x2")
    # x1*(x2+x2) = x1*x2 + x1*x2 > x1*x2, hence x1*x2 < x1*(x2+x2).
    p.have("eq: x1*(x2+x2) = x1*x2 + x1*x2").by(SATZ_30, "x1", "x2", "x2")
    p.have("gt0: x1*x2 + x1*x2 > x1*x2").by(SATZ_18, "x1*x2", "x1*x2")
    p.have("lt: x1*x2 < x1*x2 + x1*x2") \
        .by(SATZ_11, "x1*x2 + x1*x2", "x1*x2", "gt0")
    p.have("res: x1*x2 < x1*(x2+x2)").by_rewrite_of("lt", [SYM(p.fact("eq"))])
    p.thus("flt x1 (x2 + x2) x1 x2").by_unfold("res", FLT_DEF)


# Satz 55 (density):  flt x1 x2 y1 y2  ==>  ?z1 z2. flt x1 x2 z1 z2 /\ flt z1 z2 y1 y2.
# Witness: ((x1+y1), (x2+y2)).
@proof
def SATZ_55(p):
    p.goal("!x1 x2 y1 y2. flt x1 x2 y1 y2 ==> "
           "?z1 z2. flt x1 x2 z1 z2 /\\ flt z1 z2 y1 y2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: flt x1 x2 y1 y2")
    p.have("k: x1*y2 < y1*x2") \
        .by_eq_mp(UNFOLD(FLT_DEF, x1, x2, y1, y2), "h")
    # x1*x2 + x1*y2 < x1*x2 + y1*x2  via SATZ_19C with z = x1*x2 on the left.
    p.have("step1_raw: x1*y2 + x1*x2 < y1*x2 + x1*x2") \
        .by(SATZ_19C, "x1*y2", "y1*x2", "x1*x2", "k")
    # Reorder: x1*x2 + x1*y2 < x1*x2 + y1*x2.
    p.have("step1: x1*x2 + x1*y2 < x1*x2 + y1*x2") \
        .by_rewrite_of("step1_raw",
                       [SPECL([mk_mul(x1, y2), mk_mul(x1, x2)], SATZ_6),
                        SPECL([mk_mul(y1, x2), mk_mul(x1, x2)], SATZ_6)])
    # Use distributive laws directly to fold:
    distr_l = SPECL([x1, x2, y2], SATZ_30)            # x1*(x2+y2) = x1*x2 + x1*y2
    distr_r = SPECL([x1, y1, x2], RIGHT_DISTRIB)       # (x1+y1)*x2 = x1*x2 + y1*x2
    p.have("ineq_left: x1*(x2+y2) < (x1+y1)*x2") \
        .by_rewrite_of("step1", [SYM(distr_l), SYM(distr_r)])
    p.have("h_left: flt x1 x2 (x1+y1) (x2+y2)") \
        .by_unfold("ineq_left", FLT_DEF)
    # Right half: (x1+y1)*y2 < y1*(x2+y2).
    # x1*y2 + y1*y2 < y1*x2 + y1*y2  via SATZ_19C with z = y1*y2.
    p.have("step2: x1*y2 + y1*y2 < y1*x2 + y1*y2") \
        .by(SATZ_19C, "x1*y2", "y1*x2", "y1*y2", "k")
    distr_l2 = SPECL([x1, y1, y2], RIGHT_DISTRIB)      # (x1+y1)*y2 = x1*y2 + y1*y2
    distr_r2 = SPECL([y1, x2, y2], SATZ_30)            # y1*(x2+y2) = y1*x2 + y1*y2
    p.have("ineq_right: (x1+y1)*y2 < y1*(x2+y2)") \
        .by_rewrite_of("step2", [SYM(distr_l2), SYM(distr_r2)])
    p.have("h_right: flt (x1+y1) (x2+y2) y1 y2") \
        .by_unfold("ineq_right", FLT_DEF)
    p.have("conj: flt x1 x2 (x1+y1) (x2+y2) /\\ flt (x1+y1) (x2+y2) y1 y2") \
        .by(CONJ, "h_left", "h_right")
    p.have("inner: ?z2. flt x1 x2 (x1+y1) z2 /\\ flt (x1+y1) z2 y1 y2") \
        .by_witness("x2+y2", "conj")
    p.thus("?z1 z2. flt x1 x2 z1 z2 /\\ flt z1 z2 y1 y2") \
        .by_witness("x1+y1", "inner")


# ---------------------------------------------------------------------------
# §3. Addition.
# ---------------------------------------------------------------------------
#
# Definition 13: x1/x2 + y1/y2 := (x1*y2 + y1*x2) / (x2*y2).
# Since we have no fraction-type, the sum is represented by the *pair*
# ``((x1*y2 + y1*x2), (x2*y2))`` and "x/y + a/b ~ p/q" is spelled out as
# the 4-ary feq applied to that pair.
# ---------------------------------------------------------------------------


# Helper: mul_eq_AC produces an AC-bridge equation over * via AC_PROVE.
def _mul_AC(lhs, rhs):
    return AC_PROVE(TIMES, SATZ_31, SATZ_29, mk_eq(lhs, rhs))


# Satz 56:  feq x1 x2 y1 y2 /\ feq z1 z2 u1 u2  ==>
#           feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2).
@proof
def SATZ_56(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. feq x1 x2 y1 y2 ==> feq z1 z2 u1 u2 "
           "==> feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("h1: feq x1 x2 y1 y2", "h2: feq z1 z2 u1 u2")
    p.have("e1: x1*y2 = y1*x2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, x1, x2, y1, y2), "h1")
    p.have("e2: z1*u2 = u1*z2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, z1, z2, u1, u2), "h2")
    # (x1*y2)*(z2*u2) = (y1*x2)*(z2*u2)  via AP_THM on e1.
    e1_zu = AP_THM(AP_TERM(TIMES, p.fact("e1")), mk_mul(z2, u2))
    # (z1*u2)*(x2*y2) = (u1*z2)*(x2*y2)  via AP_THM on e2.
    e2_xy = AP_THM(AP_TERM(TIMES, p.fact("e2")), mk_mul(x2, y2))
    # AC-rebracket: (x1*z2)*(y2*u2) = (y1*u2)*(x2*z2).
    eq_A = TRANS_CHAIN([
        _mul_AC(mk_mul(mk_mul(x1, z2), mk_mul(y2, u2)),
                mk_mul(mk_mul(x1, y2), mk_mul(z2, u2))),
        e1_zu,
        _mul_AC(mk_mul(mk_mul(y1, x2), mk_mul(z2, u2)),
                mk_mul(mk_mul(y1, u2), mk_mul(x2, z2)))])
    # (z1*x2)*(y2*u2) = (u1*y2)*(x2*z2).
    eq_B = TRANS_CHAIN([
        _mul_AC(mk_mul(mk_mul(z1, x2), mk_mul(y2, u2)),
                mk_mul(mk_mul(z1, u2), mk_mul(x2, y2))),
        e2_xy,
        _mul_AC(mk_mul(mk_mul(u1, z2), mk_mul(x2, y2)),
                mk_mul(mk_mul(u1, y2), mk_mul(x2, z2)))])
    # Sum: (x1*z2)*(y2*u2) + (z1*x2)*(y2*u2) = (y1*u2)*(x2*z2) + (u1*y2)*(x2*z2).
    sum_eq = MK_COMB(AP_TERM(PLUS, eq_A), eq_B)
    # Refold via RIGHT_DISTRIB:
    distr_l = SPECL([mk_mul(x1, z2), mk_mul(z1, x2), mk_mul(y2, u2)], RIGHT_DISTRIB)
    distr_r = SPECL([mk_mul(y1, u2), mk_mul(u1, y2), mk_mul(x2, z2)], RIGHT_DISTRIB)
    res = TRANS_CHAIN([distr_l, sum_eq, SYM(distr_r)])
    p.thus("feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
        .by_unfold(res, FEQ_DEF)


# Satz 57:  x1/x + x2/x ~ (x1+x2)/x  -- Landau's "x1*x + x2*x over x*x ~ (x1+x2)/x".
@proof
def SATZ_57(p):
    p.goal("!x1 x2 x. feq (x1*x + x2*x) (x*x) (x1+x2) x")
    p.fix("x1 x2 x")
    # Goal unfolds to: (x1*x + x2*x)*x = (x1+x2)*(x*x).
    rd = SPECL([x1, x2, _xnat], RIGHT_DISTRIB)         # (x1+x2)*x = x1*x + x2*x
    eq1 = AP_THM(AP_TERM(TIMES, SYM(rd)), _xnat)        # (x1*x + x2*x)*x = ((x1+x2)*x)*x
    eq2 = SPECL([mk_add(x1, x2), _xnat, _xnat], SATZ_31)
    res = TRANS(eq1, eq2)
    p.thus("feq (x1*x + x2*x) (x*x) (x1+x2) x").by_unfold(res, FEQ_DEF)


# Satz 58 (commutativity of fraction sum):
#   feq (x1*y2 + y1*x2) (x2*y2) (y1*x2 + x1*y2) (y2*x2).
@proof
def SATZ_58(p):
    p.goal("!x1 x2 y1 y2. feq (x1*y2 + y1*x2) (x2*y2) (y1*x2 + x1*y2) (y2*x2)")
    p.fix("x1 x2 y1 y2")
    # Goal unfolds to: (x1*y2 + y1*x2)*(y2*x2) = (y1*x2 + x1*y2)*(x2*y2).
    # Distribute on both sides; each side becomes a sum of two monomials, AC-equal.
    distr_l = SPECL([mk_mul(x1, y2), mk_mul(y1, x2), mk_mul(y2, x2)], RIGHT_DISTRIB)
    # (x1*y2 + y1*x2)*(y2*x2) = (x1*y2)*(y2*x2) + (y1*x2)*(y2*x2)
    distr_r = SPECL([mk_mul(y1, x2), mk_mul(x1, y2), mk_mul(x2, y2)], RIGHT_DISTRIB)
    # (y1*x2 + x1*y2)*(x2*y2) = (y1*x2)*(x2*y2) + (x1*y2)*(x2*y2)
    # Bridge each monomial in *-AC, then swap summands by +-AC.
    m1 = _mul_AC(mk_mul(mk_mul(x1, y2), mk_mul(y2, x2)),
                 mk_mul(mk_mul(x1, y2), mk_mul(x2, y2)))
    m2 = _mul_AC(mk_mul(mk_mul(y1, x2), mk_mul(y2, x2)),
                 mk_mul(mk_mul(y1, x2), mk_mul(x2, y2)))
    # |- (x1*y2)*(y2*x2) = (x1*y2)*(x2*y2)  and  (y1*x2)*(y2*x2) = (y1*x2)*(x2*y2).
    sum_norm = MK_COMB(AP_TERM(PLUS, m1), m2)
    # |- (x1*y2)*(y2*x2) + (y1*x2)*(y2*x2) = (x1*y2)*(x2*y2) + (y1*x2)*(x2*y2).
    sum_swap = AC_PROVE(PLUS, SATZ_5, SATZ_6,
        mk_eq(mk_add(mk_mul(mk_mul(x1, y2), mk_mul(x2, y2)),
                     mk_mul(mk_mul(y1, x2), mk_mul(x2, y2))),
              mk_add(mk_mul(mk_mul(y1, x2), mk_mul(x2, y2)),
                     mk_mul(mk_mul(x1, y2), mk_mul(x2, y2)))))
    res = TRANS_CHAIN([distr_l, sum_norm, sum_swap, SYM(distr_r)])
    p.thus("feq (x1*y2 + y1*x2) (x2*y2) (y1*x2 + x1*y2) (y2*x2)") \
        .by_unfold(res, FEQ_DEF)


# Satz 59 (associativity of fraction sum). The unfolded goal,
#   ((x1*y2 + y1*x2)*z2 + z1*(x2*y2)) * (x2*(y2*z2))
#       =
#   (x1*(y2*z2) + (y1*z2 + z1*y2)*x2) * ((x2*y2)*z2),
# distributes to a sum of three monomials on each side, with each pair
# AC-equivalent under multiplication. We bridge each monomial via _mul_AC and
# stitch the three together with addition's MK_COMB.
@proof
def SATZ_59(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "feq ((x1*y2 + y1*x2)*z2 + z1*(x2*y2)) ((x2*y2)*z2) "
           "(x1*(y2*z2) + (y1*z2 + z1*y2)*x2) (x2*(y2*z2))")
    p.fix("x1 x2 y1 y2 z1 z2")
    # Three monomial pairs:
    A  = mk_mul(mk_mul(mk_mul(x1, y2), z2), mk_mul(x2, mk_mul(y2, z2)))
    B  = mk_mul(mk_mul(mk_mul(y1, x2), z2), mk_mul(x2, mk_mul(y2, z2)))
    C  = mk_mul(mk_mul(z1, mk_mul(x2, y2)), mk_mul(x2, mk_mul(y2, z2)))
    Ap = mk_mul(mk_mul(x1, mk_mul(y2, z2)), mk_mul(mk_mul(x2, y2), z2))
    Bp = mk_mul(mk_mul(mk_mul(y1, z2), x2), mk_mul(mk_mul(x2, y2), z2))
    Cp = mk_mul(mk_mul(mk_mul(z1, y2), x2), mk_mul(mk_mul(x2, y2), z2))
    eq_A = _mul_AC(A, Ap); eq_B = _mul_AC(B, Bp); eq_C = _mul_AC(C, Cp)

    # LHS distribution: ((x1*y2+y1*x2)*z2 + z1*(x2*y2)) * (x2*(y2*z2)) = A+B+C.
    L_factor = mk_mul(x2, mk_mul(y2, z2))
    distr1 = SPECL([mk_mul(mk_add(mk_mul(x1, y2), mk_mul(y1, x2)), z2),
                    mk_mul(z1, mk_mul(x2, y2)),
                    L_factor], RIGHT_DISTRIB)
    inner_L = SPECL([mk_mul(x1, y2), mk_mul(y1, x2), z2], RIGHT_DISTRIB)
    chunk_L = TRANS(AP_THM(AP_TERM(TIMES, inner_L), L_factor),
                    SPECL([mk_mul(mk_mul(x1, y2), z2),
                           mk_mul(mk_mul(y1, x2), z2),
                           L_factor], RIGHT_DISTRIB))
    L_distrib = TRANS(distr1,
                      MK_COMB(AP_TERM(PLUS, chunk_L),
                              REFL(mk_mul(mk_mul(z1, mk_mul(x2, y2)), L_factor))))
    # |- LHS = (A + B) + C.
    L_assoc = SPECL([A, B, C], SATZ_5)
    L_full = TRANS(L_distrib, L_assoc)
    # |- LHS = A + (B + C).

    # RHS distribution: (x1*(y2*z2) + (y1*z2+z1*y2)*x2) * ((x2*y2)*z2) = A' + (B' + C').
    R_factor = mk_mul(mk_mul(x2, y2), z2)
    distr_R1 = SPECL([mk_mul(x1, mk_mul(y2, z2)),
                      mk_mul(mk_add(mk_mul(y1, z2), mk_mul(z1, y2)), x2),
                      R_factor], RIGHT_DISTRIB)
    inner_R = SPECL([mk_mul(y1, z2), mk_mul(z1, y2), x2], RIGHT_DISTRIB)
    chunk_R = TRANS(AP_THM(AP_TERM(TIMES, inner_R), R_factor),
                    SPECL([mk_mul(mk_mul(y1, z2), x2),
                           mk_mul(mk_mul(z1, y2), x2),
                           R_factor], RIGHT_DISTRIB))
    R_distrib = TRANS(distr_R1,
                      MK_COMB(AP_TERM(PLUS,
                                      REFL(mk_mul(mk_mul(x1, mk_mul(y2, z2)),
                                                   R_factor))),
                              chunk_R))
    # |- RHS = A' + (B' + C').

    bridge = MK_COMB(AP_TERM(PLUS, eq_A),
                     MK_COMB(AP_TERM(PLUS, eq_B), eq_C))
    # |- A + (B + C) = A' + (B' + C').
    res = TRANS_CHAIN([L_full, bridge, SYM(R_distrib)])
    p.thus("feq ((x1*y2 + y1*x2)*z2 + z1*(x2*y2)) ((x2*y2)*z2) "
           "(x1*(y2*z2) + (y1*z2 + z1*y2)*x2) (x2*(y2*z2))") \
        .by_unfold(res, FEQ_DEF)


# Satz 60:  x1/x2 + y1/y2 > x1/x2.
@proof
def SATZ_60(p):
    p.goal("!x1 x2 y1 y2. fgt (x1*y2 + y1*x2) (x2*y2) x1 x2")
    p.fix("x1 x2 y1 y2")
    distr = SPECL([mk_mul(x1, y2), mk_mul(y1, x2), x2], RIGHT_DISTRIB)
    # (x1*y2 + y1*x2)*x2 = (x1*y2)*x2 + (y1*x2)*x2.
    ac1 = _mul_AC(mk_mul(mk_mul(x1, y2), x2), mk_mul(x1, mk_mul(x2, y2)))
    eq1 = TRANS(distr, MK_COMB(AP_TERM(PLUS, ac1),
                                REFL(mk_mul(mk_mul(y1, x2), x2))))
    p.have("gt_a: x1*(x2*y2) + (y1*x2)*x2 > x1*(x2*y2)") \
        .by(SATZ_18, "x1*(x2*y2)", "(y1*x2)*x2")
    p.have("gt_b: (x1*y2 + y1*x2)*x2 > x1*(x2*y2)") \
        .by_rewrite_of("gt_a", [SYM(eq1)])
    p.thus("fgt (x1*y2 + y1*x2) (x2*y2) x1 x2").by_unfold("gt_b", FGT_DEF)


# Satz 61:  fgt x1 x2 y1 y2 ==>
#   fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2).
@proof
def SATZ_61(p):
    p.goal("!x1 x2 y1 y2 z1 z2. fgt x1 x2 y1 y2 ==> "
           "fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: fgt x1 x2 y1 y2")
    p.have("g0: x1*y2 > y1*x2") \
        .by_eq_mp(UNFOLD(FGT_DEF, x1, x2, y1, y2), "h")
    # Multiply by z2 (Satz 32A): (x1*y2)*z2 > (y1*x2)*z2.
    p.have("g1: (x1*y2)*z2 > (y1*x2)*z2") \
        .by(SATZ_32A, "x1*y2", "y1*x2", "z2", "g0")
    # AC bridges:  (x1*y2)*z2 = (x1*z2)*y2;  (y1*x2)*z2 = (y1*z2)*x2.
    ac_a = _mul_AC(mk_mul(mk_mul(x1, y2), z2), mk_mul(mk_mul(x1, z2), y2))
    ac_b = _mul_AC(mk_mul(mk_mul(y1, x2), z2), mk_mul(mk_mul(y1, z2), x2))
    p.have("g2: (x1*z2)*y2 > (y1*z2)*x2") \
        .by_rewrite_of("g1", [ac_a, ac_b])
    # Equality (z1*x2)*y2 = (z1*y2)*x2.
    eq_z = _mul_AC(mk_mul(mk_mul(z1, x2), y2), mk_mul(mk_mul(z1, y2), x2))
    p.have("ge_z: (z1*x2)*y2 >= (z1*y2)*x2").by(EQ_TO_GE, eq_z)
    # Combine: (x1*z2)*y2 + (z1*x2)*y2 > (y1*z2)*x2 + (z1*y2)*x2  via SATZ_22B.
    p.have("g3: (x1*z2)*y2 + (z1*x2)*y2 > (y1*z2)*x2 + (z1*y2)*x2") \
        .by(SATZ_22B, "(x1*z2)*y2", "(y1*z2)*x2", "(z1*x2)*y2", "(z1*y2)*x2",
            "g2", "ge_z")
    # Distribute back: (x1*z2 + z1*x2)*y2 > (y1*z2 + z1*y2)*x2.
    distr_l = SPECL([mk_mul(x1, z2), mk_mul(z1, x2), y2], RIGHT_DISTRIB)
    distr_r = SPECL([mk_mul(y1, z2), mk_mul(z1, y2), x2], RIGHT_DISTRIB)
    p.have("g4: (x1*z2 + z1*x2)*y2 > (y1*z2 + z1*y2)*x2") \
        .by_rewrite_of("g3", [SYM(distr_l), SYM(distr_r)])
    # Multiply by z2: ((x1*z2 + z1*x2)*y2)*z2 > ((y1*z2 + z1*y2)*x2)*z2.
    p.have("g5: ((x1*z2 + z1*x2)*y2)*z2 > ((y1*z2 + z1*y2)*x2)*z2") \
        .by(SATZ_32A, "(x1*z2 + z1*x2)*y2", "(y1*z2 + z1*y2)*x2", "z2", "g4")
    # AC re-bracket: (X*y2)*z2 = X*(y2*z2);  (Y*x2)*z2 = Y*(x2*z2).
    XL = mk_add(mk_mul(x1, z2), mk_mul(z1, x2))
    YR = mk_add(mk_mul(y1, z2), mk_mul(z1, y2))
    bra_l = SPECL([XL, y2, z2], SATZ_31)
    bra_r = SPECL([YR, x2, z2], SATZ_31)
    p.have("g6: (x1*z2 + z1*x2)*(y2*z2) > (y1*z2 + z1*y2)*(x2*z2)") \
        .by_rewrite_of("g5", [bra_l, bra_r])
    p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
        .by_unfold("g6", FGT_DEF)


# Satz 62a/b/c -- "respectively" form: from x R y derive (x+z) R (y+z), R ∈ {>, =, <}.
# 62a is Satz 61.
SATZ_62A = SATZ_61

@proof
def SATZ_62B(p):
    p.goal("!x1 x2 y1 y2 z1 z2. feq x1 x2 y1 y2 ==> "
           "feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: feq x1 x2 y1 y2")
    p.have("e_id: feq z1 z2 z1 z2").by(SATZ_37, "z1", "z2")
    p.thus("feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
        .by(SATZ_56, "x1", "x2", "y1", "y2", "z1", "z2", "z1", "z2",
            "h", "e_id")


@proof
def SATZ_62C(p):
    p.goal("!x1 x2 y1 y2 z1 z2. flt x1 x2 y1 y2 ==> "
           "flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: flt x1 x2 y1 y2")
    p.have("yx_gt: fgt y1 y2 x1 x2").by(SATZ_43, "x1", "x2", "y1", "y2", "h")
    p.have("sum_gt: fgt (y1*z2 + z1*y2) (y2*z2) (x1*z2 + z1*x2) (x2*z2)") \
        .by(SATZ_61, "y1", "y2", "x1", "x2", "z1", "z2", "yx_gt")
    p.thus("flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
        .by(SATZ_42, "y1*z2 + z1*y2", "y2*z2", "x1*z2 + z1*x2", "x2*z2",
            "sum_gt")


# Satz 64:  fgt x1 x2 y1 y2 /\ fgt z1 z2 u1 u2  ==>
#           fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2).
# Landau: chain Sätze 61 (twice) and Sätze 56/58 with transitivity Satz 50/SATZ_44+45.
# Approach: x/x2 + z/z2 > y/y2 + z/z2 (Satz 61) and y/y2 + z/z2 ~ z/z2 + y/y2 > z/z2 + u/u2 ~ y/y2 + u/u2.
@proof
def SATZ_64(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fgt x1 x2 y1 y2 ==> fgt z1 z2 u1 u2 ==> "
           "fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("h_xy: fgt x1 x2 y1 y2", "h_zu: fgt z1 z2 u1 u2")
    # Step 1: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)  via Satz 61.
    p.have("step1: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
        .by(SATZ_61, "x1", "x2", "y1", "y2", "z1", "z2", "h_xy")
    # Step 2: fgt (z1*y2 + y1*z2) (z2*y2) (u1*y2 + y1*u2) (u2*y2)  via Satz 61
    #          (with x↔z, y↔u, z↔y).
    p.have("step2: fgt (z1*y2 + y1*z2) (z2*y2) (u1*y2 + y1*u2) (u2*y2)") \
        .by(SATZ_61, "z1", "z2", "u1", "u2", "y1", "y2", "h_zu")
    # Step 3: feq (z1*y2 + y1*z2) (z2*y2) (y1*z2 + z1*y2) (y2*z2)
    #   = SATZ_58 at (z1, z2, y1, y2)  (gives (z1*y2 + y1*z2)/(z2*y2) ~ (y1*z2+z1*y2)/(y2*z2)).
    p.have("step3: feq (z1*y2 + y1*z2) (z2*y2) (y1*z2 + z1*y2) (y2*z2)") \
        .by(SATZ_58, "z1", "z2", "y1", "y2")
    # Step 4: feq (u1*y2 + y1*u2) (u2*y2) (y1*u2 + u1*y2) (y2*u2)
    #   = SATZ_58 at (u1, u2, y1, y2).
    p.have("step4: feq (u1*y2 + y1*u2) (u2*y2) (y1*u2 + u1*y2) (y2*u2)") \
        .by(SATZ_58, "u1", "u2", "y1", "y2")
    # Bridge step2 with step3, step4 via Satz 44 to relate to (y1*z2 + z1*y2)/(y2*z2)
    # and (y1*u2 + u1*y2)/(y2*u2):
    #   fgt (y1*z2 + z1*y2) (y2*z2) (y1*u2 + u1*y2) (y2*u2)
    p.have("step5: fgt (y1*z2 + z1*y2) (y2*z2) (y1*u2 + u1*y2) (y2*u2)") \
        .by(SATZ_44,
            "z1*y2 + y1*z2", "z2*y2", "u1*y2 + y1*u2", "u2*y2",
            "y1*z2 + z1*y2", "y2*z2", "y1*u2 + u1*y2", "y2*u2",
            "step2", "step3", "step4")
    # Transitivity: step1 (>) and step5 (>) ==> via SATZ_50 (lt-trans, after flip).
    # Actually, fgt is transitive: chain via flt-trans. Use SATZ_50 (transitivity of flt)
    # after flipping both via SATZ_42; or use a fgt-transitivity helper.
    # Simpler: fgt a b ==> flt b a; chain flt; flip back.
    p.have("lt5: flt (y1*u2 + u1*y2) (y2*u2) (y1*z2 + z1*y2) (y2*z2)") \
        .by(SATZ_42, "y1*z2 + z1*y2", "y2*z2", "y1*u2 + u1*y2", "y2*u2", "step5")
    p.have("lt1: flt (y1*z2 + z1*y2) (y2*z2) (x1*z2 + z1*x2) (x2*z2)") \
        .by(SATZ_42, "x1*z2 + z1*x2", "x2*z2", "y1*z2 + z1*y2", "y2*z2", "step1")
    p.have("lt_chain: flt (y1*u2 + u1*y2) (y2*u2) (x1*z2 + z1*x2) (x2*z2)") \
        .by(SATZ_50, "y1*u2 + u1*y2", "y2*u2", "y1*z2 + z1*y2", "y2*z2",
            "x1*z2 + z1*x2", "x2*z2", "lt5", "lt1")
    p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
        .by(SATZ_43, "y1*u2 + u1*y2", "y2*u2", "x1*z2 + z1*x2", "x2*z2",
            "lt_chain")


# Satz 63a/b/c: cancellation of summand z1/z2.
# Proof template (cf. nat SATZ_20): trichotomy on (x R y) and use Satz 62 to
# contradict the unequal cases.

def _sum_terms(a1, a2, c1, c2):
    """Unfolded numerator/denominator of a1/a2 + c1/c2."""
    return (mk_add(mk_mul(a1, c2), mk_mul(c1, a2)), mk_mul(a2, c2))


@proof
def SATZ_63A(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2) "
           "==> fgt x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h_a: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    s1n, s1d = _sum_terms(x1, x2, z1, z2)
    s2n, s2d = _sum_terms(y1, y2, z1, z2)
    p.have("h_a_n: (x1*z2 + z1*x2)*(y2*z2) > (y1*z2 + z1*y2)*(x2*z2)") \
        .by_eq_mp(UNFOLD(FGT_DEF, s1n, s1d, s2n, s2d), "h_a")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.have("eq_sum: feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_62B, "x1", "x2", "y1", "y2", "z1", "z2", "h_eq")
            p.have("eq_n: (x1*z2 + z1*x2)*(y2*z2) = (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, s1n, s1d, s2n, s2d), "eq_sum")
            p.absurd().auto("h_a_n", "eq_n")
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.thus("fgt x1 x2 y1 y2").by_thm(p.fact("h_gt"))
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.have("lt_sum: flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_62C, "x1", "x2", "y1", "y2", "z1", "z2", "h_lt")
            p.have("lt_n: (x1*z2 + z1*x2)*(y2*z2) < (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FLT_DEF, s1n, s1d, s2n, s2d), "lt_sum")
            p.absurd().auto("lt_n", "h_a_n")


@proof
def SATZ_63B(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2) "
           "==> feq x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h_a: feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    s1n, s1d = _sum_terms(x1, x2, z1, z2)
    s2n, s2d = _sum_terms(y1, y2, z1, z2)
    p.have("h_a_n: (x1*z2 + z1*x2)*(y2*z2) = (y1*z2 + z1*y2)*(x2*z2)") \
        .by_eq_mp(UNFOLD(FEQ_DEF, s1n, s1d, s2n, s2d), "h_a")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.thus("feq x1 x2 y1 y2").by_thm(p.fact("h_eq"))
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.have("gt_sum: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_61, "x1", "x2", "y1", "y2", "z1", "z2", "h_gt")
            p.have("gt_n: (x1*z2 + z1*x2)*(y2*z2) > (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, s1n, s1d, s2n, s2d), "gt_sum")
            p.absurd().auto("gt_n", "h_a_n")
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.have("lt_sum: flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_62C, "x1", "x2", "y1", "y2", "z1", "z2", "h_lt")
            p.have("lt_n: (x1*z2 + z1*x2)*(y2*z2) < (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FLT_DEF, s1n, s1d, s2n, s2d), "lt_sum")
            p.absurd().auto("lt_n", "h_a_n")


@proof
def SATZ_63C(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2) "
           "==> flt x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h_a: flt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)")
    s1n, s1d = _sum_terms(x1, x2, z1, z2)
    s2n, s2d = _sum_terms(y1, y2, z1, z2)
    p.have("h_a_n: (x1*z2 + z1*x2)*(y2*z2) < (y1*z2 + z1*y2)*(x2*z2)") \
        .by_eq_mp(UNFOLD(FLT_DEF, s1n, s1d, s2n, s2d), "h_a")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.have("eq_sum: feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_62B, "x1", "x2", "y1", "y2", "z1", "z2", "h_eq")
            p.have("eq_n: (x1*z2 + z1*x2)*(y2*z2) = (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, s1n, s1d, s2n, s2d), "eq_sum")
            p.absurd().auto("h_a_n", "eq_n")
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.have("gt_sum: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_61, "x1", "x2", "y1", "y2", "z1", "z2", "h_gt")
            p.have("gt_n: (x1*z2 + z1*x2)*(y2*z2) > (y1*z2 + z1*y2)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, s1n, s1d, s2n, s2d), "gt_sum")
            p.absurd().auto("h_a_n", "gt_n")
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.thus("flt x1 x2 y1 y2").by_thm(p.fact("h_lt"))


# Satz 65a/b: x>=y, z>u (or x>y, z>=u) ==> x+z > y+u.
@proof
def SATZ_65A(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fge x1 x2 y1 y2 ==> fgt z1 z2 u1 u2 ==> "
           "fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hge: fge x1 x2 y1 y2", "hgt: fgt z1 z2 u1 u2")
    p.have("disj: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "hge")
    with p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
            .by_cases("disj"):
        with p.case("g_xy: fgt x1 x2 y1 y2"):
            p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_64, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "g_xy", "hgt")
        with p.case("e_xy: feq x1 x2 y1 y2"):
            # x+z ~ y+z (Satz 62B), y+z > y+u (via Satz 61 + Satz 58 norms),
            # transitivity of fgt under feq (Satz 44).
            p.have("eq_xz_yz: feq (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_62B, "x1", "x2", "y1", "y2", "z1", "z2", "e_xy")
            p.have("eq_yz_xz: feq (y1*z2 + z1*y2) (y2*z2) (x1*z2 + z1*x2) (x2*z2)") \
                .by(SATZ_38, "x1*z2 + z1*x2", "x2*z2",
                    "y1*z2 + z1*y2", "y2*z2", "eq_xz_yz")
            # y+z > y+u: use Satz 61 with shape (z, z, u, u, y, y) then Satz 44 to
            # commute summand order to canonical form.
            p.have("gt_zy_uy: fgt (z1*y2 + y1*z2) (z2*y2) (u1*y2 + y1*u2) (u2*y2)") \
                .by(SATZ_61, "z1", "z2", "u1", "u2", "y1", "y2", "hgt")
            p.have("comm_l: feq (z1*y2 + y1*z2) (z2*y2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_58, "z1", "z2", "y1", "y2")
            p.have("comm_r: feq (u1*y2 + y1*u2) (u2*y2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_58, "u1", "u2", "y1", "y2")
            p.have("gt_yz_yu: fgt (y1*z2 + z1*y2) (y2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_44,
                    "z1*y2 + y1*z2", "z2*y2", "u1*y2 + y1*u2", "u2*y2",
                    "y1*z2 + z1*y2", "y2*z2", "y1*u2 + u1*y2", "y2*u2",
                    "gt_zy_uy", "comm_l", "comm_r")
            p.have("id_yu: feq (y1*u2 + u1*y2) (y2*u2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_37, "y1*u2 + u1*y2", "y2*u2")
            p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_44,
                    "y1*z2 + z1*y2", "y2*z2", "y1*u2 + u1*y2", "y2*u2",
                    "x1*z2 + z1*x2", "x2*z2", "y1*u2 + u1*y2", "y2*u2",
                    "gt_yz_yu", "eq_yz_xz", "id_yu")


# Satz 65b: x>y, z>=u ==> x+z > y+u.
@proof
def SATZ_65B(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fgt x1 x2 y1 y2 ==> fge z1 z2 u1 u2 ==> "
           "fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hgt: fgt x1 x2 y1 y2", "hge: fge z1 z2 u1 u2")
    p.have("disj: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
        .by_eq_mp(UNFOLD(FGE_DEF, z1, z2, u1, u2), "hge")
    with p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
            .by_cases("disj"):
        with p.case("g_zu: fgt z1 z2 u1 u2"):
            p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_64, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "hgt", "g_zu")
        with p.case("e_zu: feq z1 z2 u1 u2"):
            # x+z > y+z (Satz 61), then bridge z→u via Satz 62B/Satz 56.
            p.have("gt_xz_yz: fgt (x1*z2 + z1*x2) (x2*z2) (y1*z2 + z1*y2) (y2*z2)") \
                .by(SATZ_61, "x1", "x2", "y1", "y2", "z1", "z2", "hgt")
            # feq y+z ~ y+u via Satz 56 with feq y~y (37) and feq z~u (e_zu).
            p.have("id_y: feq y1 y2 y1 y2").by(SATZ_37, "y1", "y2")
            p.have("eq_yz_yu: feq (y1*z2 + z1*y2) (y2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_56, "y1", "y2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "id_y", "e_zu")
            p.have("id_xz: feq (x1*z2 + z1*x2) (x2*z2) (x1*z2 + z1*x2) (x2*z2)") \
                .by(SATZ_37, "x1*z2 + z1*x2", "x2*z2")
            p.thus("fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_44,
                    "x1*z2 + z1*x2", "x2*z2", "y1*z2 + z1*y2", "y2*z2",
                    "x1*z2 + z1*x2", "x2*z2", "y1*u2 + u1*y2", "y2*u2",
                    "gt_xz_yz", "id_xz", "eq_yz_yu")


# Satz 66:  fge x1 x2 y1 y2 /\ fge z1 z2 u1 u2  ==>  fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2).
@proof
def SATZ_66(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fge x1 x2 y1 y2 ==> fge z1 z2 u1 u2 ==> "
           "fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hxy: fge x1 x2 y1 y2", "hzu: fge z1 z2 u1 u2")
    p.have("d1: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "hxy")
    p.have("d2: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
        .by_eq_mp(UNFOLD(FGE_DEF, z1, z2, u1, u2), "hzu")
    with p.thus("fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
            .by_cases("d1"):
        with p.case("g_xy: fgt x1 x2 y1 y2"):
            p.have("g: fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(SATZ_65B, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "g_xy", "hzu")
            p.have("orL: fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2) "
                   "\\/ feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by(DISJ1, "g",
                    "feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
            p.thus("fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                .by_unfold("orL", FGE_DEF)
        with p.case("e_xy: feq x1 x2 y1 y2"):
            with p.thus("fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                    .by_cases("d2"):
                with p.case("g_zu: fgt z1 z2 u1 u2"):
                    p.have("g: fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by(SATZ_65A, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                            "hxy", "g_zu")
                    p.have("orL: fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2) "
                           "\\/ feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by(DISJ1, "g",
                            "feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)")
                    p.thus("fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by_unfold("orL", FGE_DEF)
                with p.case("e_zu: feq z1 z2 u1 u2"):
                    p.have("e: feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by(SATZ_56, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                            "e_xy", "e_zu")
                    p.have("orR: fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2) "
                           "\\/ feq (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by(DISJ2,
                            "fgt (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)",
                            "e")
                    p.thus("fge (x1*z2 + z1*x2) (x2*z2) (y1*u2 + u1*y2) (y2*u2)") \
                        .by_unfold("orR", FGE_DEF)


# Satz 67: subtraction (existence and uniqueness).
#   fgt x1 x2 y1 y2  ==>  ?u1 u2. feq (y1*u2 + u1*y2) (y2*u2) x1 x2.
# Witness (Landau): u1 = u, u2 = x2*y2, where u is the nat-subtraction with
#   x1*y2 = y1*x2 + u (extracted by unfolding the > on naturals).

@proof
def SATZ_67_EXIST(p):
    p.goal("!x1 x2 y1 y2. fgt x1 x2 y1 y2 ==> "
           "?u1 u2. feq (y1*u2 + u1*y2) (y2*u2) x1 x2")
    p.fix("x1 x2 y1 y2")
    p.assume("h: fgt x1 x2 y1 y2")
    p.have("g: x1*y2 > y1*x2") \
        .by_eq_mp(UNFOLD(FGT_DEF, x1, x2, y1, y2), "h")
    p.choose("u: x1*y2 = y1*x2 + u", from_="g")
    # ``u`` in proof scope is a (@u. ...) select-term; extract it from u_eq.
    u_term = rand(p.fact("u_eq")._concl)             # y1*x2 + u
    u_term = rand(u_term)                              # u
    # Goal at u1 := u, u2 := x2*y2: feq (y1*(x2*y2) + u*y2) (y2*(x2*y2)) x1 x2.
    bridge_R = _mul_AC(mk_mul(x1, mk_mul(y2, mk_mul(x2, y2))),
                       mk_mul(mk_mul(x1, y2), mk_mul(x2, y2)))
    sub_eq = AP_THM(AP_TERM(TIMES, p.fact("u_eq")), mk_mul(x2, y2))
    distr_R = SPECL([mk_mul(y1, x2), u_term, mk_mul(x2, y2)], RIGHT_DISTRIB)
    M1 = _mul_AC(mk_mul(mk_mul(y1, x2), mk_mul(x2, y2)),
                 mk_mul(mk_mul(y1, mk_mul(x2, y2)), x2))
    M2 = _mul_AC(mk_mul(u_term, mk_mul(x2, y2)),
                 mk_mul(mk_mul(u_term, y2), x2))
    bridge_LHS_sum = MK_COMB(AP_TERM(PLUS, M1), M2)
    refold = SPECL([mk_mul(y1, mk_mul(x2, y2)), mk_mul(u_term, y2), x2],
                    RIGHT_DISTRIB)
    # refold: (y1*(x2*y2) + u*y2)*x2 = (y1*(x2*y2))*x2 + (u*y2)*x2.
    res = TRANS_CHAIN([
        refold,                  # F = E
        SYM(bridge_LHS_sum),      # E = D
        SYM(distr_R),             # D = C
        SYM(sub_eq),              # C = B
        SYM(bridge_R)])           # B = A
    p.have("witness_eq: feq (y1*(x2*y2) + u*y2) (y2*(x2*y2)) x1 x2") \
        .by_unfold(res, FEQ_DEF)
    p.have("inner: ?u2. feq (y1*u2 + u*y2) (y2*u2) x1 x2") \
        .by_witness("x2*y2", "witness_eq")
    p.thus("?u1 u2. feq (y1*u2 + u1*y2) (y2*u2) x1 x2") \
        .by_witness("u", "inner")


@proof
def SATZ_67_UNIQUE(p):
    p.goal("!x1 x2 y1 y2 v1 v2 w1 w2. "
           "feq (y1*v2 + v1*y2) (y2*v2) x1 x2 ==> "
           "feq (y1*w2 + w1*y2) (y2*w2) x1 x2 ==> "
           "feq v1 v2 w1 w2")
    p.fix("x1 x2 y1 y2 v1 v2 w1 w2")
    p.assume("hv: feq (y1*v2 + v1*y2) (y2*v2) x1 x2",
             "hw: feq (y1*w2 + w1*y2) (y2*w2) x1 x2")
    # Both sides ~ x1/x2 → both sides ~ each other.
    p.have("hw_sym: feq x1 x2 (y1*w2 + w1*y2) (y2*w2)") \
        .by(SATZ_38, "y1*w2 + w1*y2", "y2*w2", "x1", "x2", "hw")
    p.have("eq_vw: feq (y1*v2 + v1*y2) (y2*v2) (y1*w2 + w1*y2) (y2*w2)") \
        .by(SATZ_39,
            "y1*v2 + v1*y2", "y2*v2", "x1", "x2", "y1*w2 + w1*y2", "y2*w2",
            "hv", "hw_sym")
    # Apply Satz 58 (commutativity) to canonicalize the summand order on both sides.
    p.have("comm_v: feq (y1*v2 + v1*y2) (y2*v2) (v1*y2 + y1*v2) (v2*y2)") \
        .by(SATZ_58, "y1", "y2", "v1", "v2")
    p.have("comm_v_sym: feq (v1*y2 + y1*v2) (v2*y2) (y1*v2 + v1*y2) (y2*v2)") \
        .by(SATZ_38, "y1*v2 + v1*y2", "y2*v2",
            "v1*y2 + y1*v2", "v2*y2", "comm_v")
    p.have("comm_w: feq (y1*w2 + w1*y2) (y2*w2) (w1*y2 + y1*w2) (w2*y2)") \
        .by(SATZ_58, "y1", "y2", "w1", "w2")
    # Chain into canonical form:
    p.have("step_a: feq (v1*y2 + y1*v2) (v2*y2) (y1*w2 + w1*y2) (y2*w2)") \
        .by(SATZ_39,
            "v1*y2 + y1*v2", "v2*y2", "y1*v2 + v1*y2", "y2*v2",
            "y1*w2 + w1*y2", "y2*w2", "comm_v_sym", "eq_vw")
    p.have("step_b: feq (v1*y2 + y1*v2) (v2*y2) (w1*y2 + y1*w2) (w2*y2)") \
        .by(SATZ_39,
            "v1*y2 + y1*v2", "v2*y2", "y1*w2 + w1*y2", "y2*w2",
            "w1*y2 + y1*w2", "w2*y2", "step_a", "comm_w")
    # Cancel y1/y2 via Satz 63B.
    p.thus("feq v1 v2 w1 w2") \
        .by(SATZ_63B, "v1", "v2", "w1", "w2", "y1", "y2", "step_b")


# ---------------------------------------------------------------------------
# §4. Multiplication.
# ---------------------------------------------------------------------------
# Definition 15: x1/x2 * y1/y2 := (x1*y1) / (x2*y2).
# As with addition, the product is represented inline by the pair
# ((x1*y1), (x2*y2)).
# ---------------------------------------------------------------------------


# Satz 68:  feq x1 x2 y1 y2 /\ feq z1 z2 u1 u2  ==>  feq (x1*z1) (x2*z2) (y1*u1) (y2*u2).
@proof
def SATZ_68(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. feq x1 x2 y1 y2 ==> feq z1 z2 u1 u2 "
           "==> feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("h1: feq x1 x2 y1 y2", "h2: feq z1 z2 u1 u2")
    p.have("e1: x1*y2 = y1*x2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, x1, x2, y1, y2), "h1")
    p.have("e2: z1*u2 = u1*z2") \
        .by_eq_mp(UNFOLD(FEQ_DEF, z1, z2, u1, u2), "h2")
    # (x1*y2)*(z1*u2) = (y1*x2)*(u1*z2).
    prod = MK_COMB(AP_TERM(TIMES, p.fact("e1")), p.fact("e2"))
    # AC: (x1*z1)*(y2*u2) = (y1*u1)*(x2*z2).
    eq = TRANS_CHAIN([
        _mul_AC(mk_mul(mk_mul(x1, z1), mk_mul(y2, u2)),
                mk_mul(mk_mul(x1, y2), mk_mul(z1, u2))),
        prod,
        _mul_AC(mk_mul(mk_mul(y1, x2), mk_mul(u1, z2)),
                mk_mul(mk_mul(y1, u1), mk_mul(x2, z2)))])
    p.thus("feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)").by_unfold(eq, FEQ_DEF)


# Satz 69 (commutativity of fraction product):
#   feq (x1*y1) (x2*y2) (y1*x1) (y2*x2).
@proof
def SATZ_69(p):
    p.goal("!x1 x2 y1 y2. feq (x1*y1) (x2*y2) (y1*x1) (y2*x2)")
    p.fix("x1 x2 y1 y2")
    eq = _mul_AC(mk_mul(mk_mul(x1, y1), mk_mul(y2, x2)),
                 mk_mul(mk_mul(y1, x1), mk_mul(x2, y2)))
    p.thus("feq (x1*y1) (x2*y2) (y1*x1) (y2*x2)").by_unfold(eq, FEQ_DEF)


# Satz 70 (associativity of fraction product):
#   feq ((x1*y1)*z1) ((x2*y2)*z2) (x1*(y1*z1)) (x2*(y2*z2)).
@proof
def SATZ_70(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "feq ((x1*y1)*z1) ((x2*y2)*z2) (x1*(y1*z1)) (x2*(y2*z2))")
    p.fix("x1 x2 y1 y2 z1 z2")
    eq = _mul_AC(mk_mul(mk_mul(mk_mul(x1, y1), z1), mk_mul(x2, mk_mul(y2, z2))),
                 mk_mul(mk_mul(x1, mk_mul(y1, z1)), mk_mul(mk_mul(x2, y2), z2)))
    p.thus("feq ((x1*y1)*z1) ((x2*y2)*z2) (x1*(y1*z1)) (x2*(y2*z2))") \
        .by_unfold(eq, FEQ_DEF)


# Satz 71 (distributivity of fraction product over sum):
#   x*(y+z) ~ x*y + x*z, where:
#     x*(y+z)  = (x1*(y1*z2 + z1*y2)) / (x2*(y2*z2))
#     x*y + x*z = ((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2)) / ((x2*y2)*(x2*z2))
#
# Goal unfolds to:
#   (x1*(y1*z2 + z1*y2)) * ((x2*y2)*(x2*z2))
#     = ((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2)) * (x2*(y2*z2)).
@proof
def SATZ_71(p):
    p.goal("!x1 x2 y1 y2 z1 z2. "
           "feq (x1*(y1*z2 + z1*y2)) (x2*(y2*z2)) "
               "((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2)) ((x2*y2)*(x2*z2))")
    p.fix("x1 x2 y1 y2 z1 z2")
    # Distribute LHS via SATZ_30 and RIGHT_DISTRIB:
    # x1*(y1*z2 + z1*y2) = x1*(y1*z2) + x1*(z1*y2)
    # multiply by ((x2*y2)*(x2*z2)) and RIGHT_DISTRIB:
    # (x1*(y1*z2) + x1*(z1*y2)) * F  =  (x1*(y1*z2))*F + (x1*(z1*y2))*F
    F_L = mk_mul(mk_mul(x2, y2), mk_mul(x2, z2))
    inner_L = SPECL([x1, mk_mul(y1, z2), mk_mul(z1, y2)], SATZ_30)
    chunk_L = TRANS(AP_THM(AP_TERM(TIMES, inner_L), F_L),
                    SPECL([mk_mul(x1, mk_mul(y1, z2)),
                           mk_mul(x1, mk_mul(z1, y2)),
                           F_L], RIGHT_DISTRIB))
    # |- (x1*(y1*z2 + z1*y2))*F = (x1*(y1*z2))*F + (x1*(z1*y2))*F
    # Distribute RHS: ((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2)) * G  =  ...
    G_R = mk_mul(x2, mk_mul(y2, z2))
    chunk_R = SPECL([mk_mul(mk_mul(x1, y1), mk_mul(x2, z2)),
                     mk_mul(mk_mul(x1, z1), mk_mul(x2, y2)),
                     G_R], RIGHT_DISTRIB)
    # |- ((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2))*G = ((x1*y1)*(x2*z2))*G + ((x1*z1)*(x2*y2))*G
    # Bridge each pair via *-AC:
    M1L = mk_mul(mk_mul(x1, mk_mul(y1, z2)), F_L)
    M1R = mk_mul(mk_mul(mk_mul(x1, y1), mk_mul(x2, z2)), G_R)
    M2L = mk_mul(mk_mul(x1, mk_mul(z1, y2)), F_L)
    M2R = mk_mul(mk_mul(mk_mul(x1, z1), mk_mul(x2, y2)), G_R)
    eq_M1 = _mul_AC(M1L, M1R)
    eq_M2 = _mul_AC(M2L, M2R)
    bridge = MK_COMB(AP_TERM(PLUS, eq_M1), eq_M2)
    res = TRANS_CHAIN([chunk_L, bridge, SYM(chunk_R)])
    p.thus("feq (x1*(y1*z2 + z1*y2)) (x2*(y2*z2)) "
           "((x1*y1)*(x2*z2) + (x1*z1)*(x2*y2)) ((x2*y2)*(x2*z2))") \
        .by_unfold(res, FEQ_DEF)


# Satz 72a/b/c -- "respectively" forms of: x R y => x*z R y*z, R in {>, =, <}.
@proof
def SATZ_72A(p):
    p.goal("!x1 x2 y1 y2 z1 z2. fgt x1 x2 y1 y2 ==> fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: fgt x1 x2 y1 y2")
    p.have("g0: x1*y2 > y1*x2") \
        .by_eq_mp(UNFOLD(FGT_DEF, x1, x2, y1, y2), "h")
    p.have("g1: (x1*y2)*(z1*z2) > (y1*x2)*(z1*z2)") \
        .by(SATZ_32A, "x1*y2", "y1*x2", "z1*z2", "g0")
    # AC: (x1*y2)*(z1*z2) = (x1*z1)*(y2*z2);  (y1*x2)*(z1*z2) = (y1*z1)*(x2*z2).
    ac_l = _mul_AC(mk_mul(mk_mul(x1, y2), mk_mul(z1, z2)),
                   mk_mul(mk_mul(x1, z1), mk_mul(y2, z2)))
    ac_r = _mul_AC(mk_mul(mk_mul(y1, x2), mk_mul(z1, z2)),
                   mk_mul(mk_mul(y1, z1), mk_mul(x2, z2)))
    p.have("g2: (x1*z1)*(y2*z2) > (y1*z1)*(x2*z2)") \
        .by_rewrite_of("g1", [ac_l, ac_r])
    p.thus("fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)").by_unfold("g2", FGT_DEF)


@proof
def SATZ_72B(p):
    p.goal("!x1 x2 y1 y2 z1 z2. feq x1 x2 y1 y2 ==> feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: feq x1 x2 y1 y2")
    p.have("id_z: feq z1 z2 z1 z2").by(SATZ_37, "z1", "z2")
    p.thus("feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
        .by(SATZ_68, "x1", "x2", "y1", "y2", "z1", "z2", "z1", "z2",
            "h", "id_z")


@proof
def SATZ_72C(p):
    p.goal("!x1 x2 y1 y2 z1 z2. flt x1 x2 y1 y2 ==> flt (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: flt x1 x2 y1 y2")
    p.have("yx_gt: fgt y1 y2 x1 x2").by(SATZ_43, "x1", "x2", "y1", "y2", "h")
    p.have("yz_gt: fgt (y1*z1) (y2*z2) (x1*z1) (x2*z2)") \
        .by(SATZ_72A, "y1", "y2", "x1", "x2", "z1", "z2", "yx_gt")
    p.thus("flt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
        .by(SATZ_42, "y1*z1", "y2*z2", "x1*z1", "x2*z2", "yz_gt")


# Satz 73a/b/c -- cancellation in fraction product (mirror of Satz 63).
@proof
def SATZ_73A(p):
    p.goal("!x1 x2 y1 y2 z1 z2. fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2) "
           "==> fgt x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.have("eq_p: feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72B, "x1", "x2", "y1", "y2", "z1", "z2", "h_eq")
            p.have("h_n: (x1*z1)*(y2*z2) > (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "h")
            p.have("eq_n: (x1*z1)*(y2*z2) = (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "eq_p")
            p.absurd().auto("h_n", "eq_n")
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.thus("fgt x1 x2 y1 y2").by_thm(p.fact("h_gt"))
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.have("lt_p: flt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72C, "x1", "x2", "y1", "y2", "z1", "z2", "h_lt")
            p.have("h_n: (x1*z1)*(y2*z2) > (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "h")
            p.have("lt_n: (x1*z1)*(y2*z2) < (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FLT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "lt_p")
            p.absurd().auto("lt_n", "h_n")


@proof
def SATZ_73B(p):
    p.goal("!x1 x2 y1 y2 z1 z2. feq (x1*z1) (x2*z2) (y1*z1) (y2*z2) "
           "==> feq x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.thus("feq x1 x2 y1 y2").by_thm(p.fact("h_eq"))
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.have("gt_p: fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72A, "x1", "x2", "y1", "y2", "z1", "z2", "h_gt")
            p.have("gt_n: (x1*z1)*(y2*z2) > (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "gt_p")
            p.have("h_n: (x1*z1)*(y2*z2) = (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "h")
            p.absurd().auto("gt_n", "h_n")
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.have("lt_p: flt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72C, "x1", "x2", "y1", "y2", "z1", "z2", "h_lt")
            p.have("lt_n: (x1*z1)*(y2*z2) < (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FLT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "lt_p")
            p.have("h_n: (x1*z1)*(y2*z2) = (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "h")
            p.absurd().auto("lt_n", "h_n")


@proof
def SATZ_73C(p):
    p.goal("!x1 x2 y1 y2 z1 z2. flt (x1*z1) (x2*z2) (y1*z1) (y2*z2) "
           "==> flt x1 x2 y1 y2")
    p.fix("x1 x2 y1 y2 z1 z2")
    p.assume("h: flt (x1*z1) (x2*z2) (y1*z1) (y2*z2)")
    p.have("h_n: (x1*z1)*(y2*z2) < (y1*z1)*(x2*z2)") \
        .by_eq_mp(UNFOLD(FLT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                          mk_mul(y1, z1), mk_mul(y2, z2)), "h")
    with p.cases_on(SATZ_41, "x1", "x2", "y1", "y2"):
        with p.case("h_eq: feq x1 x2 y1 y2"):
            p.have("eq_p: feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72B, "x1", "x2", "y1", "y2", "z1", "z2", "h_eq")
            p.have("eq_n: (x1*z1)*(y2*z2) = (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FEQ_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "eq_p")
            p.absurd().auto("h_n", "eq_n")
        with p.case("h_gt: fgt x1 x2 y1 y2"):
            p.have("gt_p: fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72A, "x1", "x2", "y1", "y2", "z1", "z2", "h_gt")
            p.have("gt_n: (x1*z1)*(y2*z2) > (y1*z1)*(x2*z2)") \
                .by_eq_mp(UNFOLD(FGT_DEF, mk_mul(x1, z1), mk_mul(x2, z2),
                                  mk_mul(y1, z1), mk_mul(y2, z2)), "gt_p")
            p.absurd().auto("h_n", "gt_n")
        with p.case("h_lt: flt x1 x2 y1 y2"):
            p.thus("flt x1 x2 y1 y2").by_thm(p.fact("h_lt"))


# Satz 74:  fgt x1 x2 y1 y2 /\ fgt z1 z2 u1 u2 ==>
#           fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2).
# Same template as Satz 64 (replace + with *, Satz 61 with Satz 72A, Satz 58 with 69, etc).
@proof
def SATZ_74(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fgt x1 x2 y1 y2 ==> fgt z1 z2 u1 u2 ==> "
           "fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("h_xy: fgt x1 x2 y1 y2", "h_zu: fgt z1 z2 u1 u2")
    p.have("step1: fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
        .by(SATZ_72A, "x1", "x2", "y1", "y2", "z1", "z2", "h_xy")
    # step2: fgt (z1*y1) (z2*y2) (u1*y1) (u2*y2).
    p.have("step2: fgt (z1*y1) (z2*y2) (u1*y1) (u2*y2)") \
        .by(SATZ_72A, "z1", "z2", "u1", "u2", "y1", "y2", "h_zu")
    # Bridges via Satz 69 commutativity.
    p.have("comm_l: feq (z1*y1) (z2*y2) (y1*z1) (y2*z2)").by(SATZ_69, "z1", "z2", "y1", "y2")
    p.have("comm_r: feq (u1*y1) (u2*y2) (y1*u1) (y2*u2)").by(SATZ_69, "u1", "u2", "y1", "y2")
    p.have("step3: fgt (y1*z1) (y2*z2) (y1*u1) (y2*u2)") \
        .by(SATZ_44,
            "z1*y1", "z2*y2", "u1*y1", "u2*y2",
            "y1*z1", "y2*z2", "y1*u1", "y2*u2",
            "step2", "comm_l", "comm_r")
    # Transitivity of fgt: chain step1 (xz>yz) and step3 (yz>yu) → xz > yu.
    # Use SATZ_50 after flipping with SATZ_42, then flip back.
    p.have("lt3: flt (y1*u1) (y2*u2) (y1*z1) (y2*z2)") \
        .by(SATZ_42, "y1*z1", "y2*z2", "y1*u1", "y2*u2", "step3")
    p.have("lt1: flt (y1*z1) (y2*z2) (x1*z1) (x2*z2)") \
        .by(SATZ_42, "x1*z1", "x2*z2", "y1*z1", "y2*z2", "step1")
    p.have("lt_chain: flt (y1*u1) (y2*u2) (x1*z1) (x2*z2)") \
        .by(SATZ_50, "y1*u1", "y2*u2", "y1*z1", "y2*z2",
            "x1*z1", "x2*z2", "lt3", "lt1")
    p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
        .by(SATZ_43, "y1*u1", "y2*u2", "x1*z1", "x2*z2", "lt_chain")


# Satz 75 a/b: x>=y, z>u (or x>y, z>=u) ==> x*z > y*u.   Mirror of Satz 65.
@proof
def SATZ_75A(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fge x1 x2 y1 y2 ==> fgt z1 z2 u1 u2 ==> "
           "fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hge: fge x1 x2 y1 y2", "hgt: fgt z1 z2 u1 u2")
    p.have("disj: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "hge")
    with p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)").by_cases("disj"):
        with p.case("g_xy: fgt x1 x2 y1 y2"):
            p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_74, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "g_xy", "hgt")
        with p.case("e_xy: feq x1 x2 y1 y2"):
            # x*z ~ y*z (Satz 72B) and y*z > y*u (Satz 72A on hgt + Satz 69 commute), then transit.
            p.have("eq_xz_yz: feq (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72B, "x1", "x2", "y1", "y2", "z1", "z2", "e_xy")
            p.have("eq_yz_xz: feq (y1*z1) (y2*z2) (x1*z1) (x2*z2)") \
                .by(SATZ_38, "x1*z1", "x2*z2", "y1*z1", "y2*z2", "eq_xz_yz")
            p.have("gt_zy_uy: fgt (z1*y1) (z2*y2) (u1*y1) (u2*y2)") \
                .by(SATZ_72A, "z1", "z2", "u1", "u2", "y1", "y2", "hgt")
            p.have("comm_l: feq (z1*y1) (z2*y2) (y1*z1) (y2*z2)") \
                .by(SATZ_69, "z1", "z2", "y1", "y2")
            p.have("comm_r: feq (u1*y1) (u2*y2) (y1*u1) (y2*u2)") \
                .by(SATZ_69, "u1", "u2", "y1", "y2")
            p.have("gt_yz_yu: fgt (y1*z1) (y2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_44,
                    "z1*y1", "z2*y2", "u1*y1", "u2*y2",
                    "y1*z1", "y2*z2", "y1*u1", "y2*u2",
                    "gt_zy_uy", "comm_l", "comm_r")
            p.have("id_yu: feq (y1*u1) (y2*u2) (y1*u1) (y2*u2)") \
                .by(SATZ_37, "y1*u1", "y2*u2")
            p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_44,
                    "y1*z1", "y2*z2", "y1*u1", "y2*u2",
                    "x1*z1", "x2*z2", "y1*u1", "y2*u2",
                    "gt_yz_yu", "eq_yz_xz", "id_yu")


@proof
def SATZ_75B(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fgt x1 x2 y1 y2 ==> fge z1 z2 u1 u2 ==> "
           "fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hgt: fgt x1 x2 y1 y2", "hge: fge z1 z2 u1 u2")
    p.have("disj: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
        .by_eq_mp(UNFOLD(FGE_DEF, z1, z2, u1, u2), "hge")
    with p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)").by_cases("disj"):
        with p.case("g_zu: fgt z1 z2 u1 u2"):
            p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_74, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "hgt", "g_zu")
        with p.case("e_zu: feq z1 z2 u1 u2"):
            p.have("gt_xz_yz: fgt (x1*z1) (x2*z2) (y1*z1) (y2*z2)") \
                .by(SATZ_72A, "x1", "x2", "y1", "y2", "z1", "z2", "hgt")
            p.have("id_y: feq y1 y2 y1 y2").by(SATZ_37, "y1", "y2")
            p.have("eq_yz_yu: feq (y1*z1) (y2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_68, "y1", "y2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "id_y", "e_zu")
            p.have("id_xz: feq (x1*z1) (x2*z2) (x1*z1) (x2*z2)") \
                .by(SATZ_37, "x1*z1", "x2*z2")
            p.thus("fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_44,
                    "x1*z1", "x2*z2", "y1*z1", "y2*z2",
                    "x1*z1", "x2*z2", "y1*u1", "y2*u2",
                    "gt_xz_yz", "id_xz", "eq_yz_yu")


# Satz 76: fge x1 x2 y1 y2, fge z1 z2 u1 u2 ==> fge (x1*z1) (x2*z2) (y1*u1) (y2*u2).
@proof
def SATZ_76(p):
    p.goal("!x1 x2 y1 y2 z1 z2 u1 u2. fge x1 x2 y1 y2 ==> fge z1 z2 u1 u2 ==> "
           "fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
    p.fix("x1 x2 y1 y2 z1 z2 u1 u2")
    p.assume("hxy: fge x1 x2 y1 y2", "hzu: fge z1 z2 u1 u2")
    p.have("d1: fgt x1 x2 y1 y2 \\/ feq x1 x2 y1 y2") \
        .by_eq_mp(UNFOLD(FGE_DEF, x1, x2, y1, y2), "hxy")
    p.have("d2: fgt z1 z2 u1 u2 \\/ feq z1 z2 u1 u2") \
        .by_eq_mp(UNFOLD(FGE_DEF, z1, z2, u1, u2), "hzu")
    with p.thus("fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)").by_cases("d1"):
        with p.case("g_xy: fgt x1 x2 y1 y2"):
            p.have("g: fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(SATZ_75B, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                    "g_xy", "hzu")
            p.have("orL: fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2) \\/ "
                   "feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by(DISJ1, "g", "feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
            p.thus("fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                .by_unfold("orL", FGE_DEF)
        with p.case("e_xy: feq x1 x2 y1 y2"):
            with p.thus("fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)").by_cases("d2"):
                with p.case("g_zu: fgt z1 z2 u1 u2"):
                    p.have("g: fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by(SATZ_75A, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                            "hxy", "g_zu")
                    p.have("orL: fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2) \\/ "
                           "feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by(DISJ1, "g",
                            "feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)")
                    p.thus("fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by_unfold("orL", FGE_DEF)
                with p.case("e_zu: feq z1 z2 u1 u2"):
                    p.have("e: feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by(SATZ_68, "x1", "x2", "y1", "y2", "z1", "z2", "u1", "u2",
                            "e_xy", "e_zu")
                    p.have("orR: fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2) \\/ "
                           "feq (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by(DISJ2,
                            "fgt (x1*z1) (x2*z2) (y1*u1) (y2*u2)", "e")
                    p.thus("fge (x1*z1) (x2*z2) (y1*u1) (y2*u2)") \
                        .by_unfold("orR", FGE_DEF)


# Satz 77 (existence and uniqueness of fraction division): for fixed x, y, the
# equivalence (y1*u1)/(y2*u2) ~ x1/x2 has a solution u, and any two solutions
# are equivalent. The witness from Landau is u = (x1*y2)/(x2*y1).
#
# Existence:  feq (y1*(x1*y2)) (y2*(x2*y1)) x1 x2.
# Uniqueness: feq (y1*v1) (y2*v2) x1 x2 /\ feq (y1*w1) (y2*w2) x1 x2
#              ==> feq v1 v2 w1 w2.   (Comes from Satz 73B.)

@proof
def SATZ_77_EXIST(p):
    """Existence half of Satz 77 -- the explicit Landau witness."""
    p.goal("!x1 x2 y1 y2. feq (y1*(x1*y2)) (y2*(x2*y1)) x1 x2")
    p.fix("x1 x2 y1 y2")
    # Goal unfolds to (y1*(x1*y2)) * x2 = x1 * (y2*(x2*y1)).
    eq = _mul_AC(mk_mul(mk_mul(y1, mk_mul(x1, y2)), x2),
                 mk_mul(x1, mk_mul(y2, mk_mul(x2, y1))))
    p.thus("feq (y1*(x1*y2)) (y2*(x2*y1)) x1 x2").by_unfold(eq, FEQ_DEF)


@proof
def SATZ_77_UNIQUE(p):
    """Uniqueness half of Satz 77 -- two solutions are equivalent."""
    p.goal("!x1 x2 y1 y2 v1 v2 w1 w2. "
           "feq (y1*v1) (y2*v2) x1 x2 ==> feq (y1*w1) (y2*w2) x1 x2 ==> "
           "feq v1 v2 w1 w2")
    p.fix("x1 x2 y1 y2 v1 v2 w1 w2")
    p.assume("hv: feq (y1*v1) (y2*v2) x1 x2",
             "hw: feq (y1*w1) (y2*w2) x1 x2")
    # By transitivity of feq through x1/x2: (y1*v1)/(y2*v2) ~ (y1*w1)/(y2*w2).
    p.have("hw_sym: feq x1 x2 (y1*w1) (y2*w2)") \
        .by(SATZ_38, "y1*w1", "y2*w2", "x1", "x2", "hw")
    p.have("eq_yvw: feq (y1*v1) (y2*v2) (y1*w1) (y2*w2)") \
        .by(SATZ_39, "y1*v1", "y2*v2", "x1", "x2", "y1*w1", "y2*w2",
            "hv", "hw_sym")
    # Cancel the y1, y2 factor via Satz 73B (after Satz 69 commute to x*z form).
    p.have("comm_v: feq (y1*v1) (y2*v2) (v1*y1) (v2*y2)") \
        .by(SATZ_69, "y1", "y2", "v1", "v2")
    p.have("comm_w: feq (y1*w1) (y2*w2) (w1*y1) (w2*y2)") \
        .by(SATZ_69, "y1", "y2", "w1", "w2")
    p.have("comm_v_sym: feq (v1*y1) (v2*y2) (y1*v1) (y2*v2)") \
        .by(SATZ_38, "y1*v1", "y2*v2", "v1*y1", "v2*y2", "comm_v")
    # Transitive chain to bring v and w under the canonical x*z form.
    #   comm_v_sym : feq (v1*y1) (v2*y2) (y1*v1) (y2*v2)
    #   eq_yvw     : feq (y1*v1) (y2*v2) (y1*w1) (y2*w2)
    #   comm_w     : feq (y1*w1) (y2*w2) (w1*y1) (w2*y2)
    p.have("step_a: feq (v1*y1) (v2*y2) (y1*w1) (y2*w2)") \
        .by(SATZ_39, "v1*y1", "v2*y2", "y1*v1", "y2*v2", "y1*w1", "y2*w2",
            "comm_v_sym", "eq_yvw")
    p.have("step_b: feq (v1*y1) (v2*y2) (w1*y1) (w2*y2)") \
        .by(SATZ_39, "v1*y1", "v2*y2", "y1*w1", "y2*w2", "w1*y1", "w2*y2",
            "step_a", "comm_w")
    p.thus("feq v1 v2 w1 w2") \
        .by(SATZ_73B, "v1", "v2", "w1", "w2", "y1", "y2", "step_b")


if __name__ == "__main__":
    print("§1 OK -- Definition 8 + Sätze 37, 38, 39, 40 proved.")
    print("  SATZ_37:", pp_thm(SATZ_37))
    print("  SATZ_38:", pp_thm(SATZ_38))
    print("  SATZ_39:", pp_thm(SATZ_39))
    print("  SATZ_40:", pp_thm(SATZ_40))
    print("§2 OK -- Definitions 9-12 + Sätze 41-55 proved.")
    print("  SATZ_41:", pp_thm(SATZ_41))
    print("  SATZ_42:", pp_thm(SATZ_42))
    print("  SATZ_43:", pp_thm(SATZ_43))
    print("  SATZ_44:", pp_thm(SATZ_44))
    print("  SATZ_45:", pp_thm(SATZ_45))
    print("  SATZ_46:", pp_thm(SATZ_46))
    print("  SATZ_47:", pp_thm(SATZ_47))
    print("  SATZ_48:", pp_thm(SATZ_48))
    print("  SATZ_49:", pp_thm(SATZ_49))
    print("  SATZ_50:", pp_thm(SATZ_50))
    print("  SATZ_51A:", pp_thm(SATZ_51A))
    print("  SATZ_51B:", pp_thm(SATZ_51B))
    print("  SATZ_52:", pp_thm(SATZ_52))
    print("  SATZ_53:", pp_thm(SATZ_53))
    print("  SATZ_54:", pp_thm(SATZ_54))
    print("  SATZ_55:", pp_thm(SATZ_55))
    print("§3 progressing -- Definition 13 + Sätze 56-66 (60-66 added).")
    print("  SATZ_56:", pp_thm(SATZ_56))
    print("  SATZ_57:", pp_thm(SATZ_57))
    print("  SATZ_58:", pp_thm(SATZ_58))
    print("  SATZ_59:", pp_thm(SATZ_59))
    print("  SATZ_60:", pp_thm(SATZ_60))
    print("  SATZ_61:", pp_thm(SATZ_61))
    print("  SATZ_62A:", pp_thm(SATZ_62A))
    print("  SATZ_62B:", pp_thm(SATZ_62B))
    print("  SATZ_62C:", pp_thm(SATZ_62C))
    print("  SATZ_63A:", pp_thm(SATZ_63A))
    print("  SATZ_63B:", pp_thm(SATZ_63B))
    print("  SATZ_63C:", pp_thm(SATZ_63C))
    print("  SATZ_64:", pp_thm(SATZ_64))
    print("  SATZ_65A:", pp_thm(SATZ_65A))
    print("  SATZ_65B:", pp_thm(SATZ_65B))
    print("  SATZ_66:", pp_thm(SATZ_66))
    print("  SATZ_67_EXIST:", pp_thm(SATZ_67_EXIST))
    print("  SATZ_67_UNIQUE:", pp_thm(SATZ_67_UNIQUE))
    print("§4 OK -- Definition 15 + Sätze 68-77 proved.")
    print("  SATZ_68:", pp_thm(SATZ_68))
    print("  SATZ_69:", pp_thm(SATZ_69))
    print("  SATZ_70:", pp_thm(SATZ_70))
    print("  SATZ_71:", pp_thm(SATZ_71))
    print("  SATZ_72A:", pp_thm(SATZ_72A))
    print("  SATZ_72B:", pp_thm(SATZ_72B))
    print("  SATZ_72C:", pp_thm(SATZ_72C))
    print("  SATZ_73A:", pp_thm(SATZ_73A))
    print("  SATZ_73B:", pp_thm(SATZ_73B))
    print("  SATZ_73C:", pp_thm(SATZ_73C))
    print("  SATZ_74:", pp_thm(SATZ_74))
    print("  SATZ_75A:", pp_thm(SATZ_75A))
    print("  SATZ_75B:", pp_thm(SATZ_75B))
    print("  SATZ_76:", pp_thm(SATZ_76))
    print("  SATZ_77_EXIST:", pp_thm(SATZ_77_EXIST))
    print("  SATZ_77_UNIQUE:", pp_thm(SATZ_77_UNIQUE))
