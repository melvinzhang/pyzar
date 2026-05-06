"""Formalisation of Landau's *Foundations of Analysis*, Chapter 2 §5.

Rational numbers (Definition 16) and integers (Definition 25).

A rational number `X` is the equivalence class of all fractions equivalent to
some fixed fraction.  Carrying that class as a quotient type `rat`:

  IS_RAT K  :=  ?a b. K = feq a b               -- "K is some class".
  rat       := { K : num -> num -> bool | IS_RAT K }
  Q a b     := mk_rat (feq a b)                 -- quotient injection.

The central lemma (`RAT_EQ`) is

  Q a b = Q c d   <=>   feq a b c d.

Once this is in hand, every Satz of §5 is a routine lift of the corresponding
fraction-level Satz from `frac.py`.

  Definition 17 (=)   built-in `=` on rat
  Definition 18-19    rgt / rlt
  Definition 20-21    rge / rle
  Definition 22       radd
  Definition 23       rsub
  Definition 24       rmul
  Definition 25       IS_INT_RAT (integer-rational predicate)
  Definition 27       rdiv

Two parts of §5 are deliberately not formalised:

  Definition 26       Reuses the symbol ``x`` for both the natural number and
                      its image ``Q x 1`` as a rational.  Pure surface syntax
                      (Landau "throws away the naturals" and re-binds the
                      lowercase letters); the maths is already covered by
                      Sätze 111-112, so there is nothing to prove.  We keep
                      the natural and rational layers as distinct types and
                      write ``Q x 1`` explicitly throughout.

  Satz 113, clause 5  Peano induction for the integer-rational subset.  The
                      statement is "every set ``M`` of integer rationals
                      containing ``Q 1 1`` and closed under successor
                      contains every integer rational" -- it quantifies over
                      sets of rationals.  We have no set type, so this clause
                      cannot be stated as written.  Clauses 1-4 (existence,
                      successor, ``SUC x ≠ 1``, successor injectivity) are
                      proved as ``SATZ_113_3`` / ``SATZ_113_4`` plus the
                      trivial existence/successor facts.
"""

from fusion import (
    Var,
    REFL,
    TRANS,
    EQ_MP,
    INST,
    mk_comb,
    mk_type,
    new_basic_type_definition,
)
from basics import (
    mk_app,
    mk_const,
    rand,
)
from tactics import (
    AP_TERM,
    AP_THM,
    SYM,
    SPECL,
    GEN,
    CONJ,
    DISJ1,
    DISJ2,
    UNFOLD,
    REWRITE_RULE,
)
from num import ONE
from nat import (
    mk_mul,
    TIMES,
    SATZ_29,
    MUL_1,
    ONE_MUL,
    GE_DEF,
    AXIOM_3,
    AXIOM_4,
    SATZ_24,
)
from frac import (
    FEQ,
    FEQ_DEF,
    FGT_DEF,
    FLT_DEF,
    SATZ_37,
    SATZ_38,
    SATZ_39,
    SATZ_41,
    SATZ_42,
    SATZ_43,
    SATZ_44,
    SATZ_45,
    SATZ_50,
    SATZ_53,
    SATZ_54,
    SATZ_55,
    SATZ_56,
    SATZ_58,
    SATZ_59,
    SATZ_60,
    SATZ_61,
    SATZ_63A,
    SATZ_63B,
    SATZ_67_EXIST,
    SATZ_68,
    SATZ_69,
    SATZ_70,
    SATZ_71,
    SATZ_72A,
    SATZ_73A,
    SATZ_73B,
    SATZ_77_EXIST,
)
from parser import (
    define,
    parse_type,
    pp_thm,
    add_const,
    add_type,
)
from proof import proof, register_unfolder, register_disj_unfolder, register_refl_prover


# ---------------------------------------------------------------------------
# Step 1.  IS_RAT predicate.
# ---------------------------------------------------------------------------
# K : num -> num -> bool is a "rational class" if K = feq a b for some a, b.

n2b_ty = parse_type("num -> num -> bool")

IS_RAT_DEF = define(
    "IS_RAT", "(num -> num -> bool) -> bool", "\\K:Knnb. ?a b. K = feq a b", Knnb=n2b_ty
)
IS_RAT = mk_const("IS_RAT", [])


# ---------------------------------------------------------------------------
# Step 2.  Witness:  |- IS_RAT (feq 1 1).
# ---------------------------------------------------------------------------

K_var = Var("K", n2b_ty)

feq_1_1 = mk_app(FEQ, ONE, ONE)


@proof
def IS_RAT_FEQ_1_1(p):
    p.goal("IS_RAT (feq 1 1)")
    p.have("ex: ?pa pb. feq 1 1 = feq pa pb").by_exists(["1", "1"])
    p.thus("IS_RAT (feq 1 1)").by_unfold("ex", IS_RAT_DEF)


# ---------------------------------------------------------------------------
# Step 3.  Carve out `rat` as a subtype of (num -> num -> bool).
# ---------------------------------------------------------------------------

MK_RAT_DEST, RAT_DEST_MK = new_basic_type_definition(
    "rat", ("mk_rat", "dest_rat"), IS_RAT_FEQ_1_1
)
# MK_RAT_DEST : |- mk_rat (dest_rat r) = r           (r : rat)
# RAT_DEST_MK : |- IS_RAT K = (dest_rat (mk_rat K) = K)

rat_ty = mk_type("rat", [])
mk_rat = mk_const("mk_rat", [])
dest_rat = mk_const("dest_rat", [])

add_type("rat", rat_ty)
add_const("mk_rat", mk_rat)
add_const("dest_rat", dest_rat)


# ---------------------------------------------------------------------------
# Step 4.  Define the quotient injection Q : num -> num -> rat.
# ---------------------------------------------------------------------------
# Q a b := mk_rat (feq a b).

Q_DEF = define("Q", "num -> num -> rat", "\\a b. mk_rat (feq a b)")
Q = mk_const("Q", [])


def mk_Q(a, b):
    return mk_app(Q, a, b)


# Standard variable names for rationals.
X = Var("X", rat_ty)
Y = Var("Y", rat_ty)
Z = Var("Z", rat_ty)
U = Var("U", rat_ty)
V = Var("V", rat_ty)
W = Var("W", rat_ty)


# ---------------------------------------------------------------------------
# Step 5.  Lemma:  |- IS_RAT (feq a b)  -- every "feq a b" is a class.
# ---------------------------------------------------------------------------


@proof
def IS_RAT_FEQ(p):
    p.goal("!a b. IS_RAT (feq a b)")
    p.fix("a b")
    p.have("ex: ?pa pb. feq a b = feq pa pb").by_exists(["a", "b"])
    p.thus("IS_RAT (feq a b)").by_unfold("ex", IS_RAT_DEF)


# ---------------------------------------------------------------------------
# Step 6.  Round-trip:  |- !a b. dest_rat (mk_rat (feq a b)) = feq a b
#                        =  !a b. dest_rat (Q a b) = feq a b.
# ---------------------------------------------------------------------------

_r_n2b = Var("r", n2b_ty)


@proof
def DEST_RAT_FEQ(p):
    p.goal("!a b. dest_rat (mk_rat (feq a b)) = feq a b")
    p.fix("a b")
    p.have("isr: IS_RAT (feq a b)").by_match(IS_RAT_FEQ)
    feq_ab = mk_app(FEQ, p._parse("a"), p._parse("b"))
    # RAT_DEST_MK : |- IS_RAT r = (dest_rat (mk_rat r) = r)  with r : num->num->bool
    r_inst = INST([(feq_ab, _r_n2b)], RAT_DEST_MK)
    p.thus("dest_rat (mk_rat (feq a b)) = feq a b").by_eq_mp(r_inst, "isr")


# ---------------------------------------------------------------------------
# Step 7.  Central lemma --
#   |- !a b c d. (Q a b = Q c d) = feq a b c d.
#
# Forward (==>):  apply dest_rat to both sides, peel via DEST_RAT_FEQ to get
#                 feq a b = feq c d as functions; specialise at (c, d) and use
#                 SATZ_37 (feq c d c d) to get feq a b c d.
# Reverse (<==):  given feq a b c d, build !p q. feq a b p q = feq c d p q
#                 (each direction by SATZ_38/39), apply FUN_EXT twice to get
#                 feq a b = feq c d, AP_TERM mk_rat to get Q a b = Q c d.
# ---------------------------------------------------------------------------


@proof
def RAT_EQ(p):
    p.goal("!a b c d. (Q a b = Q c d) = feq a b c d")
    p.fix("a b c d")
    a_t = p._parse("a")
    b_t = p._parse("b")
    c_t = p._parse("c")
    d_t = p._parse("d")
    mk_app(FEQ, a_t, b_t)
    mk_app(FEQ, c_t, d_t)
    mk_app(Q, a_t, b_t)
    mk_app(Q, c_t, d_t)

    # Q a b = mk_rat (feq a b)  via Q_DEF unfolded twice.
    Q_unfold_ab = p.unfold(Q_DEF, "a", "b")  # |- Q a b = mk_rat (feq a b)
    Q_unfold_cd = p.unfold(Q_DEF, "c", "d")  # |- Q c d = mk_rat (feq c d)

    # Forward direction.
    with p.have("fwd: Q a b = Q c d ==> feq a b c d").proof():
        p.assume("hQ: Q a b = Q c d")
        with p.calc("h_mk: mk_rat (feq a b)") as c:
            c.step("= Q a b").by_thm(SYM(Q_unfold_ab))
            c.step("= Q c d").by_thm(p.fact("hQ"))
            c.step("= mk_rat (feq c d)").by_thm(Q_unfold_cd)
        with p.calc("feq_eq: feq a b") as c:
            c.step("= dest_rat (mk_rat (feq a b))").by_thm(
                SYM(SPECL([a_t, b_t], DEST_RAT_FEQ))
            )
            c.step("= dest_rat (mk_rat (feq c d))").by_cong(dest_rat, "h_mk")
            c.step("= feq c d").by_inst(DEST_RAT_FEQ, "c", "d")
        # Apply at (c, d): feq a b c d = feq c d c d.
        feq_at_cd = AP_THM(AP_THM(p.fact("feq_eq"), c_t), d_t)
        p.have("rcd: feq c d c d").by_inst(SATZ_37, "c", "d")
        p.thus("feq a b c d").by_eq_mp(SYM(feq_at_cd), "rcd")

    # Reverse direction.
    with p.have("rev: feq a b c d ==> Q a b = Q c d").proof():
        p.assume("hf: feq a b c d")
        # Build !p q. feq a b p q = feq c d p q.
        # For each p, q: prove the bool equality via two MPs.
        with p.have("ptw: !p q. feq a b p q = feq c d p q").proof():
            p.fix("p q")
            # ==>: feq a b p q ==> feq c d p q via SATZ_38 + SATZ_39.
            with p.have("imp1: feq a b p q ==> feq c d p q").proof():
                p.assume("hap: feq a b p q")
                p.have("hcd_ab: feq c d a b").by_match(SATZ_38, "hf")
                p.thus("feq c d p q").by_match(SATZ_39, "hcd_ab", "hap")
            # <==: feq c d p q ==> feq a b p q.
            with p.have("imp2: feq c d p q ==> feq a b p q").proof():
                p.assume("hcp: feq c d p q")
                p.thus("feq a b p q").by_match(SATZ_39, "hf", "hcp")
            p.thus("feq a b p q = feq c d p q").by_iff("imp1", "imp2")
        p.have("feq_eq: feq a b = feq c d").by_ext("ptw")
        p.have("mk_eq: mk_rat (feq a b) = mk_rat (feq c d)").by_cong(mk_rat, "feq_eq")
        with p.calc("Q a b", thus=True) as c:
            c.step("= mk_rat (feq a b)").by_thm(Q_unfold_ab)
            c.step("= mk_rat (feq c d)").by_thm("mk_eq")
            c.step("= Q c d").by_thm(SYM(Q_unfold_cd))

    p.thus("(Q a b = Q c d) = feq a b c d").by_iff("fwd", "rev")


# A frequent shorthand: from (Q a b = Q c d) extract feq a b c d, and v.v.
def Q_eq_to_feq(th):
    """|- Q a b = Q c d  ==>  |- feq a b c d."""
    from basics import dest_eq

    Q_ab, Q_cd = dest_eq(th._concl)
    a_t = Q_ab.fun.arg
    b_t = Q_ab.arg
    c_t = Q_cd.fun.arg
    d_t = Q_cd.arg
    eq_th = SPECL([a_t, b_t, c_t, d_t], RAT_EQ)
    return EQ_MP(eq_th, th)


def feq_to_Q_eq(th):
    """|- feq a b c d  ==>  |- Q a b = Q c d."""
    from basics import rator

    # th concl = feq a b c d = ((feq a) b c) d.
    fcd = rator(th._concl)  # feq a b c
    fc = rator(fcd)  # feq a b
    fa = rator(fc)  # feq a
    a_t = rand(fa)
    b_t = rand(fc)
    c_t = rand(fcd)
    d_t = rand(th._concl)
    eq_th = SPECL([a_t, b_t, c_t, d_t], RAT_EQ)
    return EQ_MP(SYM(eq_th), th)


# ---------------------------------------------------------------------------
# Step 8.  Surjectivity of Q:  |- !X. ?a b. X = Q a b.
#
# Strategy: dest_rat X is a class (IS_RAT (dest_rat X)), so by IS_RAT_DEF it
# equals feq a b for some a, b. Apply mk_rat: X = mk_rat (dest_rat X) =
# mk_rat (feq a b) = Q a b.
# ---------------------------------------------------------------------------

X_var = Var("X", rat_ty)

# Type annotations for rat-typed parameters in goal strings.
_R_TYPES = {
    "X": rat_ty,
    "Y": rat_ty,
    "Z": rat_ty,
    "U": rat_ty,
    "V": rat_ty,
    "W": rat_ty,
}


@proof
def IS_RAT_DEST(p):
    p.goal("!X. IS_RAT (dest_rat X)", types=_R_TYPES)
    p.fix("X")
    X_t = p._parse("X")
    # mk_rat (dest_rat X) = X  (MK_RAT_DEST instantiated).
    a_var = Var("a", rat_ty)
    md_X = INST([(X_t, a_var)], MK_RAT_DEST)
    # |- mk_rat (dest_rat X) = X.
    p.have("dest_md:").by_cong(dest_rat, md_X)
    # |- dest_rat (mk_rat (dest_rat X)) = dest_rat X.
    # RAT_DEST_MK at r := dest_rat X:
    dr_X = mk_comb(dest_rat, X_t)
    iso_inst = INST([(dr_X, _r_n2b)], RAT_DEST_MK)
    # |- IS_RAT (dest_rat X) = (dest_rat (mk_rat (dest_rat X)) = dest_rat X).
    p.thus("IS_RAT (dest_rat X)").by_eq_mp(SYM(iso_inst), "dest_md")


@proof
def Q_SURJ(p):
    p.goal("!X. ?a b. X = Q a b", types=_R_TYPES)
    p.fix("X")
    X_t = p._parse("X")
    p.have("isr: IS_RAT (dest_rat X)").by_match(IS_RAT_DEST)
    # Unfold: ?pa pb. dest_rat X = feq pa pb.
    dr_X = mk_comb(dest_rat, X_t)
    p.have("ex: ?pa pb. dest_rat X = feq pa pb").by_eq_mp(
        p.unfold(IS_RAT_DEF, dr_X), "isr"
    )
    p.choose("pa pb: dest_rat X = feq pa pb", from_="ex")
    a_var = Var("a", rat_ty)
    md_X = INST([(X_t, a_var)], MK_RAT_DEST)  # mk_rat (dest_rat X) = X
    with p.calc("Xpapb: X") as c:
        c.step("= mk_rat (dest_rat X)").by_thm(SYM(md_X))
        c.step("= mk_rat (feq pa pb)").by_cong(mk_rat, "pb_eq")
        c.step("= Q pa pb").by_thm(SYM(p.unfold(Q_DEF, "pa", "pb")))
    p.thus("?a b. X = Q a b").by_witness(["pa", "pb"], "Xpapb")


# ---------------------------------------------------------------------------
# §5 Part 1.  Definition 17 and Sätze 78-80.
#
# The relation `=` on rat is the kernel-level equality; Sätze 78, 79, 80
# (reflexivity, symmetry, transitivity of `=`) are direct REFL/SYM/TRANS
# applied to terms of type rat.
# ---------------------------------------------------------------------------

# Satz 78:  X = X.
SATZ_78 = GEN(X_var, REFL(X_var))


@proof
def SATZ_79(p):
    p.goal("!X Y. X = Y ==> Y = X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: X = Y")
    p.thus("Y = X").by_thm(SYM(p.fact("h")))


@proof
def SATZ_80(p):
    p.goal("!X Y Z. X = Y ==> Y = Z ==> X = Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h1: X = Y", "h2: Y = Z")
    p.thus("X = Z").by_trans("h1", "h2")


# ---------------------------------------------------------------------------
# §5 Part 2.  Definitions 18, 19 and order on rat.
#
#   X > Y  iff for some (every) representatives a/b of X, c/d of Y,
#           the fraction-level fgt a b c d holds.
#
# We use the existential form (the well-definedness Satz 44 ensures that
# "for some" coincides with "for every").
# ---------------------------------------------------------------------------

RGT_DEF = define(
    "rgt",
    "rat -> rat -> bool",
    "\\X:rat Y:rat. ?a b c d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d",
    infix=(40, "non"),
)
RGT = mk_const("rgt", [])

RLT_DEF = define(
    "rlt",
    "rat -> rat -> bool",
    "\\X:rat Y:rat. ?a b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d",
    infix=(40, "non"),
)
RLT = mk_const("rlt", [])

register_unfolder("rgt", lambda a, b: UNFOLD(RGT_DEF, a, b))
register_unfolder("rlt", lambda a, b: UNFOLD(RLT_DEF, a, b))


# Connection lemma: for any representatives, fgt at the fraction level lifts to
# rgt at the rat level (and vice versa).
@proof
def RGT_INTRO(p):
    p.goal("!a b c d. fgt a b c d ==> rgt (Q a b) (Q c d)")
    p.fix("a b c d")
    p.assume("hgt: fgt a b c d")
    Q_ab = p._parse("Q a b")
    Q_cd = p._parse("Q c d")
    body_inner = CONJ(REFL(Q_ab), CONJ(REFL(Q_cd), p.fact("hgt")))
    p.thus("rgt (Q a b) (Q c d)").by_witness(["a", "b", "c", "d"], body_inner)


@proof
def RLT_INTRO(p):
    p.goal("!a b c d. flt a b c d ==> rlt (Q a b) (Q c d)")
    p.fix("a b c d")
    p.assume("hlt: flt a b c d")
    Q_ab = p._parse("Q a b")
    Q_cd = p._parse("Q c d")
    body_inner = CONJ(REFL(Q_ab), CONJ(REFL(Q_cd), p.fact("hlt")))
    p.thus("rlt (Q a b) (Q c d)").by_witness(["a", "b", "c", "d"], body_inner)


# Elimination: rgt (Q a b) (Q c d) ==> fgt a b c d (and similarly for rlt).
# These are the inverse-direction lemmas of RGT_INTRO/RLT_INTRO; together with
# RAT_EQ they form the rgt/rlt <-> fgt/flt isomorphism on canonical forms.
@proof
def RGT_ELIM(p):
    p.goal("!a b c d. rgt (Q a b) (Q c d) ==> fgt a b c d")
    p.fix("a b c d")
    p.assume("h: rgt (Q a b) (Q c d)")
    p.choose(
        "a1 b1 c1 d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1 /\\ fgt a1 b1 c1 d1",
        from_="h",
    )
    p.split("d1_eq", "(hQab, hrest)")
    p.split("hrest", "(hQcd, hgt)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    p.have("feq_ab_s: feq a1 b1 a b").by_match(SATZ_38, "feq_ab")
    p.have("feq_cd_s: feq c1 d1 c d").by_match(SATZ_38, "feq_cd")
    p.thus("fgt a b c d").by_match(SATZ_44, "hgt", "feq_ab_s", "feq_cd_s")


@proof
def RLT_ELIM(p):
    p.goal("!a b c d. rlt (Q a b) (Q c d) ==> flt a b c d")
    p.fix("a b c d")
    p.assume("h: rlt (Q a b) (Q c d)")
    p.choose(
        "a1 b1 c1 d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1 /\\ flt a1 b1 c1 d1",
        from_="h",
    )
    p.split("d1_eq", "(hQab, hrest)")
    p.split("hrest", "(hQcd, hlt)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    p.have("feq_ab_s: feq a1 b1 a b").by_match(SATZ_38, "feq_ab")
    p.have("feq_cd_s: feq c1 d1 c d").by_match(SATZ_38, "feq_cd")
    p.thus("flt a b c d").by_match(SATZ_45, "hlt", "feq_ab_s", "feq_cd_s")


# Satz 81 (trichotomy):  X = Y \/ rgt X Y \/ rlt X Y.
@proof
def SATZ_81(p):
    p.goal("!X Y. X = Y \\/ rgt X Y \\/ rlt X Y", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    # Trichotomy at fraction level.
    p.have("tri: feq a b c d \\/ fgt a b c d \\/ flt a b c d").by_match(SATZ_41)
    with p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by_cases("tri"):
        with p.case("e: feq a b c d"):
            # X = Q a b = Q c d = Y.
            Qab_eq_Qcd = feq_to_Q_eq(p.fact("e"))  # |- Q a b = Q c d
            with p.calc("X_eq_Y: X") as c:
                c.step("= Q a b").by_thm(p.fact("b_eq"))
                c.step("= Q c d").by_thm(Qab_eq_Qcd)
                c.step("= Y").by_thm(SYM(p.fact("d_eq")))
            p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by(
                DISJ1, "X_eq_Y", "rgt X Y \\/ rlt X Y"
            )
        with p.case("g: fgt a b c d"):
            p.have("rg: rgt (Q a b) (Q c d)").by_match(RGT_INTRO, "g")
            # rgt X Y via X = Q a b, Y = Q c d substitution.
            p.have("rgXY: rgt X Y").by_rewrite_of(
                "rg", [SYM(p.fact("b_eq")), SYM(p.fact("d_eq"))]
            )
            p.have("orMid: rgt X Y \\/ rlt X Y").by(DISJ1, "rgXY", "rlt X Y")
            p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by(DISJ2, "X = Y", "orMid")
        with p.case("l: flt a b c d"):
            p.have("rl: rlt (Q a b) (Q c d)").by_match(RLT_INTRO, "l")
            p.have("rlXY: rlt X Y").by_rewrite_of(
                "rl", [SYM(p.fact("b_eq")), SYM(p.fact("d_eq"))]
            )
            p.have("orMid: rgt X Y \\/ rlt X Y").by(DISJ2, "rgt X Y", "rlXY")
            p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by(DISJ2, "X = Y", "orMid")


# A useful helper: from rgt X Y, deconstruct to obtain representatives.
# Implemented inline via p.choose chains in subsequent proofs.


# Satz 82:  rgt X Y ==> rlt Y X.
@proof
def SATZ_82(p):
    p.goal("!X Y. rgt X Y ==> rlt Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rgt X Y")
    p.choose("a b c d: X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="h")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hgt)")
    p.simp("hX", "hY")
    p.have("flt: flt c d a b").by_match(SATZ_42, "hgt")
    p.have("rl_QcdQab: rlt (Q c d) (Q a b)").by_match(RLT_INTRO, "flt")
    p.thus("rlt Y X").by_rewrite_of("rl_QcdQab", [])


# Satz 83:  rlt X Y ==> rgt Y X.
@proof
def SATZ_83(p):
    p.goal("!X Y. rlt X Y ==> rgt Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rlt X Y")
    p.choose("a b c d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="h")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hlt)")
    p.simp("hX", "hY")
    p.have("fgt: fgt c d a b").by_match(SATZ_43, "hlt")
    p.have("rg_QcdQab: rgt (Q c d) (Q a b)").by_match(RGT_INTRO, "fgt")
    p.thus("rgt Y X").by_rewrite_of("rg_QcdQab", [])


# Definition 20 / 21:  >= and <= on rat.
RGE_DEF = define(
    "rge", "rat -> rat -> bool", "\\X:rat Y:rat. rgt X Y \\/ X = Y", infix=(40, "non")
)
RGE = mk_const("rge", [])

RLE_DEF = define(
    "rle", "rat -> rat -> bool", "\\X:rat Y:rat. rlt X Y \\/ X = Y", infix=(40, "non")
)
RLE = mk_const("rle", [])

register_disj_unfolder("rge", lambda a, b: UNFOLD(RGE_DEF, a, b))
register_disj_unfolder("rle", lambda a, b: UNFOLD(RLE_DEF, a, b))


# rge t t / rle t t are reflexive via the X = Y disjunct of their disj-unfold.
register_refl_prover(
    "rge",
    lambda t: EQ_MP(SYM(UNFOLD(RGE_DEF, t, t)), DISJ2(mk_app(RGT, t, t), REFL(t))),
)
register_refl_prover(
    "rle",
    lambda t: EQ_MP(SYM(UNFOLD(RLE_DEF, t, t)), DISJ2(mk_app(RLT, t, t), REFL(t))),
)


# Satz 84:  rge X Y ==> rle Y X.
@proof
def SATZ_84(p):
    p.goal("!X Y. rge X Y ==> rle Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rge X Y")
    with p.thus("rle Y X").by_cases("h"):
        with p.case("g: rgt X Y"):
            p.have("l: rlt Y X").by_match(SATZ_82, "g")
            p.have("orL: rlt Y X \\/ Y = X").by(DISJ1, "l", "Y = X")
            p.thus("rle Y X").by_fold("orL")
        with p.case("e: X = Y"):
            p.have("eYX: Y = X").by_thm(SYM(p.fact("e")))
            p.have("orR: rlt Y X \\/ Y = X").by(DISJ2, "rlt Y X", "eYX")
            p.thus("rle Y X").by_fold("orR")


# Satz 85:  rle X Y ==> rge Y X.
@proof
def SATZ_85(p):
    p.goal("!X Y. rle X Y ==> rge Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rle X Y")
    with p.thus("rge Y X").by_cases("h"):
        with p.case("l: rlt X Y"):
            p.have("g: rgt Y X").by_match(SATZ_83, "l")
            p.have("orL: rgt Y X \\/ Y = X").by(DISJ1, "g", "Y = X")
            p.thus("rge Y X").by_fold("orL")
        with p.case("e: X = Y"):
            p.have("eYX: Y = X").by_thm(SYM(p.fact("e")))
            p.have("orR: rgt Y X \\/ Y = X").by(DISJ2, "rgt Y X", "eYX")
            p.thus("rge Y X").by_fold("orR")


# Satz 86 (transitivity of <):  rlt X Y, rlt Y Z ==> rlt X Z.
@proof
def SATZ_86(p):
    p.goal("!X Y Z. rlt X Y ==> rlt Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h1: rlt X Y", "h2: rlt Y Z")
    p.choose("a b c d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="h1")
    p.split("d_eq", "(hX, t1)")
    p.split("t1", "(hY1, hlt1)")
    # For the second hypothesis, we need a copy of Y's representation; it's
    # consistent with hY1, but the (e, f) representatives of Z are fresh.
    p.choose(
        "e1 f1 g1 h1n: Y = Q e1 f1 /\\ Z = Q g1 h1n /\\ flt e1 f1 g1 h1n", from_="h2"
    )
    p.split("h1n_eq", "(hY2, t2)")
    p.split("t2", "(hZ, hlt2)")
    p.simp("hX", "hZ")
    # Y = Q c d = Q e1 f1 ; so Q c d = Q e1 f1, hence feq c d e1 f1.
    p.have("Qcd_eq_Qe1f1: Q c d = Q e1 f1").by_thm(
        TRANS(SYM(p.fact("hY1")), p.fact("hY2"))
    )
    p.have("feq_eq: feq c d e1 f1").by_thm(Q_eq_to_feq(p.fact("Qcd_eq_Qe1f1")))
    p.have("feq_e1f1_cd: feq e1 f1 c d").by_match(SATZ_38, "feq_eq")
    p.have("flt_cd_gh: flt c d g1 h1n").by_match(
        SATZ_45, "hlt2", "feq_e1f1_cd", ...
    )
    p.have("flt_ab_gh: flt a b g1 h1n").by_match(SATZ_50, "hlt1", "flt_cd_gh")
    p.have("rl: rlt (Q a b) (Q g1 h1n)").by_match(RLT_INTRO, "flt_ab_gh")
    p.thus("rlt X Z").by_rewrite_of("rl", [])


# Satz 89:  for any X there exists Z > X.
@proof
def SATZ_89(p):
    p.goal("!X. ?Z. rgt Z X", types=_R_TYPES)
    p.fix("X")
    p.have("ex: ?a b. X = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="ex")
    # Witness: Q (a+a) b. SATZ_53: fgt (x1+x1) x2 x1 x2.
    p.have("fg: fgt (a+a) b a b").by_match(SATZ_53)
    p.have("rg: rgt (Q (a+a) b) (Q a b)").by_match(RGT_INTRO, "fg")
    # rgt (Q (a+a) b) X via X = Q a b.
    Z_witness = p._parse("Q (a+a) b")
    p.have("rgZX: rgt (Q (a+a) b) X").by_rewrite_of("rg", [SYM(p.fact("b_eq"))])
    p.thus("?Z. rgt Z X").by_witness(Z_witness, "rgZX")


# Satz 90:  for any X there exists Z < X.
@proof
def SATZ_90(p):
    p.goal("!X. ?Z. rlt Z X", types=_R_TYPES)
    p.fix("X")
    p.have("ex: ?a b. X = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="ex")
    p.have("fl: flt a (b+b) a b").by_match(SATZ_54)
    p.have("rl: rlt (Q a (b+b)) (Q a b)").by_match(RLT_INTRO, "fl")
    Z_witness = p._parse("Q a (b+b)")
    p.have("rlZX: rlt (Q a (b+b)) X").by_rewrite_of("rl", [SYM(p.fact("b_eq"))])
    p.thus("?Z. rlt Z X").by_witness(Z_witness, "rlZX")


# Satz 87:  rle X Y /\ rlt Y Z  -or-  rlt X Y /\ rle Y Z  ==>  rlt X Z.
@proof
def SATZ_87A(p):
    p.goal("!X Y Z. rle X Y ==> rlt Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("hle: rle X Y", "hlt: rlt Y Z")
    with p.thus("rlt X Z").by_cases("hle"):
        with p.case("l: rlt X Y"):
            p.thus("rlt X Z").by_match(SATZ_86, "l", "hlt")
        with p.case("e: X = Y"):
            p.thus("rlt X Z").by_rewrite_of("hlt", ["e"])


@proof
def SATZ_87B(p):
    p.goal("!X Y Z. rlt X Y ==> rle Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("hlt: rlt X Y", "hle: rle Y Z")
    with p.thus("rlt X Z").by_cases("hle"):
        with p.case("l: rlt Y Z"):
            p.thus("rlt X Z").by_match(SATZ_86, "hlt", "l")
        with p.case("e: Y = Z"):
            p.thus("rlt X Z").by_rewrite_of("hlt", ["e"])


# Satz 88:  rle X Y /\ rle Y Z  ==>  rle X Z.
@proof
def SATZ_88(p):
    p.goal("!X Y Z. rle X Y ==> rle Y Z ==> rle X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h1: rle X Y", "h2: rle Y Z")
    with p.thus("rle X Z").by_cases("h1"):
        with p.case("l1: rlt X Y"):
            p.have("lt_XZ: rlt X Z").by_match(SATZ_87B, "l1", "h2")
            p.have("orL: rlt X Z \\/ X = Z").by(DISJ1, "lt_XZ", "X = Z")
            p.thus("rle X Z").by_fold("orL")
        with p.case("e1: X = Y"):
            with p.thus("rle X Z").by_cases("h2"):
                with p.case("l2: rlt Y Z"):
                    p.have("lt_XZ: rlt X Z").by_rewrite_of("l2", ["e1"])
                    p.have("orL: rlt X Z \\/ X = Z").by(DISJ1, "lt_XZ", "X = Z")
                    p.thus("rle X Z").by_fold("orL")
                with p.case("e2: Y = Z"):
                    p.have("eq_XZ: X = Z").by_thm(TRANS(p.fact("e1"), p.fact("e2")))
                    p.have("orR: rlt X Z \\/ X = Z").by(DISJ2, "rlt X Z", "eq_XZ")
                    p.thus("rle X Z").by_fold("orR")


# Satz 91 (density of rationals):  rlt X Y ==> ?Z. rlt X Z /\ rlt Z Y.
@proof
def SATZ_91(p):
    p.goal("!X Y. rlt X Y ==> ?Z. rlt X Z /\\ rlt Z Y", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rlt X Y")
    p.choose("a b c d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="h")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hlt)")
    # Witness midpoint Q (a+c) (b+d).
    # Satz 55 gives flt a b (a+c) (b+d) /\ flt (a+c) (b+d) c d.
    # Actually Satz 55 returns the conjunction directly via ?-witness.
    # We use SATZ_55 statement: flt x1 x2 y1 y2 ==> ?z1 z2. flt x1 x2 z1 z2 /\ flt z1 z2 y1 y2.
    p.have("ex55: ?z1 z2. flt a b z1 z2 /\\ flt z1 z2 c d").by_match(SATZ_55, "hlt")
    p.choose("z1 z2: flt a b z1 z2 /\\ flt z1 z2 c d", from_="ex55")
    p.split("z2_eq", "(flt_a, flt_b)")
    p.have("rl1_QabQz: rlt (Q a b) (Q z1 z2)").by_match(RLT_INTRO, "flt_a")
    p.have("rl2_QzQcd: rlt (Q z1 z2) (Q c d)").by_match(RLT_INTRO, "flt_b")
    p.simp("hX", "hY")
    p.have("rlt_XZ: rlt X (Q z1 z2)").by_rewrite_of("rl1_QabQz", [])
    p.have("rlt_ZY: rlt (Q z1 z2) Y").by_rewrite_of("rl2_QzQcd", [])
    p.have("conj: rlt X (Q z1 z2) /\\ rlt (Q z1 z2) Y").by(CONJ, "rlt_XZ", "rlt_ZY")
    p.thus("?Z. rlt X Z /\\ rlt Z Y").by_witness(p._parse("Q z1 z2"), "conj")


# ---------------------------------------------------------------------------
# §5 Part 3.  Definition 22 -- addition on rat.
#
#   X + Y := the unique class containing the sum of representatives.
# Operationally:
#   radd X Y := @Z. ?a b c d. X = Q a b /\ Y = Q c d /\ Z = Q (a*d + c*b) (b*d).
# ---------------------------------------------------------------------------

RADD_DEF = define(
    "radd",
    "rat -> rat -> rat",
    "\\X:rat Y:rat. @Z:rat. ?a b c d. X = Q a b /\\ Y = Q c d "
    "/\\ Z = Q (a*d + c*b) (b*d)",
    infix=(50, "left"),
)
RADD = mk_const("radd", [])


# Key canonical-form lemma:
#   radd (Q a b) (Q c d) = Q (a*d + c*b) (b*d).
#
# Proof: SELECT_AX gives that radd (Q a b) (Q c d) satisfies
#   ?a' b' c' d'. Q a b = Q a' b' /\ Q c d = Q c' d'
#                  /\ radd ... = Q (a'*d' + c'*b') (b'*d')
# from the witnessed existence at (a, b, c, d).
# Then well-definedness (Satz 56) on (a,b,c,d) ~ (a',b',c',d') yields
# Q (a*d + c*b) (b*d) = Q (a'*d' + c'*b') (b'*d') = radd ...
# whence the result by SYM and TRANS.
@proof
def RADD_QQ(p):
    p.goal("!a b c d. radd (Q a b) (Q c d) = Q (a*d + c*b) (b*d)")
    p.fix("a b c d")
    # Witness the SELECT body of RADD_DEF at canonical (a, b, c, d, Q ...);
    # each conjunct is reflexive at this tuple.
    p.have(
        "ex: ?Z:rat. ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ Z = Q (a1*d1 + c1*b1) (b1*d1)"
    ).by_exists(["Q (a*d + c*b) (b*d)", "a", "b", "c", "d"])
    # Read radd's defining body at radd (Q a b) (Q c d) via SELECT_AX.
    p.have(
        "sel_body: ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)"
    ).by_select_def(RADD_DEF, "Q a b", "Q c d", from_="ex")
    p.choose(
        "a1 b1 c1 d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)",
        from_="sel_body",
    )
    p.split("d1_eq", "(hQab, hQcd, hradd)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    p.have("feq_sum: feq (a*d + c*b) (b*d) (a1*d1 + c1*b1) (b1*d1)").by_match(
        SATZ_56, "feq_ab", "feq_cd"
    )
    p.have("Qsum: Q (a*d + c*b) (b*d) = Q (a1*d1 + c1*b1) (b1*d1)").by_thm(
        feq_to_Q_eq(p.fact("feq_sum"))
    )
    with p.calc("radd (Q a b) (Q c d)", thus=True) as cc:
        cc.step("= Q (a1*d1 + c1*b1) (b1*d1)").by_thm("hradd")
        cc.step("= Q (a*d + c*b) (b*d)").by_thm(SYM(p.fact("Qsum")))


# Helpers for lifting binary operations / relations on rat to representatives.
# Both consume two equations ``hX : tX = Q a b`` and ``hY : tY = Q c d`` and
# produce an equation about ``op tX tY``: ``_bin_subst`` only bridges the
# operands (``op tX tY = op (Q a b) (Q c d)``), while ``_Q_canon`` chains
# through an ``op_QQ`` lemma to land at the canonical ``Q ...`` form. The
# arguments ``a, b, c, d`` are read out of the equations' RHS, so callers
# never have to re-parse them.


def _bin_subst(op_const, hX, hY):
    """|- op tX tY = op (Q a b) (Q c d)."""
    return TRANS(
        AP_THM(AP_TERM(op_const, hX), rand(hY._concl.fun)),
        AP_TERM(mk_app(op_const, rand(hX._concl)), hY),
    )


def _Q_canon(op_const, op_QQ, hX, hY):
    """|- op tX tY = Q (canonical), where ``op_QQ`` is the
    ``!a b c d. op (Q a b) (Q c d) = Q (...)`` lemma."""
    Q_ab = rand(hX._concl)
    Q_cd = rand(hY._concl)
    return TRANS(
        _bin_subst(op_const, hX, hY),
        SPECL([rand(Q_ab.fun), rand(Q_ab), rand(Q_cd.fun), rand(Q_cd)], op_QQ),
    )


# Satz 92 (commutativity of rat addition):  X + Y = Y + X.
@proof
def SATZ_92(p):
    p.goal("!X Y. radd X Y = radd Y X", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    radd_XY = _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), p.fact("d_eq"))
    radd_YX = _Q_canon(RADD, RADD_QQ, p.fact("d_eq"), p.fact("b_eq"))
    p.have("feq58: feq (a*d + c*b) (b*d) (c*b + a*d) (d*b)").by_match(SATZ_58)
    p.have("Qcomm: Q (a*d + c*b) (b*d) = Q (c*b + a*d) (d*b)").by_thm(
        feq_to_Q_eq(p.fact("feq58"))
    )
    with p.calc("radd X Y", thus=True) as c:
        c.step("= Q (a*d + c*b) (b*d)").by_thm(radd_XY)
        c.step("= Q (c*b + a*d) (d*b)").by_thm(p.fact("Qcomm"))
        c.step("= radd Y X").by_thm(SYM(radd_YX))


# Satz 93 (associativity of rat addition):  (X + Y) + Z = X + (Y + Z).
@proof
def SATZ_93(p):
    p.goal("!X Y Z. radd (radd X Y) Z = radd X (radd Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    # radd X Y = Q (a*d + c*b) (b*d).
    radd_XY = _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), p.fact("d_eq"))
    # (radd X Y) + Z = Q ((a*d+c*b)*f + e*(b*d)) ((b*d)*f).
    lhs_canon = _Q_canon(RADD, RADD_QQ, radd_XY, p.fact("f_eq"))
    # radd Y Z = Q (c*f + e*d) (d*f).
    radd_YZ = _Q_canon(RADD, RADD_QQ, p.fact("d_eq"), p.fact("f_eq"))
    # X + (radd Y Z) = Q (a*(d*f) + (c*f+e*d)*b) (b*(d*f)).
    rhs_canon = _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), radd_YZ)
    # SATZ_59 gives the fraction-level associativity equivalence.
    p.have(
        "feq59: feq ((a*d + c*b)*f + e*(b*d)) ((b*d)*f) "
        "(a*(d*f) + (c*f + e*d)*b) (b*(d*f))"
    ).by_match(SATZ_59)
    p.have(
        "Qassoc: Q ((a*d + c*b)*f + e*(b*d)) ((b*d)*f) "
        "= Q (a*(d*f) + (c*f + e*d)*b) (b*(d*f))"
    ).by_thm(feq_to_Q_eq(p.fact("feq59")))
    with p.calc("radd (radd X Y) Z", thus=True) as c:
        c.step("= Q ((a*d + c*b)*f + e*(b*d)) ((b*d)*f)").by_thm(lhs_canon)
        c.step("= Q (a*(d*f) + (c*f + e*d)*b) (b*(d*f))").by_thm(p.fact("Qassoc"))
        c.step("= radd X (radd Y Z)").by_thm(SYM(rhs_canon))


# Satz 94:  X + Y > X.
@proof
def SATZ_94(p):
    p.goal("!X Y. rgt (radd X Y) X", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.have("radd_eq_canon:").by_thm(
        _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), p.fact("d_eq"))
    )
    # radd_eq_canon : |- radd X Y = Q (a*d + c*b) (b*d).
    p.have("fg: fgt (a*d + c*b) (b*d) a b").by_match(SATZ_60)
    p.have("rg_canon: rgt (Q (a*d + c*b) (b*d)) (Q a b)").by_match(RGT_INTRO, "fg")
    # rg_canon rewritten back: lhs via SYM(radd_eq_canon), rhs via SYM(b_eq).
    p.thus("rgt (radd X Y) X").by_rewrite_of(
        "rg_canon", [SYM(p.fact("radd_eq_canon")), SYM(p.fact("b_eq"))]
    )


# Satz 95:  X > Y ==> X + Z > Y + Z.
@proof
def SATZ_95(p):
    p.goal("!X Y Z. rgt X Y ==> rgt (radd X Z) (radd Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rgt X Y")
    p.choose("a b c d: X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="h")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hgt)")
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("e f: Z = Q e f", from_="eZ")
    # Lift fgt to canonical-sum fgt via SATZ_61.
    p.have("fg_sum: fgt (a*f + e*b) (b*f) (c*f + e*d) (d*f)").by_match(SATZ_61, "hgt")
    p.have("rg_canon: rgt (Q (a*f + e*b) (b*f)) (Q (c*f + e*d) (d*f))").by_match(
        RGT_INTRO, "fg_sum"
    )
    # X + Z = Q (a*f + e*b) (b*f).
    p.have("radd_XZ:").by_thm(_Q_canon(RADD, RADD_QQ, p.fact("hX"), p.fact("f_eq")))
    p.have("radd_YZ:").by_thm(_Q_canon(RADD, RADD_QQ, p.fact("hY"), p.fact("f_eq")))
    # rg_canon rewritten back: lhs/rhs Q-canonical → radd-form.
    p.thus("rgt (radd X Z) (radd Y Z)").by_rewrite_of(
        "rg_canon", [SYM(p.fact("radd_XZ")), SYM(p.fact("radd_YZ"))]
    )


# Satz 96A = Satz 95.
SATZ_96A = SATZ_95


# Satz 96B:  X = Y ==> X + Z = Y + Z  (well-definedness of +).
@proof
def SATZ_96B(p):
    p.goal("!X Y Z. X = Y ==> radd X Z = radd Y Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: X = Y")
    Z_t = p._parse("Z")
    p.have("eq_l:").by_cong(RADD, "h")
    p.thus("radd X Z = radd Y Z").by_cong("eq_l", Z_t)


# Satz 96C:  X < Y ==> X + Z < Y + Z.
@proof
def SATZ_96C(p):
    p.goal("!X Y Z. rlt X Y ==> rlt (radd X Z) (radd Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rlt X Y")
    p.have("hYX: rgt Y X").by_match(SATZ_83, "h")
    p.have("gYZ: rgt (radd Y Z) (radd X Z)").by_match(SATZ_95, "hYX")
    p.thus("rlt (radd X Z) (radd Y Z)").by_match(SATZ_82, "gYZ")


# Satz 97A:  X + Z > Y + Z  ==>  X > Y.
@proof
def SATZ_97A(p):
    p.goal("!X Y Z. rgt (radd X Z) (radd Y Z) ==> rgt X Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rgt (radd X Z) (radd Y Z)")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    radd_XZ = _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), p.fact("f_eq"))
    radd_YZ = _Q_canon(RADD, RADD_QQ, p.fact("d_eq"), p.fact("f_eq"))
    bridge_h = _bin_subst(RGT, radd_XZ, radd_YZ)
    p.have("rg_canon: rgt (Q (a*f + e*b) (b*f)) (Q (c*f + e*d) (d*f))").by_eq_mp(
        bridge_h, "h"
    )
    p.have("fg_canon: fgt (a*f + e*b) (b*f) (c*f + e*d) (d*f)").by_match(
        RGT_ELIM, "rg_canon"
    )
    p.have("fg_orig: fgt a b c d").by_match(SATZ_63A, "fg_canon")
    p.have("rg_QQ: rgt (Q a b) (Q c d)").by_match(RGT_INTRO, "fg_orig")
    bridge_XY = _bin_subst(RGT, p.fact("b_eq"), p.fact("d_eq"))
    p.thus("rgt X Y").by_eq_mp(SYM(bridge_XY), "rg_QQ")


# Satz 97B:  X + Z = Y + Z  ==>  X = Y.
@proof
def SATZ_97B(p):
    p.goal("!X Y Z. radd X Z = radd Y Z ==> X = Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: radd X Z = radd Y Z")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    radd_XZ = _Q_canon(RADD, RADD_QQ, p.fact("b_eq"), p.fact("f_eq"))
    radd_YZ = _Q_canon(RADD, RADD_QQ, p.fact("d_eq"), p.fact("f_eq"))
    with p.calc("Qsum_eq: Q (a*f + e*b) (b*f)") as c:
        c.step("= radd X Z").by_thm(SYM(radd_XZ))
        c.step("= radd Y Z").by_thm(p.fact("h"))
        c.step("= Q (c*f + e*d) (d*f)").by_thm(radd_YZ)
    p.have("feq_canon: feq (a*f + e*b) (b*f) (c*f + e*d) (d*f)").by_thm(
        Q_eq_to_feq(p.fact("Qsum_eq"))
    )
    p.have("feq_orig: feq a b c d").by_match(SATZ_63B, "feq_canon")
    p.have("Q_eq: Q a b = Q c d").by_thm(feq_to_Q_eq(p.fact("feq_orig")))
    with p.calc("X", thus=True) as c:
        c.step("= Q a b").by_thm(p.fact("b_eq"))
        c.step("= Q c d").by_thm(p.fact("Q_eq"))
        c.step("= Y").by_thm(SYM(p.fact("d_eq")))


# Satz 97C:  X + Z < Y + Z  ==>  X < Y.
@proof
def SATZ_97C(p):
    p.goal("!X Y Z. rlt (radd X Z) (radd Y Z) ==> rlt X Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rlt (radd X Z) (radd Y Z)")
    p.have("hYX: rgt (radd Y Z) (radd X Z)").by_match(SATZ_83, "h")
    p.have("rgYX: rgt Y X").by_match(SATZ_97A, "hYX")
    p.thus("rlt X Y").by_match(SATZ_82, "rgYX")


# Satz 98:  rgt X Y, rgt Z U ==> rgt (X + Z) (Y + U).
@proof
def SATZ_98(p):
    p.goal(
        "!X Y Z U. rgt X Y ==> rgt Z U ==> rgt (radd X Z) (radd Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hXY: rgt X Y", "hZU: rgt Z U")
    Z_t = p._parse("Z")
    Y_t = p._parse("Y")
    U_t = p._parse("U")
    p.have("g1: rgt (radd X Z) (radd Y Z)").by_match(SATZ_95, "hXY")
    p.have("g2: rgt (radd Z Y) (radd U Y)").by_match(SATZ_95, "hZU")
    p.simp(SPECL([Z_t, Y_t], SATZ_92), SPECL([U_t, Y_t], SATZ_92))
    p.have("g2b: rgt (radd Y Z) (radd Y U)").by_rewrite_of("g2", [])
    p.have("l1: rlt (radd Y Z) (radd X Z)").by_match(SATZ_82, "g1")
    p.have("l2: rlt (radd Y U) (radd Y Z)").by_match(SATZ_82, "g2b")
    p.have("l_chain: rlt (radd Y U) (radd X Z)").by_match(SATZ_86, "l2", "l1")
    p.thus("rgt (radd X Z) (radd Y U)").by_match(SATZ_83, "l_chain")


# Satz 99A:  rge X Y, rgt Z U ==> rgt (X + Z) (Y + U).
@proof
def SATZ_99A(p):
    p.goal(
        "!X Y Z U. rge X Y ==> rgt Z U ==> rgt (radd X Z) (radd Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hge: rge X Y", "hgt: rgt Z U")
    Y_t = p._parse("Y")
    Z_t = p._parse("Z")
    U_t = p._parse("U")
    with p.thus("rgt (radd X Z) (radd Y U)").by_cases("hge"):
        with p.case("g_xy: rgt X Y"):
            p.thus("rgt (radd X Z) (radd Y U)").by_match(SATZ_98, "g_xy", "hgt")
        with p.case("e_xy: X = Y"):
            p.have("g_zy: rgt (radd Z Y) (radd U Y)").by_match(SATZ_95, "hgt")
            p.simp(SPECL([Z_t, Y_t], SATZ_92), SPECL([U_t, Y_t], SATZ_92))
            p.have("g_yzy: rgt (radd Y Z) (radd Y U)").by_rewrite_of("g_zy", [])
            p.have("eq_xz_yz: radd X Z = radd Y Z").by_match(SATZ_96B, "e_xy")
            p.thus("rgt (radd X Z) (radd Y U)").by_rewrite_of("g_yzy", ["eq_xz_yz"])


# Satz 99B:  rgt X Y, rge Z U ==> rgt (X + Z) (Y + U).
@proof
def SATZ_99B(p):
    p.goal(
        "!X Y Z U. rgt X Y ==> rge Z U ==> rgt (radd X Z) (radd Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hgt: rgt X Y", "hge: rge Z U")
    with p.thus("rgt (radd X Z) (radd Y U)").by_cases("hge"):
        with p.case("g_zu: rgt Z U"):
            p.thus("rgt (radd X Z) (radd Y U)").by_match(SATZ_98, "hgt", "g_zu")
        with p.case("e_zu: Z = U"):
            p.have("g_xu: rgt (radd X U) (radd Y U)").by_match(SATZ_95, "hgt")
            p.thus("rgt (radd X Z) (radd Y U)").by_rewrite_of("g_xu", ["e_zu"])


# Satz 100:  rge X Y, rge Z U ==> rge (X + Z) (Y + U).
@proof
def SATZ_100(p):
    p.goal(
        "!X Y Z U. rge X Y ==> rge Z U ==> rge (radd X Z) (radd Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hge1: rge X Y", "hge2: rge Z U")
    Y_t = p._parse("Y")
    with p.thus("rge (radd X Z) (radd Y U)").by_cases("hge1"):
        with p.case("g1: rgt X Y"):
            p.have("g_xy_zu: rgt (radd X Z) (radd Y U)").by_match(
                SATZ_99B, "g1", "hge2"
            )
            p.have("orL: rgt (radd X Z) (radd Y U) \\/ radd X Z = radd Y U").by(
                DISJ1, "g_xy_zu", "radd X Z = radd Y U"
            )
            p.thus("rge (radd X Z) (radd Y U)").by_fold("orL")
        with p.case("e1: X = Y"):
            with p.thus("rge (radd X Z) (radd Y U)").by_cases("hge2"):
                with p.case("g2: rgt Z U"):
                    p.have("g_xz_yu: rgt (radd X Z) (radd Y U)").by_match(
                        SATZ_99A, "hge1", "g2"
                    )
                    p.have("orL: rgt (radd X Z) (radd Y U) \\/ radd X Z = radd Y U").by(
                        DISJ1, "g_xz_yu", "radd X Z = radd Y U"
                    )
                    p.thus("rge (radd X Z) (radd Y U)").by_fold("orL")
                with p.case("e2: Z = U"):
                    p.have("eq_xz_yz: radd X Z = radd Y Z").by_match(SATZ_96B, "e1")
                    p.have("eq_yz_yu:").by_cong(mk_app(RADD, Y_t), "e2")
                    p.have("eq_full: radd X Z = radd Y U").by_trans(
                        "eq_xz_yz", "eq_yz_yu"
                    )
                    p.have("orR: rgt (radd X Z) (radd Y U) \\/ radd X Z = radd Y U").by(
                        DISJ2, "rgt (radd X Z) (radd Y U)", "eq_full"
                    )
                    p.thus("rge (radd X Z) (radd Y U)").by_fold("orR")


# Satz 101 (existence & uniqueness of subtraction):  given rgt X Y, the
# equation radd Y U = X has a unique solution U.


@proof
def SATZ_101_EXIST(p):
    p.goal("!X Y. rgt X Y ==> ?U. radd Y U = X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("hgt: rgt X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    c_t = p._parse("c")
    d_t = p._parse("d")
    # rgt X Y = rgt (Q a b) (Q c d) → fgt a b c d.
    bridge_xy = _bin_subst(RGT, p.fact("b_eq"), p.fact("d_eq"))
    p.have("rg_QQ: rgt (Q a b) (Q c d)").by_eq_mp(bridge_xy, "hgt")
    p.have("fg: fgt a b c d").by_match(RGT_ELIM, "rg_QQ")
    # SATZ_67_EXIST: ?u1 u2. feq (c*u2 + u1*d) (d*u2) a b.
    p.have("ex_uv: ?u1 u2. feq (c*u2 + u1*d) (d*u2) a b").by_match(SATZ_67_EXIST, "fg")
    p.choose("u v: feq (c*v + u*d) (d*v) a b", from_="ex_uv")
    u_t = p._parse("u")
    v_t = p._parse("v")
    # Q (c*v + u*d) (d*v) = Q a b.
    p.have("Qsum_eq: Q (c*v + u*d) (d*v) = Q a b").by_thm(feq_to_Q_eq(p.fact("v_eq")))
    # radd (Q c d) (Q u v) = Q (c*v + u*d) (d*v) by RADD_QQ.
    p.have("radd_canon:").by_inst(RADD_QQ, c_t, d_t, u_t, v_t)
    # radd Y (Q u v) = radd (Q c d) (Q u v).
    p.have("sub_y:").by_cong(RADD, "d_eq")  # RADD Y = RADD (Q c d)
    p.have("sub_y_at:").by_cong("sub_y", mk_app(Q, u_t, v_t))
    p.have("X_eq_Qab:").by_thm(SYM(p.fact("b_eq")))
    with p.calc("rad_eq_X: radd Y (Q u v)") as c:
        c.step("= radd (Q c d) (Q u v)").by_thm("sub_y_at")
        c.step("= Q (c*v + u*d) (d*v)").by_thm("radd_canon")
        c.step("= Q a b").by_thm("Qsum_eq")
        c.step("= X").by_thm("X_eq_Qab")
    p.thus("?U. radd Y U = X").by_witness("Q u v", "rad_eq_X")


@proof
def SATZ_101_UNIQUE(p):
    p.goal("!X Y V W. radd Y V = X ==> radd Y W = X ==> V = W", types={**_R_TYPES})
    p.fix("X Y V W")
    p.assume("hv: radd Y V = X", "hw: radd Y W = X")
    p.have("hw_sym:").by_thm(SYM(p.fact("hw")))
    p.have("eq_yvw: radd Y V = radd Y W").by_trans("hv", "hw_sym")
    Y_t = p._parse("Y")
    V_t = p._parse("V")
    W_t = p._parse("W")
    p.have("eq_vy_yv:").by_inst(SATZ_92, V_t, Y_t)  # V+Y = Y+V
    p.have("eq_wy_yw:").by_inst(SATZ_92, W_t, Y_t)  # W+Y = Y+W
    with p.calc("eq_vw_swap: radd V Y") as c:
        c.step("= radd Y V").by_thm("eq_vy_yv")
        c.step("= radd Y W").by_thm("eq_yvw")
        c.step("= radd W Y").by_thm(SYM(p.fact("eq_wy_yw")))
    p.thus("V = W").by_match(SATZ_97B, "eq_vw_swap")


# Definition 23:  X - Y is the unique U with radd Y U = X.
RSUB_DEF = define(
    "rsub",
    "rat -> rat -> rat",
    "\\X:rat Y:rat. @U:rat. radd Y U = X",
    infix=(50, "left"),
)
RSUB = mk_const("rsub", [])


# Defining property:  rgt X Y ==> radd Y (rsub X Y) = X.
@proof
def RSUB_PROP(p):
    p.goal("!X Y. rgt X Y ==> radd Y (rsub X Y) = X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rgt X Y")
    p.have("ex: ?U:rat. radd Y U = X").by_match(SATZ_101_EXIST, "h")
    p.thus("radd Y (rsub X Y) = X").by_select_def(RSUB_DEF, "X", "Y", from_="ex")


# ---------------------------------------------------------------------------
# §5 Part 4.  Definition 24 -- multiplication on rat.
#
#   X * Y := the unique class containing the product of representatives.
# Operationally:
#   rmul X Y := @Z. ?a b c d. X = Q a b /\ Y = Q c d /\ Z = Q (a*c) (b*d).
# ---------------------------------------------------------------------------

RMUL_DEF = define(
    "rmul",
    "rat -> rat -> rat",
    "\\X:rat Y:rat. @Z:rat. ?a b c d. X = Q a b /\\ Y = Q c d /\\ Z = Q (a*c) (b*d)",
    infix=(60, "left"),
)
RMUL = mk_const("rmul", [])


# Key canonical-form lemma (parallel to RADD_QQ):
#   rmul (Q a b) (Q c d) = Q (a*c) (b*d).
@proof
def RMUL_QQ(p):
    p.goal("!a b c d. rmul (Q a b) (Q c d) = Q (a*c) (b*d)")
    p.fix("a b c d")
    p.have(
        "ex: ?Z:rat. ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ Z = Q (a1*c1) (b1*d1)"
    ).by_exists(["Q (a*c) (b*d)", "a", "b", "c", "d"])
    p.have(
        "sel_body: ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)"
    ).by_select_def(RMUL_DEF, "Q a b", "Q c d", from_="ex")
    p.choose(
        "a1 b1 c1 d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
        " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)",
        from_="sel_body",
    )
    p.split("d1_eq", "(hQab, hQcd, hrmul)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    p.have("feq_prod: feq (a*c) (b*d) (a1*c1) (b1*d1)").by_match(
        SATZ_68, "feq_ab", "feq_cd"
    )
    p.have("Qprod: Q (a*c) (b*d) = Q (a1*c1) (b1*d1)").by_thm(
        feq_to_Q_eq(p.fact("feq_prod"))
    )
    with p.calc("rmul (Q a b) (Q c d)", thus=True) as cc:
        cc.step("= Q (a1*c1) (b1*d1)").by_thm("hrmul")
        cc.step("= Q (a*c) (b*d)").by_thm(SYM(p.fact("Qprod")))


# Satz 102 (commutativity of rat multiplication):  X * Y = Y * X.
@proof
def SATZ_102(p):
    p.goal("!X Y. rmul X Y = rmul Y X", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    rmul_XY = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("d_eq"))
    rmul_YX = _Q_canon(RMUL, RMUL_QQ, p.fact("d_eq"), p.fact("b_eq"))
    p.have("feq69: feq (a*c) (b*d) (c*a) (d*b)").by_match(SATZ_69)
    p.have("Qcomm: Q (a*c) (b*d) = Q (c*a) (d*b)").by_thm(feq_to_Q_eq(p.fact("feq69")))
    with p.calc("rmul X Y", thus=True) as c:
        c.step("= Q (a*c) (b*d)").by_thm(rmul_XY)
        c.step("= Q (c*a) (d*b)").by_thm(p.fact("Qcomm"))
        c.step("= rmul Y X").by_thm(SYM(rmul_YX))


# Satz 103 (associativity of rat multiplication):  (XY)Z = X(YZ).
@proof
def SATZ_103(p):
    p.goal("!X Y Z. rmul (rmul X Y) Z = rmul X (rmul Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    rmul_XY = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("d_eq"))
    lhs_canon = _Q_canon(RMUL, RMUL_QQ, rmul_XY, p.fact("f_eq"))
    rmul_YZ = _Q_canon(RMUL, RMUL_QQ, p.fact("d_eq"), p.fact("f_eq"))
    rhs_canon = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), rmul_YZ)
    p.have("feq70: feq ((a*c)*e) ((b*d)*f) (a*(c*e)) (b*(d*f))").by_match(SATZ_70)
    p.have("Qassoc: Q ((a*c)*e) ((b*d)*f) = Q (a*(c*e)) (b*(d*f))").by_thm(
        feq_to_Q_eq(p.fact("feq70"))
    )
    with p.calc("rmul (rmul X Y) Z", thus=True) as c:
        c.step("= Q ((a*c)*e) ((b*d)*f)").by_thm(lhs_canon)
        c.step("= Q (a*(c*e)) (b*(d*f))").by_thm(p.fact("Qassoc"))
        c.step("= rmul X (rmul Y Z)").by_thm(SYM(rhs_canon))


# Satz 104 (distributivity):  X(Y + Z) = XY + XZ.
@proof
def SATZ_104(p):
    p.goal("!X Y Z. rmul X (radd Y Z) = radd (rmul X Y) (rmul X Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    # Y + Z canonical.
    radd_YZ = _Q_canon(RADD, RADD_QQ, p.fact("d_eq"), p.fact("f_eq"))
    # X(Y+Z) = Q (a*(c*f + e*d)) (b*(d*f)).
    lhs_canon = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), radd_YZ)
    # XY = Q (a*c) (b*d).
    rmul_XY = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("d_eq"))
    # XZ = Q (a*e) (b*f).
    rmul_XZ = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("f_eq"))
    # XY + XZ = Q ((a*c)*(b*f) + (a*e)*(b*d)) ((b*d)*(b*f)).
    rhs_canon = _Q_canon(RADD, RADD_QQ, rmul_XY, rmul_XZ)
    # SATZ_71 fraction-level distributivity.
    p.have(
        "feq71: feq (a*(c*f + e*d)) (b*(d*f)) ((a*c)*(b*f) + (a*e)*(b*d)) ((b*d)*(b*f))"
    ).by_match(SATZ_71)
    p.have(
        "Qdistr: Q (a*(c*f + e*d)) (b*(d*f)) "
        "= Q ((a*c)*(b*f) + (a*e)*(b*d)) ((b*d)*(b*f))"
    ).by_thm(feq_to_Q_eq(p.fact("feq71")))
    with p.calc("rmul X (radd Y Z)", thus=True) as c:
        c.step("= Q (a*(c*f + e*d)) (b*(d*f))").by_thm(lhs_canon)
        c.step("= Q ((a*c)*(b*f) + (a*e)*(b*d)) ((b*d)*(b*f))").by_thm(p.fact("Qdistr"))
        c.step("= radd (rmul X Y) (rmul X Z)").by_thm(SYM(rhs_canon))


# Satz 105A:  rgt X Y ==> rgt (X*Z) (Y*Z).
@proof
def SATZ_105A(p):
    p.goal("!X Y Z. rgt X Y ==> rgt (rmul X Z) (rmul Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rgt X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    bridge_xy = _bin_subst(RGT, p.fact("b_eq"), p.fact("d_eq"))
    p.have("rg_QQ: rgt (Q a b) (Q c d)").by_eq_mp(bridge_xy, "h")
    p.have("fg: fgt a b c d").by_match(RGT_ELIM, "rg_QQ")
    p.have("fg_prod: fgt (a*e) (b*f) (c*e) (d*f)").by_match(SATZ_72A, "fg")
    p.have("rg_canon: rgt (Q (a*e) (b*f)) (Q (c*e) (d*f))").by_match(
        RGT_INTRO, "fg_prod"
    )
    rmul_XZ = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("f_eq"))
    rmul_YZ = _Q_canon(RMUL, RMUL_QQ, p.fact("d_eq"), p.fact("f_eq"))
    bridge = _bin_subst(RGT, rmul_XZ, rmul_YZ)
    p.thus("rgt (rmul X Z) (rmul Y Z)").by_eq_mp(SYM(bridge), "rg_canon")


# Satz 105B:  X = Y ==> X*Z = Y*Z.
@proof
def SATZ_105B(p):
    p.goal("!X Y Z. X = Y ==> rmul X Z = rmul Y Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: X = Y")
    Z_t = p._parse("Z")
    p.have("eq_l:").by_cong(RMUL, "h")
    p.thus("rmul X Z = rmul Y Z").by_cong("eq_l", Z_t)


# Satz 105C:  rlt X Y ==> rlt (X*Z) (Y*Z).
@proof
def SATZ_105C(p):
    p.goal("!X Y Z. rlt X Y ==> rlt (rmul X Z) (rmul Y Z)", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rlt X Y")
    p.have("hYX: rgt Y X").by_match(SATZ_83, "h")
    p.have("g_yz_xz: rgt (rmul Y Z) (rmul X Z)").by_match(SATZ_105A, "hYX")
    p.thus("rlt (rmul X Z) (rmul Y Z)").by_match(SATZ_82, "g_yz_xz")


# Satz 106A:  rgt (X*Z) (Y*Z) ==> rgt X Y.
@proof
def SATZ_106A(p):
    p.goal("!X Y Z. rgt (rmul X Z) (rmul Y Z) ==> rgt X Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rgt (rmul X Z) (rmul Y Z)")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    rmul_XZ = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("f_eq"))
    rmul_YZ = _Q_canon(RMUL, RMUL_QQ, p.fact("d_eq"), p.fact("f_eq"))
    bridge_h = _bin_subst(RGT, rmul_XZ, rmul_YZ)
    p.have("rg_canon: rgt (Q (a*e) (b*f)) (Q (c*e) (d*f))").by_eq_mp(bridge_h, "h")
    p.have("fg_canon: fgt (a*e) (b*f) (c*e) (d*f)").by_match(RGT_ELIM, "rg_canon")
    p.have("fg_orig: fgt a b c d").by_match(SATZ_73A, "fg_canon")
    p.have("rg_QQ: rgt (Q a b) (Q c d)").by_match(RGT_INTRO, "fg_orig")
    bridge_xy = _bin_subst(RGT, p.fact("b_eq"), p.fact("d_eq"))
    p.thus("rgt X Y").by_eq_mp(SYM(bridge_xy), "rg_QQ")


# Satz 106B:  X*Z = Y*Z ==> X = Y.
@proof
def SATZ_106B(p):
    p.goal("!X Y Z. rmul X Z = rmul Y Z ==> X = Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rmul X Z = rmul Y Z")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    p.choose("e f: Z = Q e f", from_="eZ")
    rmul_XZ = _Q_canon(RMUL, RMUL_QQ, p.fact("b_eq"), p.fact("f_eq"))
    rmul_YZ = _Q_canon(RMUL, RMUL_QQ, p.fact("d_eq"), p.fact("f_eq"))
    with p.calc("Qprod_eq: Q (a*e) (b*f)") as c:
        c.step("= rmul X Z").by_thm(SYM(rmul_XZ))
        c.step("= rmul Y Z").by_thm(p.fact("h"))
        c.step("= Q (c*e) (d*f)").by_thm(rmul_YZ)
    p.have("feq_canon: feq (a*e) (b*f) (c*e) (d*f)").by_thm(
        Q_eq_to_feq(p.fact("Qprod_eq"))
    )
    p.have("feq_orig: feq a b c d").by_match(SATZ_73B, "feq_canon")
    p.have("Q_eq: Q a b = Q c d").by_thm(feq_to_Q_eq(p.fact("feq_orig")))
    with p.calc("X", thus=True) as c:
        c.step("= Q a b").by_thm(p.fact("b_eq"))
        c.step("= Q c d").by_thm(p.fact("Q_eq"))
        c.step("= Y").by_thm(SYM(p.fact("d_eq")))


# Satz 106C:  rlt (X*Z) (Y*Z) ==> rlt X Y.
@proof
def SATZ_106C(p):
    p.goal("!X Y Z. rlt (rmul X Z) (rmul Y Z) ==> rlt X Y", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h: rlt (rmul X Z) (rmul Y Z)")
    p.have("hYX: rgt (rmul Y Z) (rmul X Z)").by_match(SATZ_83, "h")
    p.have("rgYX: rgt Y X").by_match(SATZ_106A, "hYX")
    p.thus("rlt X Y").by_match(SATZ_82, "rgYX")


# Satz 107:  rgt X Y, rgt Z U ==> rgt (X*Z) (Y*U).
@proof
def SATZ_107(p):
    p.goal(
        "!X Y Z U. rgt X Y ==> rgt Z U ==> rgt (rmul X Z) (rmul Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hXY: rgt X Y", "hZU: rgt Z U")
    Z_t = p._parse("Z")
    Y_t = p._parse("Y")
    U_t = p._parse("U")
    p.have("g1: rgt (rmul X Z) (rmul Y Z)").by_match(SATZ_105A, "hXY")
    p.have("g2: rgt (rmul Z Y) (rmul U Y)").by_match(SATZ_105A, "hZU")
    p.simp(SPECL([Z_t, Y_t], SATZ_102), SPECL([U_t, Y_t], SATZ_102))
    p.have("g2b: rgt (rmul Y Z) (rmul Y U)").by_rewrite_of("g2", [])
    p.have("l1: rlt (rmul Y Z) (rmul X Z)").by_match(SATZ_82, "g1")
    p.have("l2: rlt (rmul Y U) (rmul Y Z)").by_match(SATZ_82, "g2b")
    p.have("l_chain: rlt (rmul Y U) (rmul X Z)").by_match(SATZ_86, "l2", "l1")
    p.thus("rgt (rmul X Z) (rmul Y U)").by_match(SATZ_83, "l_chain")


# Satz 108A:  rge X Y, rgt Z U ==> rgt (X*Z) (Y*U).
@proof
def SATZ_108A(p):
    p.goal(
        "!X Y Z U. rge X Y ==> rgt Z U ==> rgt (rmul X Z) (rmul Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hge: rge X Y", "hgt: rgt Z U")
    Y_t = p._parse("Y")
    Z_t = p._parse("Z")
    U_t = p._parse("U")
    with p.thus("rgt (rmul X Z) (rmul Y U)").by_cases("hge"):
        with p.case("g_xy: rgt X Y"):
            p.thus("rgt (rmul X Z) (rmul Y U)").by_match(SATZ_107, "g_xy", "hgt")
        with p.case("e_xy: X = Y"):
            p.have("g_zy: rgt (rmul Z Y) (rmul U Y)").by_match(SATZ_105A, "hgt")
            p.simp(SPECL([Z_t, Y_t], SATZ_102), SPECL([U_t, Y_t], SATZ_102))
            p.have("g_yzy: rgt (rmul Y Z) (rmul Y U)").by_rewrite_of("g_zy", [])
            p.have("eq_xz_yz: rmul X Z = rmul Y Z").by_match(SATZ_105B, "e_xy")
            p.thus("rgt (rmul X Z) (rmul Y U)").by_rewrite_of("g_yzy", ["eq_xz_yz"])


# Satz 108B:  rgt X Y, rge Z U ==> rgt (X*Z) (Y*U).
@proof
def SATZ_108B(p):
    p.goal(
        "!X Y Z U. rgt X Y ==> rge Z U ==> rgt (rmul X Z) (rmul Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hgt: rgt X Y", "hge: rge Z U")
    with p.thus("rgt (rmul X Z) (rmul Y U)").by_cases("hge"):
        with p.case("g_zu: rgt Z U"):
            p.thus("rgt (rmul X Z) (rmul Y U)").by_match(SATZ_107, "hgt", "g_zu")
        with p.case("e_zu: Z = U"):
            p.have("g_xu: rgt (rmul X U) (rmul Y U)").by_match(SATZ_105A, "hgt")
            p.thus("rgt (rmul X Z) (rmul Y U)").by_rewrite_of("g_xu", ["e_zu"])


# Satz 109:  rge X Y, rge Z U ==> rge (X*Z) (Y*U).
@proof
def SATZ_109(p):
    p.goal(
        "!X Y Z U. rge X Y ==> rge Z U ==> rge (rmul X Z) (rmul Y U)", types=_R_TYPES
    )
    p.fix("X Y Z U")
    p.assume("hge1: rge X Y", "hge2: rge Z U")
    Y_t = p._parse("Y")
    with p.thus("rge (rmul X Z) (rmul Y U)").by_cases("hge1"):
        with p.case("g1: rgt X Y"):
            p.have("g_xy_zu: rgt (rmul X Z) (rmul Y U)").by_match(
                SATZ_108B, "g1", "hge2"
            )
            p.have("orL: rgt (rmul X Z) (rmul Y U) \\/ rmul X Z = rmul Y U").by(
                DISJ1, "g_xy_zu", "rmul X Z = rmul Y U"
            )
            p.thus("rge (rmul X Z) (rmul Y U)").by_fold("orL")
        with p.case("e1: X = Y"):
            with p.thus("rge (rmul X Z) (rmul Y U)").by_cases("hge2"):
                with p.case("g2: rgt Z U"):
                    p.have("g_xz_yu: rgt (rmul X Z) (rmul Y U)").by_match(
                        SATZ_108A, "hge1", "g2"
                    )
                    p.have("orL: rgt (rmul X Z) (rmul Y U) \\/ rmul X Z = rmul Y U").by(
                        DISJ1, "g_xz_yu", "rmul X Z = rmul Y U"
                    )
                    p.thus("rge (rmul X Z) (rmul Y U)").by_fold("orL")
                with p.case("e2: Z = U"):
                    p.have("eq_xz_yz: rmul X Z = rmul Y Z").by_match(SATZ_105B, "e1")
                    p.have("eq_yz_yu:").by_cong(mk_app(RMUL, Y_t), "e2")
                    p.have("eq_full: rmul X Z = rmul Y U").by_trans(
                        "eq_xz_yz", "eq_yz_yu"
                    )
                    p.have("orR: rgt (rmul X Z) (rmul Y U) \\/ rmul X Z = rmul Y U").by(
                        DISJ2, "rgt (rmul X Z) (rmul Y U)", "eq_full"
                    )
                    p.thus("rge (rmul X Z) (rmul Y U)").by_fold("orR")


# Satz 110 (existence & uniqueness of division):  YU = X has a unique solution.
@proof
def SATZ_110_EXIST(p):
    p.goal("!X Y. ?U. rmul Y U = X", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    p.choose("c d: Y = Q c d", from_="eY")
    c_t = p._parse("c")
    d_t = p._parse("d")
    # Witness U = Q (a*d) (b*c). SATZ_77_EXIST: feq (c*(a*d)) (d*(b*c)) a b.
    p.have("feq77: feq (c*(a*d)) (d*(b*c)) a b").by_match(SATZ_77_EXIST)
    p.have("Qprod_eq_a: Q (c*(a*d)) (d*(b*c)) = Q a b").by_thm(
        feq_to_Q_eq(p.fact("feq77"))
    )
    # rmul (Q c d) (Q (a*d) (b*c)) = Q (c*(a*d)) (d*(b*c)) by RMUL_QQ.
    p.have("rmul_canon:").by_inst(RMUL_QQ, c_t, d_t, p._parse("a*d"), p._parse("b*c"))
    p.have("sub_y:").by_cong(RMUL, "d_eq")  # RMUL Y = RMUL (Q c d)
    U_witness = mk_app(Q, p._parse("a*d"), p._parse("b*c"))
    p.have("sub_y_at:").by_cong("sub_y", U_witness)
    p.have("X_eq_Qab:").by_thm(SYM(p.fact("b_eq")))
    with p.calc("rmul_eq_X: rmul Y (Q (a*d) (b*c))") as c:
        c.step("= rmul (Q c d) (Q (a*d) (b*c))").by_thm("sub_y_at")
        c.step("= Q (c*(a*d)) (d*(b*c))").by_thm("rmul_canon")
        c.step("= Q a b").by_thm("Qprod_eq_a")
        c.step("= X").by_thm("X_eq_Qab")
    p.thus("?U. rmul Y U = X").by_witness("Q (a*d) (b*c)", "rmul_eq_X")


@proof
def SATZ_110_UNIQUE(p):
    p.goal("!X Y V W. rmul Y V = X ==> rmul Y W = X ==> V = W", types=_R_TYPES)
    p.fix("X Y V W")
    p.assume("hv: rmul Y V = X", "hw: rmul Y W = X")
    p.have("hw_sym:").by_thm(SYM(p.fact("hw")))
    p.have("eq_yvw: rmul Y V = rmul Y W").by_trans("hv", "hw_sym")
    Y_t = p._parse("Y")
    V_t = p._parse("V")
    W_t = p._parse("W")
    p.have("eq_vy_yv:").by_inst(SATZ_102, V_t, Y_t)
    p.have("eq_wy_yw:").by_inst(SATZ_102, W_t, Y_t)
    with p.calc("eq_vw_swap: rmul V Y") as c:
        c.step("= rmul Y V").by_thm("eq_vy_yv")
        c.step("= rmul Y W").by_thm("eq_yvw")
        c.step("= rmul W Y").by_thm(SYM(p.fact("eq_wy_yw")))
    p.thus("V = W").by_match(SATZ_106B, "eq_vw_swap")


# Definition 27:  X / Y is the unique U with rmul Y U = X.
RDIV_DEF = define(
    "rdiv",
    "rat -> rat -> rat",
    "\\X:rat Y:rat. @U:rat. rmul Y U = X",
    infix=(60, "left"),
)
RDIV = mk_const("rdiv", [])


# Defining property:  rmul Y (rdiv X Y) = X.
@proof
def RDIV_PROP(p):
    p.goal("!X Y. rmul Y (rdiv X Y) = X", types=_R_TYPES)
    p.fix("X Y")
    p.have("ex: ?U:rat. rmul Y U = X").by_match(SATZ_110_EXIST)
    p.thus("rmul Y (rdiv X Y) = X").by_select_def(RDIV_DEF, "X", "Y", from_="ex")


# ---------------------------------------------------------------------------
# §5 Part 5.  Sätze 111-115 -- integer rationals (Definition 25),
#             identification with naturals, Archimedean property.
# ---------------------------------------------------------------------------


# Satz 111B (forward):  Q x 1 = Q y 1 ==> x = y.
@proof
def SATZ_111B_FWD(p):
    p.goal("!x y. Q x 1 = Q y 1 ==> x = y")
    p.fix("x y")
    p.assume("h: Q x 1 = Q y 1")
    p.have("feq: feq x 1 y 1").by_thm(Q_eq_to_feq(p.fact("h")))
    p.have("eq_mul: x * 1 = y * 1").by_def(FEQ_DEF, "feq")
    p.have("mul1_x:").by_inst(MUL_1, "x")
    p.have("mul1_y:").by_inst(MUL_1, "y")
    with p.calc("x", thus=True) as c:
        c.step("= x*1").by_thm(SYM(p.fact("mul1_x")))
        c.step("= y*1").by_thm(p.fact("eq_mul"))
        c.step("= y").by_thm("mul1_y")


# Satz 111B (reverse):  x = y ==> Q x 1 = Q y 1.
@proof
def SATZ_111B_REV(p):
    p.goal("!x y. x = y ==> Q x 1 = Q y 1")
    p.fix("x y")
    p.assume("h: x = y")
    p.have("sub_l: Q x = Q y").by_cong(Q, "h")
    p.thus("Q x 1 = Q y 1").by_cong("sub_l", "1")


# Satz 111A (forward):  rgt (Q x 1) (Q y 1) ==> x > y.
@proof
def SATZ_111A_FWD(p):
    p.goal("!x y. rgt (Q x 1) (Q y 1) ==> x > y")
    p.fix("x y")
    p.assume("h: rgt (Q x 1) (Q y 1)")
    p.have("fg: fgt x 1 y 1").by_match(RGT_ELIM, "h")
    p.have("gt_mul: x * 1 > y * 1").by_def(FGT_DEF, "fg")
    p.thus("x > y").by_thm(REWRITE_RULE([MUL_1], p.fact("gt_mul")))


# Satz 111A (reverse):  x > y ==> rgt (Q x 1) (Q y 1).
@proof
def SATZ_111A_REV(p):
    p.goal("!x y. x > y ==> rgt (Q x 1) (Q y 1)")
    p.fix("x y")
    p.assume("h: x > y")
    x_t = p._parse("x")
    y_t = p._parse("y")
    ONE_t = p._parse("1")
    p.have("mul1_x:").by_inst(MUL_1, x_t)  # x * 1 = x
    p.have("mul1_y:").by_inst(MUL_1, y_t)  # y * 1 = y
    p.have("gt_mul: x * 1 > y * 1").by_rewrite_of("h", ["mul1_x", "mul1_y"])
    p.have("fg: fgt x 1 y 1").by_eq_mp(
        SYM(UNFOLD(FGT_DEF, x_t, ONE_t, y_t, ONE_t)), "gt_mul"
    )
    p.thus("rgt (Q x 1) (Q y 1)").by_match(RGT_INTRO, "fg")


# Satz 111C (forward):  rlt (Q x 1) (Q y 1) ==> x < y.
@proof
def SATZ_111C_FWD(p):
    p.goal("!x y. rlt (Q x 1) (Q y 1) ==> x < y")
    p.fix("x y")
    p.assume("h: rlt (Q x 1) (Q y 1)")
    p.have("fl: flt x 1 y 1").by_match(RLT_ELIM, "h")
    p.have("lt_mul: x * 1 < y * 1").by_def(FLT_DEF, "fl")
    p.thus("x < y").by_thm(REWRITE_RULE([MUL_1], p.fact("lt_mul")))


# Satz 111C (reverse):  x < y ==> rlt (Q x 1) (Q y 1).
@proof
def SATZ_111C_REV(p):
    p.goal("!x y. x < y ==> rlt (Q x 1) (Q y 1)")
    p.fix("x y")
    p.assume("h: x < y")
    x_t = p._parse("x")
    y_t = p._parse("y")
    ONE_t = p._parse("1")
    p.have("mul1_x:").by_inst(MUL_1, x_t)
    p.have("mul1_y:").by_inst(MUL_1, y_t)
    p.have("lt_mul: x * 1 < y * 1").by_rewrite_of("h", ["mul1_x", "mul1_y"])
    p.have("fl: flt x 1 y 1").by_eq_mp(
        SYM(UNFOLD(FLT_DEF, x_t, ONE_t, y_t, ONE_t)), "lt_mul"
    )
    p.thus("rlt (Q x 1) (Q y 1)").by_match(RLT_INTRO, "fl")


# Definition 25:  IS_INT_RAT X iff X = Q x 1 for some x.
IS_INT_RAT_DEF = define("IS_INT_RAT", "rat -> bool", "\\X:rat. ?x. X = Q x 1")
IS_INT_RAT = mk_const("IS_INT_RAT", [])


# Satz 112A:  Q x 1 + Q y 1 = Q (x + y) 1.
@proof
def SATZ_112A(p):
    p.goal("!x y. radd (Q x 1) (Q y 1) = Q (x + y) 1")
    p.fix("x y")
    x_t = p._parse("x")
    y_t = p._parse("y")
    ONE_t = p._parse("1")
    # RADD_QQ: radd (Q x 1) (Q y 1) = Q (x*1 + y*1) (1*1).
    p.have("raw:").by_inst(RADD_QQ, x_t, ONE_t, y_t, ONE_t)
    # Rewrite x*1 → x, y*1 → y, 1*1 → 1.
    p.thus("radd (Q x 1) (Q y 1) = Q (x + y) 1").by_rewrite_of("raw", [MUL_1])


# Satz 112B:  (Q x 1) * (Q y 1) = Q (x*y) 1.
@proof
def SATZ_112B(p):
    p.goal("!x y. rmul (Q x 1) (Q y 1) = Q (x * y) 1")
    p.fix("x y")
    x_t = p._parse("x")
    y_t = p._parse("y")
    ONE_t = p._parse("1")
    p.have("raw:").by_inst(RMUL_QQ, x_t, ONE_t, y_t, ONE_t)  # = Q (x*y) (1*1)
    p.thus("rmul (Q x 1) (Q y 1) = Q (x * y) 1").by_rewrite_of("raw", [MUL_1])


# Multiplicative identity:  !X. rmul (Q 1 1) X = X.
@proof
def RMUL_ONE(p):
    p.goal("!X. rmul (Q 1 1) X = X", types=_R_TYPES)
    p.fix("X")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.choose("a b: X = Q a b", from_="eX")
    a_t = p._parse("a")
    b_t = p._parse("b")
    ONE_t = p._parse("1")
    Q11 = mk_app(Q, ONE_t, ONE_t)
    p.have("sub_x:").by_cong(mk_app(RMUL, Q11), "b_eq")
    p.have("canon:").by_inst(RMUL_QQ, ONE_t, ONE_t, a_t, b_t)
    p.have("one_a:").by_inst(ONE_MUL, a_t)  # 1*a = a
    p.have("one_b:").by_inst(ONE_MUL, b_t)  # 1*b = b
    p.have("times_one_a:").by_cong(TIMES, "one_a")
    p.have("eq_l:").by_cong("times_one_a", b_t)  # (1*a)*b = a*b
    p.have("b_one_b:").by_thm(SYM(p.fact("one_b")))  # b = 1*b
    p.have("eq_r:").by_cong(mk_app(TIMES, a_t), "b_one_b")  # a*b = a*(1*b)
    p.have("eq_full:").by_trans("eq_l", "eq_r")
    p.have("feq_th:").by_eq_mp(
        SYM(p.unfold(FEQ_DEF, mk_mul(ONE_t, a_t), mk_mul(ONE_t, b_t), a_t, b_t)),
        "eq_full",
    )
    p.have("Q_eq:").by_thm(feq_to_Q_eq(p.fact("feq_th")))
    p.have("X_eq_Qab:").by_thm(SYM(p.fact("b_eq")))  # Q a b = X
    with p.calc("rmul (Q 1 1) X", thus=True) as c:
        c.step("= rmul (Q 1 1) (Q a b)").by_thm("sub_x")
        c.step("= Q (1*a) (1*b)").by_thm("canon")
        c.step("= Q a b").by_thm("Q_eq")
        c.step("= X").by_thm("X_eq_Qab")


# Satz 113 (the integer rationals satisfy Peano-like axioms).  Landau lists
# five clauses; the meat for us is the third (successor avoids the unit) and
# the fourth (successor is injective) -- both follow from Satz 111B and
# AXIOM_3 / AXIOM_4 at the natural-number level.


@proof
def SATZ_113_3(p):
    p.goal("!x. ~(Q (SUC x) 1 = Q 1 1)")
    p.fix("x")
    with p.suppose("h: Q (SUC x) 1 = Q 1 1"):
        p.have("eq_n: SUC x = 1").by_match(SATZ_111B_FWD, "h")
        p.have("ne_n: ~(SUC x = 1)").by_match(AXIOM_3)
        p.absurd().by_conj("eq_n", "ne_n")


@proof
def SATZ_113_4(p):
    p.goal("!x y. Q (SUC x) 1 = Q (SUC y) 1 ==> Q x 1 = Q y 1")
    p.fix("x y")
    p.assume("h: Q (SUC x) 1 = Q (SUC y) 1")
    p.have("eq_s: SUC x = SUC y").by_match(SATZ_111B_FWD, "h")
    p.have("eq_xy: x = y").by_match(AXIOM_4, "eq_s")
    p.thus("Q x 1 = Q y 1").by_match(SATZ_111B_REV, "eq_xy")


# Satz 114:  for Z = Q x y, we have y * Z = x  (in the integer-rational sense
#            x = Q x 1).
@proof
def SATZ_114(p):
    p.goal("!x y. rmul (Q y 1) (Q x y) = Q x 1")
    p.fix("x y")
    x_t = p._parse("x")
    y_t = p._parse("y")
    ONE_t = p._parse("1")
    p.have("raw:").by_inst(RMUL_QQ, y_t, ONE_t, x_t, y_t)
    # raw: rmul (Q y 1) (Q x y) = Q (y*x) (1*y).
    # Need Q (y*x) (1*y) = Q x 1, via feq (y*x) (1*y) x 1, i.e. (y*x)*1 = x*(1*y).
    yx = mk_mul(y_t, x_t)
    xy_inner = mk_mul(ONE_t, y_t)
    p.have("mul1_yx:").by_inst(MUL_1, yx)  # (y*x)*1 = y*x
    p.have("satz29:").by_inst(SATZ_29, y_t, x_t)  # y*x = x*y
    p.have("one_y:").by_inst(ONE_MUL, y_t)  # 1*y = y
    p.have("y_one:").by_thm(SYM(p.fact("one_y")))  # y = 1*y
    p.have("expand:").by_cong(mk_app(TIMES, x_t), "y_one")  # x*y = x*(1*y)
    with p.calc("eq_chain: (y*x)*1") as c:
        c.step("= y*x").by_thm("mul1_yx")
        c.step("= x*y").by_thm("satz29")
        c.step("= x*(1*y)").by_thm("expand")
    # eq_chain : |- (y*x)*1 = x*(1*y).  FEQ_DEF: feq a b c d = (a*d = c*b).
    # Match a=y*x, b=1*y, c=x, d=1 to fold to feq (y*x) (1*y) x 1.
    p.have("feq_thm:").by_eq_mp(
        SYM(p.unfold(FEQ_DEF, yx, xy_inner, x_t, ONE_t)), "eq_chain"
    )
    p.have("Q_eq:").by_thm(feq_to_Q_eq(p.fact("feq_thm")))
    p.thus("rmul (Q y 1) (Q x y) = Q x 1").by_trans("raw", "Q_eq")


# Satz 115 (Archimedean property):  given X, Y rational, there exists a
# natural z with rgt ((Q z 1) * X) Y.
@proof
def SATZ_115(p):
    p.goal("!X Y. ?z. rgt (rmul (Q z 1) X) Y", types=_R_TYPES)
    p.fix("X Y")
    X_t = p._parse("X")
    Y_t = p._parse("Y")
    YoverX = mk_app(RDIV, Y_t, X_t)
    # By rat-level Satz 89, ?Z. rgt Z (Y/X).
    p.have("ex_Z: ?Z. rgt Z (rdiv Y X)").by_match(SATZ_89)
    p.choose("Z: rgt Z (rdiv Y X)", from_="ex_Z")
    Z_t = p._parse("Z")
    # Reps z, v of Z.
    p.have("eZ: ?a b. Z = Q a b").by_match(Q_SURJ)
    p.choose("z v: Z = Q z v", from_="eZ")
    z_t = p._parse("z")
    v_t = p._parse("v")
    ONE_t = p._parse("1")
    # rgt (Z*X) Y via Satz 105A and rmul (Y/X) X = Y.
    p.fact("Z_eq")  # rgt Z (rdiv Y X) — but it's stored under "Z_eq"? Let me reuse.
    # Actually p.choose("Z: ...") binds the body, what's the fact name?
    # We named the existential "ex_Z" with body rgt Z (rdiv Y X). After choose("Z: ..."),
    # the body becomes a fact under "Z_eq". So rgt Z (rdiv Y X) is registered as Z_eq.
    p.have("g_ZW: rgt (rmul Z X) (rmul (rdiv Y X) X)").by_match(SATZ_105A, "Z_eq")
    p.have("eq_WX_Y: rmul (rdiv Y X) X = Y").by_trans(
        p.have("com:").by_inst(SATZ_102, YoverX, X_t),
        p.have("rdiv_prop:").by_inst(RDIV_PROP, Y_t, X_t),
    )
    p.have("sub:").by_cong(mk_app(RGT, mk_app(RMUL, Z_t, X_t)), "eq_WX_Y")
    p.have("g_ZX_Y: rgt (rmul Z X) Y").by_eq_mp("sub", "g_ZW")
    # v >= 1 (nat).
    p.have("v_ge: v >= 1").by_match(SATZ_24)
    p.have("v_disj: v > 1 \\/ v = 1").by_def(GE_DEF, "v_ge")
    mk_app(Q, ONE_t, ONE_t)
    Qv1 = mk_app(Q, v_t, ONE_t)
    with p.have("rge_v1: rge (Q v 1) (Q 1 1)").by_cases("v_disj"):
        with p.case("g1: v > 1"):
            p.have("rg: rgt (Q v 1) (Q 1 1)").by_match(SATZ_111A_REV, "g1")
            p.have("orL: rgt (Q v 1) (Q 1 1) \\/ Q v 1 = Q 1 1").by(
                DISJ1, "rg", "Q v 1 = Q 1 1"
            )
            p.thus("rge (Q v 1) (Q 1 1)").by_fold("orL")
        with p.case("e1: v = 1"):
            p.have("eq: Q v 1 = Q 1 1").by_match(SATZ_111B_REV, "e1")
            p.have("orR: rgt (Q v 1) (Q 1 1) \\/ Q v 1 = Q 1 1").by(
                DISJ2, "rgt (Q v 1) (Q 1 1)", "eq"
            )
            p.thus("rge (Q v 1) (Q 1 1)").by_fold("orR")
    # Multiplication monotonicity (Satz 109): rge (rmul (Q v 1) (Z*X)) (rmul (Q 1 1) (Z*X)).
    # The rge (Z*X) (Z*X) antecedent is auto-derived via the refl prover.
    p.have(
        "rge_full: rge (rmul (Q v 1) (rmul Z X)) (rmul (Q 1 1) (rmul Z X))"
    ).by_match(SATZ_109, "rge_v1", ...)
    # rmul (Q 1 1) (Z*X) = Z*X.
    p.have("rm1:").by_inst(RMUL_ONE, mk_app(RMUL, Z_t, X_t))
    p.have("sub_rm1:").by_cong(
        mk_app(RGE, mk_app(RMUL, Qv1, mk_app(RMUL, Z_t, X_t))), "rm1"
    )
    p.have("rge_simp: rge (rmul (Q v 1) (rmul Z X)) (rmul Z X)").by_eq_mp(
        p.fact("sub_rm1"), "rge_full"
    )
    # Combine: rge A B, rgt B Y => rgt A Y, where A = (Q v 1)*(Z*X), B = Z*X.
    p.have("le_BA: rle (rmul Z X) (rmul (Q v 1) (rmul Z X))").by_match(
        SATZ_84, "rge_simp"
    )
    p.have("lt_YB: rlt Y (rmul Z X)").by_match(SATZ_82, "g_ZX_Y")
    p.have("lt_YA: rlt Y (rmul (Q v 1) (rmul Z X))").by_match(
        SATZ_87B, "lt_YB", "le_BA"
    )
    p.have("gt_AY: rgt (rmul (Q v 1) (rmul Z X)) Y").by_match(SATZ_83, "lt_YA")
    # (Q v 1) * Z = Q z 1 (Satz 114 with x=z, y=v).
    p.have("qv_z:").by_inst(SATZ_114, z_t, v_t)  # rmul (Q v 1) (Q z v) = Q z 1
    # Bridge rmul (Q v 1) Z = Q z 1 via Z = Q z v.
    p.have("sub_z:").by_cong(mk_app(RMUL, Qv1), "v_eq")
    p.have("eq_QvZ:").by_trans("sub_z", "qv_z")  # rmul (Q v 1) Z = Q z 1
    # Apply X on the right: rmul (rmul (Q v 1) Z) X = rmul (Q z 1) X.
    p.have("rmul_eqQvZ:").by_cong(RMUL, "eq_QvZ")
    p.have("sub_x:").by_cong("rmul_eqQvZ", X_t)
    # Bridge: associativity rmul (Q v 1) (rmul Z X) = rmul (rmul (Q v 1) Z) X (SYM SATZ_103).
    p.have("assoc:").by_inst(SATZ_103, Qv1, Z_t, X_t)
    p.have("assoc_sym:").by_thm(SYM(p.fact("assoc")))
    p.have("eq_full:").by_trans("assoc_sym", "sub_x")
    p.have("sub_g:").by_cong(RGT, "eq_full")
    p.have("sub_g_at:").by_cong("sub_g", Y_t)
    p.have("gt_zX_Y: rgt (rmul (Q z 1) X) Y").by_eq_mp(p.fact("sub_g_at"), "gt_AY")
    p.thus("?z. rgt (rmul (Q z 1) X) Y").by_witness("z", "gt_zX_Y")


if __name__ == "__main__":
    print("§5 foundation:")
    print("  IS_RAT_FEQ_1_1:", pp_thm(IS_RAT_FEQ_1_1))
    print("  MK_RAT_DEST:   ", pp_thm(MK_RAT_DEST))
    print("  RAT_DEST_MK:   ", pp_thm(RAT_DEST_MK))
    print("  IS_RAT_FEQ:    ", pp_thm(IS_RAT_FEQ))
    print("  DEST_RAT_FEQ:  ", pp_thm(DEST_RAT_FEQ))
    print("  RAT_EQ:        ", pp_thm(RAT_EQ))
    print("  IS_RAT_DEST:   ", pp_thm(IS_RAT_DEST))
    print("  Q_SURJ:        ", pp_thm(Q_SURJ))
    print("§5 §1 (= and order):")
    print("  SATZ_78:       ", pp_thm(SATZ_78))
    print("  SATZ_79:       ", pp_thm(SATZ_79))
    print("  SATZ_80:       ", pp_thm(SATZ_80))
    print("  RGT_INTRO:     ", pp_thm(RGT_INTRO))
    print("  RLT_INTRO:     ", pp_thm(RLT_INTRO))
    print("  SATZ_81:       ", pp_thm(SATZ_81))
    print("  SATZ_82:       ", pp_thm(SATZ_82))
    print("  SATZ_83:       ", pp_thm(SATZ_83))
    print("  SATZ_84:       ", pp_thm(SATZ_84))
    print("  SATZ_85:       ", pp_thm(SATZ_85))
    print("  SATZ_86:       ", pp_thm(SATZ_86))
    print("  SATZ_87A:      ", pp_thm(SATZ_87A))
    print("  SATZ_87B:      ", pp_thm(SATZ_87B))
    print("  SATZ_88:       ", pp_thm(SATZ_88))
    print("  SATZ_89:       ", pp_thm(SATZ_89))
    print("  SATZ_90:       ", pp_thm(SATZ_90))
    print("  SATZ_91:       ", pp_thm(SATZ_91))
    print("§5 §3 (addition):")
    print("  RADD_QQ:       ", pp_thm(RADD_QQ))
    print("  SATZ_92:       ", pp_thm(SATZ_92))
    print("  SATZ_93:       ", pp_thm(SATZ_93))
    print("  SATZ_94:       ", pp_thm(SATZ_94))
    print("  SATZ_95:       ", pp_thm(SATZ_95))
    print("  SATZ_96A:      ", pp_thm(SATZ_96A))
    print("  SATZ_96B:      ", pp_thm(SATZ_96B))
    print("  SATZ_96C:      ", pp_thm(SATZ_96C))
    print("  SATZ_97A:      ", pp_thm(SATZ_97A))
    print("  SATZ_97B:      ", pp_thm(SATZ_97B))
    print("  SATZ_97C:      ", pp_thm(SATZ_97C))
    print("  SATZ_98:       ", pp_thm(SATZ_98))
    print("  SATZ_99A:      ", pp_thm(SATZ_99A))
    print("  SATZ_99B:      ", pp_thm(SATZ_99B))
    print("  SATZ_100:      ", pp_thm(SATZ_100))
    print("  SATZ_101_EXIST:", pp_thm(SATZ_101_EXIST))
    print("  SATZ_101_UNIQ: ", pp_thm(SATZ_101_UNIQUE))
    print("  RSUB_PROP:     ", pp_thm(RSUB_PROP))
    print("§5 §4 (multiplication):")
    print("  RMUL_QQ:       ", pp_thm(RMUL_QQ))
    print("  SATZ_102:      ", pp_thm(SATZ_102))
    print("  SATZ_103:      ", pp_thm(SATZ_103))
    print("  SATZ_104:      ", pp_thm(SATZ_104))
    print("  SATZ_105A:     ", pp_thm(SATZ_105A))
    print("  SATZ_105B:     ", pp_thm(SATZ_105B))
    print("  SATZ_105C:     ", pp_thm(SATZ_105C))
    print("  SATZ_106A:     ", pp_thm(SATZ_106A))
    print("  SATZ_106B:     ", pp_thm(SATZ_106B))
    print("  SATZ_106C:     ", pp_thm(SATZ_106C))
    print("  SATZ_107:      ", pp_thm(SATZ_107))
    print("  SATZ_108A:     ", pp_thm(SATZ_108A))
    print("  SATZ_108B:     ", pp_thm(SATZ_108B))
    print("  SATZ_109:      ", pp_thm(SATZ_109))
    print("  SATZ_110_EXIST:", pp_thm(SATZ_110_EXIST))
    print("  SATZ_110_UNIQ: ", pp_thm(SATZ_110_UNIQUE))
    print("  RDIV_PROP:     ", pp_thm(RDIV_PROP))
    print("§5 §5 (integer rationals, Archimedean):")
    print("  SATZ_111A_FWD: ", pp_thm(SATZ_111A_FWD))
    print("  SATZ_111A_REV: ", pp_thm(SATZ_111A_REV))
    print("  SATZ_111B_FWD: ", pp_thm(SATZ_111B_FWD))
    print("  SATZ_111B_REV: ", pp_thm(SATZ_111B_REV))
    print("  SATZ_111C_FWD: ", pp_thm(SATZ_111C_FWD))
    print("  SATZ_111C_REV: ", pp_thm(SATZ_111C_REV))
    print("  SATZ_112A:     ", pp_thm(SATZ_112A))
    print("  SATZ_112B:     ", pp_thm(SATZ_112B))
    print("  SATZ_113_3:    ", pp_thm(SATZ_113_3))
    print("  SATZ_113_4:    ", pp_thm(SATZ_113_4))
    print("  SATZ_114:      ", pp_thm(SATZ_114))
    print("  IS_INT_RAT_DEF:", pp_thm(IS_INT_RAT_DEF))
    print("  RMUL_ONE:      ", pp_thm(RMUL_ONE))
    print("  SATZ_115:      ", pp_thm(SATZ_115))
