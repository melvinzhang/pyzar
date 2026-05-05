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
  Definition 25-27    integer subset, identification, division
"""
from fusion import (
    Var, Comb, REFL, TRANS, MK_COMB, EQ_MP, ABS, INST, INST_TYPE,
    mk_comb, mk_type, new_basic_type_definition,
)
from basics import (
    aty, bty, mk_abs, mk_app, mk_const, mk_eq, rand,
)
from axioms import (
    mk_and, mk_or, mk_imp, mk_not, mk_forall, mk_exists, mk_select,
)
from tactics import (
    AP_TERM, AP_THM, FUN_EXT, SYM, SPEC, SPECL, GEN, GENL,
    CONJ, CONJUNCT1, CONJUNCT2, MP, EXISTS, DISJ1, DISJ2,
    CHOOSE_WITNESS, TRANS_CHAIN, UNFOLD, REWRITE_RULE, AC_PROVE,
    BETA_CONV,
)
from nat import (
    num_ty, ONE, mk_suc, mk_add, mk_mul, PLUS, TIMES,
    SATZ_5, SATZ_6, SATZ_29, SATZ_31,
)
from frac import (
    FEQ, FEQ_DEF, FGT, FGT_DEF, FLT, FLT_DEF, FGE, FGE_DEF, FLE, FLE_DEF,
    SATZ_37, SATZ_38, SATZ_39, SATZ_40,
    SATZ_41, SATZ_42, SATZ_43, SATZ_44, SATZ_45,
    SATZ_46, SATZ_47, SATZ_48, SATZ_49, SATZ_50,
    SATZ_51A, SATZ_51B, SATZ_52, SATZ_53, SATZ_54, SATZ_55,
    SATZ_56, SATZ_57, SATZ_58, SATZ_59, SATZ_60,
    SATZ_61, SATZ_62A, SATZ_62B, SATZ_62C,
    SATZ_63A, SATZ_63B, SATZ_63C, SATZ_64, SATZ_65A, SATZ_65B, SATZ_66,
    SATZ_67_EXIST, SATZ_67_UNIQUE,
    SATZ_68, SATZ_69, SATZ_70, SATZ_71,
    SATZ_72A, SATZ_72B, SATZ_72C,
    SATZ_73A, SATZ_73B, SATZ_73C, SATZ_74, SATZ_75A, SATZ_75B, SATZ_76,
    SATZ_77_EXIST, SATZ_77_UNIQUE,
    x1 as f_x1, x2 as f_x2, y1 as f_y1, y2 as f_y2,
    z1 as f_z1, z2 as f_z2, u1 as f_u1, u2 as f_u2,
    v1 as f_v1, v2 as f_v2, w1 as f_w1, w2 as f_w2,
)
from parser import (
    define, parse, parse_type, pp_thm,
    add_const, add_type, set_default_var_ty,
)
from proof import proof


# ---------------------------------------------------------------------------
# Step 1.  IS_RAT predicate.
# ---------------------------------------------------------------------------
# K : num -> num -> bool is a "rational class" if K = feq a b for some a, b.

n2b_ty = parse_type("num -> num -> bool")

IS_RAT_DEF = define("IS_RAT", "(num -> num -> bool) -> bool",
    "\\K:Knnb. ?a b. K = feq a b", Knnb=n2b_ty)
IS_RAT = mk_const("IS_RAT", [])


# ---------------------------------------------------------------------------
# Step 2.  Witness:  |- IS_RAT (feq 1 1).
# ---------------------------------------------------------------------------

K_var = Var("K", n2b_ty)
# Fresh bound-variable names for IS_RAT's existential (must not clash with
# free-variable names like ``a``, ``b`` in callers).
_pa = Var("pa", num_ty)
_pb = Var("pb", num_ty)

feq_1_1 = mk_app(FEQ, ONE, ONE)


@proof
def IS_RAT_FEQ_1_1(p):
    p.goal("IS_RAT (feq 1 1)")
    refl_th = REFL(feq_1_1)              # |- feq 1 1 = feq 1 1
    inner = EXISTS(
        mk_abs(_pb, mk_eq(feq_1_1, mk_app(FEQ, ONE, _pb))),
        ONE, refl_th)                    # |- ?pb. feq 1 1 = feq 1 pb
    outer = EXISTS(
        mk_abs(_pa, mk_exists(_pb, mk_eq(feq_1_1, mk_app(FEQ, _pa, _pb)))),
        ONE, inner)                      # |- ?pa pb. feq 1 1 = feq pa pb
    p.thus("IS_RAT (feq 1 1)") \
        .by_eq_mp(SYM(UNFOLD(IS_RAT_DEF, feq_1_1)), outer)


# ---------------------------------------------------------------------------
# Step 3.  Carve out `rat` as a subtype of (num -> num -> bool).
# ---------------------------------------------------------------------------

MK_RAT_DEST, RAT_DEST_MK = new_basic_type_definition(
    "rat", ("mk_rat", "dest_rat"), IS_RAT_FEQ_1_1)
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

Q_DEF = define("Q", "num -> num -> rat",
    "\\a b. mk_rat (feq a b)")
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
    a_t = p._parse("a"); b_t = p._parse("b")
    feq_ab = mk_app(FEQ, a_t, b_t)
    refl_th = REFL(feq_ab)
    inner = EXISTS(
        mk_abs(_pb, mk_eq(feq_ab, mk_app(FEQ, a_t, _pb))),
        b_t, refl_th)
    outer = EXISTS(
        mk_abs(_pa, mk_exists(_pb, mk_eq(feq_ab, mk_app(FEQ, _pa, _pb)))),
        a_t, inner)
    p.thus("IS_RAT (feq a b)") \
        .by_eq_mp(SYM(UNFOLD(IS_RAT_DEF, feq_ab)), outer)


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
    p.thus("dest_rat (mk_rat (feq a b)) = feq a b") \
        .by_eq_mp(r_inst, "isr")


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
    a_t = p._parse("a"); b_t = p._parse("b")
    c_t = p._parse("c"); d_t = p._parse("d")
    feq_ab = mk_app(FEQ, a_t, b_t)
    feq_cd = mk_app(FEQ, c_t, d_t)
    Q_ab = mk_app(Q, a_t, b_t)
    Q_cd = mk_app(Q, c_t, d_t)

    # Q a b = mk_rat (feq a b)  via Q_DEF unfolded twice.
    p_var = Var("p", num_ty); q_var = Var("q", num_ty)
    Q_unfold_ab = UNFOLD(Q_DEF, a_t, b_t)        # |- Q a b = mk_rat (feq a b)
    Q_unfold_cd = UNFOLD(Q_DEF, c_t, d_t)        # |- Q c d = mk_rat (feq c d)

    # Forward direction.
    with p.have("fwd: Q a b = Q c d ==> feq a b c d").proof():
        p.assume("hQ: Q a b = Q c d")
        # mk_rat (feq a b) = mk_rat (feq c d).
        h_mk = TRANS_CHAIN([SYM(Q_unfold_ab), p.fact("hQ"), Q_unfold_cd])
        h_dest = AP_TERM(dest_rat, h_mk)
        # dest_rat (mk_rat (feq a b)) = feq a b.
        d_ab = SPECL([a_t, b_t], DEST_RAT_FEQ)
        d_cd = SPECL([c_t, d_t], DEST_RAT_FEQ)
        feq_eq = TRANS_CHAIN([SYM(d_ab), h_dest, d_cd])  # |- feq a b = feq c d
        # Apply at (c, d): feq a b c d = feq c d c d.
        feq_at_c = AP_THM(feq_eq, c_t)              # |- feq a b c = feq c d c
        feq_at_cd = AP_THM(feq_at_c, d_t)           # |- feq a b c d = feq c d c d
        refl_cd = SPECL([c_t, d_t], SATZ_37)        # |- feq c d c d
        p.have("rcd: feq c d c d").by_thm(refl_cd)
        p.thus("feq a b c d").by_eq_mp(SYM(feq_at_cd), "rcd")

    # Reverse direction.
    with p.have("rev: feq a b c d ==> Q a b = Q c d").proof():
        p.assume("hf: feq a b c d")
        # Build !p q. feq a b p q = feq c d p q.
        # For each p, q: prove the bool equality via two MPs.
        with p.have("ptw: !p q. feq a b p q = feq c d p q").proof():
            p.fix("p q")
            p_t = p._parse("p"); q_t = p._parse("q")
            feq_ab_pq = mk_app(FEQ, a_t, b_t, p_t, q_t)
            feq_cd_pq = mk_app(FEQ, c_t, d_t, p_t, q_t)
            # ==>: feq a b p q ==> feq c d p q via SATZ_38 + SATZ_39.
            with p.have("imp1: feq a b p q ==> feq c d p q").proof():
                p.assume("hap: feq a b p q")
                p.have("hcd_ab: feq c d a b").by_match(SATZ_38, "hf")
                p.thus("feq c d p q") \
                    .by_match(SATZ_39, "hcd_ab", "hap")
            # <==: feq c d p q ==> feq a b p q.
            with p.have("imp2: feq c d p q ==> feq a b p q").proof():
                p.assume("hcp: feq c d p q")
                p.thus("feq a b p q") \
                    .by_match(SATZ_39, "hf", "hcp")
            # Bool equality from biconditional.
            from tactics import DISCH
            from basics import dest_eq, mk_eq as _mk_eq
            # We need: feq a b p q = feq c d p q.  Use IMP_ANTISYM_RULE? Simpler:
            # bool extensionality by DEDUCT_ANTISYM_RULE which equates two formulas
            # mutually implying each other.
            from fusion import DEDUCT_ANTISYM_RULE, ASSUME
            th_l = MP(p.fact("imp1"), ASSUME(feq_ab_pq))   # {feq_ab_pq} |- feq_cd_pq
            th_r = MP(p.fact("imp2"), ASSUME(feq_cd_pq))   # {feq_cd_pq} |- feq_ab_pq
            iff_th = SYM(DEDUCT_ANTISYM_RULE(th_l, th_r))
            # DEDUCT_ANTISYM produces |- feq c d p q = feq a b p q (concl(th_l)
            # on the lhs); we want the other orientation.
            p.thus("feq a b p q = feq c d p q").by_thm(iff_th)
        # FUN_EXT twice.
        # ptw : |- !p q. feq a b p q = feq c d p q.
        # First strip the outer ! via SPEC then FUN_EXT on q.
        # Actually: ptw is |- !p. (!q. feq a b p q = feq c d p q).
        # Inner: SPEC p gives !q. .. ; then FUN_EXT gives feq a b p = feq c d p
        # (Or: we directly call FUN_EXT on (!q. feq a b p q = feq c d p q) where
        #  the bound var is q.)
        # Let me build it manually:
        spec_p = SPEC(p_var, p.fact("ptw"))   # |- !q. feq a b p q = feq c d p q
        f_at_p_eq = FUN_EXT(spec_p)           # |- feq a b p = feq c d p
        # Now we need !p. feq a b p = feq c d p, then FUN_EXT.
        gen_f_at_p = GEN(p_var, f_at_p_eq)     # |- !p. feq a b p = feq c d p
        feq_eq = FUN_EXT(gen_f_at_p)           # |- feq a b = feq c d
        # Apply mk_rat: mk_rat (feq a b) = mk_rat (feq c d).
        mk_eq_th = AP_TERM(mk_rat, feq_eq)
        # Bridge with Q_DEF unfolds.
        Q_eq = TRANS_CHAIN([Q_unfold_ab, mk_eq_th, SYM(Q_unfold_cd)])
        p.thus("Q a b = Q c d").by_thm(Q_eq)

    # Combine via IFF.
    from fusion import DEDUCT_ANTISYM_RULE, ASSUME
    th_fwd = MP(p.fact("fwd"), ASSUME(mk_eq(Q_ab, Q_cd)))   # {Q_ab=Q_cd} |- feq_abcd
    feq_abcd = mk_app(FEQ, a_t, b_t, c_t, d_t)
    th_rev = MP(p.fact("rev"), ASSUME(feq_abcd))            # {feq_abcd} |- Q_ab=Q_cd
    # DEDUCT_ANTISYM(th_rev, th_fwd) yields |- (Q a b = Q c d) = feq a b c d.
    iff_th = DEDUCT_ANTISYM_RULE(th_rev, th_fwd)
    p.thus("(Q a b = Q c d) = feq a b c d").by_thm(iff_th)


# A frequent shorthand: from (Q a b = Q c d) extract feq a b c d, and v.v.
def Q_eq_to_feq(th):
    """ |- Q a b = Q c d  ==>  |- feq a b c d. """
    from basics import dest_eq
    Q_ab, Q_cd = dest_eq(th._concl)
    a_t = Q_ab.fun.arg; b_t = Q_ab.arg
    c_t = Q_cd.fun.arg; d_t = Q_cd.arg
    eq_th = SPECL([a_t, b_t, c_t, d_t], RAT_EQ)
    return EQ_MP(eq_th, th)


def feq_to_Q_eq(th):
    """ |- feq a b c d  ==>  |- Q a b = Q c d. """
    from basics import rator, rand
    # th concl = feq a b c d = ((feq a) b c) d.
    fcd = rator(th._concl)            # feq a b c
    fc  = rator(fcd)                  # feq a b
    fa  = rator(fc)                   # feq a
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
_R_TYPES = {"X": rat_ty, "Y": rat_ty, "Z": rat_ty,
            "U": rat_ty, "V": rat_ty, "W": rat_ty}


@proof
def IS_RAT_DEST(p):
    p.goal("!X. IS_RAT (dest_rat X)", types=_R_TYPES)
    p.fix("X")
    X_t = p._parse("X")
    # mk_rat (dest_rat X) = X  (MK_RAT_DEST instantiated).
    a_var = Var("a", rat_ty)
    md_X = INST([(X_t, a_var)], MK_RAT_DEST)
    # |- mk_rat (dest_rat X) = X.
    # dest_rat applied to both sides:
    dest_md = AP_TERM(dest_rat, md_X)
    # |- dest_rat (mk_rat (dest_rat X)) = dest_rat X.
    # RAT_DEST_MK at r := dest_rat X:
    dr_X = mk_comb(dest_rat, X_t)
    iso_inst = INST([(dr_X, _r_n2b)], RAT_DEST_MK)
    # |- IS_RAT (dest_rat X) = (dest_rat (mk_rat (dest_rat X)) = dest_rat X).
    p.thus("IS_RAT (dest_rat X)").by_eq_mp(SYM(iso_inst), dest_md)


@proof
def Q_SURJ(p):
    p.goal("!X. ?a b. X = Q a b", types=_R_TYPES)
    p.fix("X")
    X_t = p._parse("X")
    p.have("isr: IS_RAT (dest_rat X)").by_match(IS_RAT_DEST)
    # Unfold: ?pa pb. dest_rat X = feq pa pb.
    dr_X = mk_comb(dest_rat, X_t)
    unfold_th = UNFOLD(IS_RAT_DEF, dr_X)   # |- IS_RAT (dest_rat X) = ?pa pb. dest_rat X = feq pa pb
    p.have("ex: ?pa pb. dest_rat X = feq pa pb") \
        .by_eq_mp(unfold_th, "isr")
    p.choose("pa: ?pb. dest_rat X = feq pa pb", from_="ex")
    p.choose("pb: dest_rat X = feq pa pb", from_="pa_eq")
    # Now we have pb_eq: |- dest_rat X = feq pa pb.
    pb_eq = p.fact("pb_eq")
    # Apply mk_rat: mk_rat (dest_rat X) = mk_rat (feq pa pb).
    mk_eq_th = AP_TERM(mk_rat, pb_eq)
    # mk_rat (dest_rat X) = X.
    a_var = Var("a", rat_ty)
    md_X = INST([(X_t, a_var)], MK_RAT_DEST)
    # mk_rat (feq pa pb) = Q pa pb (by SYM of Q_DEF unfolded).
    pa_t = p._parse("pa"); pb_t = p._parse("pb")
    Q_unfold = UNFOLD(Q_DEF, pa_t, pb_t)   # |- Q pa pb = mk_rat (feq pa pb).
    # Combine: X = mk_rat (dest_rat X) = mk_rat (feq pa pb) = Q pa pb.
    X_eq = TRANS_CHAIN([SYM(md_X), mk_eq_th, SYM(Q_unfold)])
    p.have("Xpapb: X = Q pa pb").by_thm(X_eq)
    # Build nested existentials manually (with fresh bound names).
    pa_w = p._parse("pa"); pb_w = p._parse("pb")
    inner = EXISTS(
        mk_abs(_pb, mk_eq(X_t, mk_app(Q, pa_w, _pb))),
        pb_w, p.fact("Xpapb"))
    outer = EXISTS(
        mk_abs(_pa, mk_exists(_pb, mk_eq(X_t, mk_app(Q, _pa, _pb)))),
        pa_w, inner)
    p.thus("?a b. X = Q a b").by_thm(outer)


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
    p.thus("X = Z").by_thm(TRANS(p.fact("h1"), p.fact("h2")))


# ---------------------------------------------------------------------------
# §5 Part 2.  Definitions 18, 19 and order on rat.
#
#   X > Y  iff for some (every) representatives a/b of X, c/d of Y,
#           the fraction-level fgt a b c d holds.
#
# We use the existential form (the well-definedness Satz 44 ensures that
# "for some" coincides with "for every").
# ---------------------------------------------------------------------------

RGT_DEF = define("rgt", "rat -> rat -> bool",
    "\\X:rat Y:rat. ?a b c d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d",
    infix=(40, "non"))
RGT = mk_const("rgt", [])

RLT_DEF = define("rlt", "rat -> rat -> bool",
    "\\X:rat Y:rat. ?a b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d",
    infix=(40, "non"))
RLT = mk_const("rlt", [])


# Connection lemma: for any representatives, fgt at the fraction level lifts to
# rgt at the rat level (and vice versa).
@proof
def RGT_INTRO(p):
    p.goal("!a b c d. fgt a b c d ==> rgt (Q a b) (Q c d)")
    p.fix("a b c d")
    p.assume("hgt: fgt a b c d")
    a_t = p._parse("a"); b_t = p._parse("b")
    c_t = p._parse("c"); d_t = p._parse("d")
    Q_ab = mk_app(Q, a_t, b_t)
    Q_cd = mk_app(Q, c_t, d_t)
    refl_ab = REFL(Q_ab)        # |- Q a b = Q a b
    refl_cd = REFL(Q_cd)        # |- Q c d = Q c d
    # Combined: Q a b = Q a b /\ Q c d = Q c d /\ fgt a b c d.
    body_inner = CONJ(refl_ab, CONJ(refl_cd, p.fact("hgt")))
    # Build existentials: ?a' b' c' d'. Q a b = Q a' b' /\ Q c d = Q c' d' /\ fgt a' b' c' d'.
    _qa = Var("qa", num_ty); _qb = Var("qb", num_ty)
    _qc = Var("qc", num_ty); _qd = Var("qd", num_ty)
    inner_d = EXISTS(
        mk_abs(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, c_t, _qd)),
                   mk_app(FGT, a_t, b_t, c_t, _qd)))),
        d_t, body_inner)
    inner_c = EXISTS(
        mk_abs(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FGT, a_t, b_t, _qc, _qd))))),
        c_t, inner_d)
    inner_b = EXISTS(
        mk_abs(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FGT, a_t, _qb, _qc, _qd)))))),
        b_t, inner_c)
    inner_a = EXISTS(
        mk_abs(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FGT, _qa, _qb, _qc, _qd))))))),
        a_t, inner_b)
    # |- ?a' b' c' d'. (Q a b = Q a' b') /\ (Q c d = Q c' d') /\ fgt a' b' c' d'.
    # Bridge to rgt (Q a b) (Q c d).
    rgt_unfold = UNFOLD(RGT_DEF, Q_ab, Q_cd)
    p.thus("rgt (Q a b) (Q c d)").by_eq_mp(SYM(rgt_unfold), inner_a)


@proof
def RLT_INTRO(p):
    p.goal("!a b c d. flt a b c d ==> rlt (Q a b) (Q c d)")
    p.fix("a b c d")
    p.assume("hlt: flt a b c d")
    a_t = p._parse("a"); b_t = p._parse("b")
    c_t = p._parse("c"); d_t = p._parse("d")
    Q_ab = mk_app(Q, a_t, b_t)
    Q_cd = mk_app(Q, c_t, d_t)
    body_inner = CONJ(REFL(Q_ab), CONJ(REFL(Q_cd), p.fact("hlt")))
    _qa = Var("qa", num_ty); _qb = Var("qb", num_ty)
    _qc = Var("qc", num_ty); _qd = Var("qd", num_ty)
    inner_d = EXISTS(
        mk_abs(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, c_t, _qd)),
                   mk_app(FLT, a_t, b_t, c_t, _qd)))),
        d_t, body_inner)
    inner_c = EXISTS(
        mk_abs(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FLT, a_t, b_t, _qc, _qd))))),
        c_t, inner_d)
    inner_b = EXISTS(
        mk_abs(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FLT, a_t, _qb, _qc, _qd)))))),
        b_t, inner_c)
    inner_a = EXISTS(
        mk_abs(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_app(FLT, _qa, _qb, _qc, _qd))))))),
        a_t, inner_b)
    rlt_unfold = UNFOLD(RLT_DEF, Q_ab, Q_cd)
    p.thus("rlt (Q a b) (Q c d)").by_eq_mp(SYM(rlt_unfold), inner_a)


# Elimination: from rgt X Y, choose representatives a, b, c, d with X = Q a b,
# Y = Q c d, and fgt a b c d. (Used in subsequent proofs.)
# This is conceptually the dual of RGT_INTRO; we'll use ``p.choose`` patterns
# inline in the proofs that need it rather than creating a standalone form.


# Satz 81 (trichotomy):  X = Y \/ rgt X Y \/ rlt X Y.
@proof
def SATZ_81(p):
    p.goal("!X Y. X = Y \\/ rgt X Y \\/ rlt X Y", types=_R_TYPES)
    p.fix("X Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="eX")
    p.choose("b: X = Q a b", from_="a_eq")
    p.choose("c: ?b. Y = Q c b", from_="eY")
    p.choose("d: Y = Q c d", from_="c_eq")
    # Trichotomy at fraction level.
    p.have("tri: feq a b c d \\/ fgt a b c d \\/ flt a b c d") \
        .by_match(SATZ_41)
    with p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by_cases("tri"):
        with p.case("e: feq a b c d"):
            # X = Q a b = Q c d = Y.
            Qab_eq_Qcd = feq_to_Q_eq(p.fact("e"))   # |- Q a b = Q c d
            X_eq_Y = TRANS_CHAIN([
                p.fact("b_eq"),       # X = Q a b
                Qab_eq_Qcd,           # Q a b = Q c d
                SYM(p.fact("d_eq"))   # Q c d = Y
            ])
            p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by(DISJ1, X_eq_Y, "rgt X Y \\/ rlt X Y")
        with p.case("g: fgt a b c d"):
            p.have("rg: rgt (Q a b) (Q c d)").by_match(RGT_INTRO, "g")
            # rgt X Y via X = Q a b, Y = Q c d substitution.
            sub1 = AP_TERM(RGT, p.fact("b_eq"))    # rgt X = rgt (Q a b)
            sub2 = AP_THM(sub1, p._parse("Q c d"))  # rgt X (Q c d) = rgt (Q a b) (Q c d)
            sub3 = AP_TERM(mk_app(RGT, p._parse("X")), p.fact("d_eq"))  # rgt X Y = rgt X (Q c d)
            sub_full = TRANS(sub3, sub2)            # |- rgt X Y = rgt (Q a b) (Q c d)
            p.have("rgXY: rgt X Y").by_eq_mp(SYM(sub_full), "rg")
            p.have("orMid: rgt X Y \\/ rlt X Y").by(DISJ1, "rgXY", "rlt X Y")
            p.thus("X = Y \\/ rgt X Y \\/ rlt X Y").by(DISJ2, "X = Y", "orMid")
        with p.case("l: flt a b c d"):
            p.have("rl: rlt (Q a b) (Q c d)").by_match(RLT_INTRO, "l")
            sub1 = AP_TERM(RLT, p.fact("b_eq"))
            sub2 = AP_THM(sub1, p._parse("Q c d"))
            sub3 = AP_TERM(mk_app(RLT, p._parse("X")), p.fact("d_eq"))
            sub_full = TRANS(sub3, sub2)
            p.have("rlXY: rlt X Y").by_eq_mp(SYM(sub_full), "rl")
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
    X_t = p._parse("X"); Y_t = p._parse("Y")
    # Unfold rgt to existential.
    p.have("ex0: ?a b c d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d") \
        .by_eq_mp(UNFOLD(RGT_DEF, X_t, Y_t), "h")
    p.choose("a: ?b c d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="ex0")
    p.choose("b: ?c d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="a_eq")
    p.choose("c: ?d. X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="b_eq")
    p.choose("d: X = Q a b /\\ Y = Q c d /\\ fgt a b c d", from_="c_eq")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hgt)")
    p.have("flt: flt c d a b").by_match(SATZ_42, "hgt")
    p.have("rl_QcdQab: rlt (Q c d) (Q a b)").by_match(RLT_INTRO, "flt")
    # rlt Y X = rlt (Q c d) (Q a b) via hY, hX.
    sub_l = AP_TERM(RLT, p.fact("hY"))                       # rlt Y = rlt (Q c d)
    sub_l2 = AP_THM(sub_l, p._parse("Q a b"))                 # rlt Y (Q a b) = rlt (Q c d) (Q a b)
    sub_r = AP_TERM(mk_app(RLT, Y_t), p.fact("hX"))           # rlt Y X = rlt Y (Q a b)
    sub_full = TRANS(sub_r, sub_l2)
    p.thus("rlt Y X").by_eq_mp(SYM(sub_full), "rl_QcdQab")


# Satz 83:  rlt X Y ==> rgt Y X.
@proof
def SATZ_83(p):
    p.goal("!X Y. rlt X Y ==> rgt Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rlt X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("ex0: ?a b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d") \
        .by_eq_mp(UNFOLD(RLT_DEF, X_t, Y_t), "h")
    p.choose("a: ?b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="ex0")
    p.choose("b: ?c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="a_eq")
    p.choose("c: ?d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="b_eq")
    p.choose("d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="c_eq")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hlt)")
    p.have("fgt: fgt c d a b").by_match(SATZ_43, "hlt")
    p.have("rg_QcdQab: rgt (Q c d) (Q a b)").by_match(RGT_INTRO, "fgt")
    sub_l = AP_TERM(RGT, p.fact("hY"))
    sub_l2 = AP_THM(sub_l, p._parse("Q a b"))
    sub_r = AP_TERM(mk_app(RGT, Y_t), p.fact("hX"))
    sub_full = TRANS(sub_r, sub_l2)
    p.thus("rgt Y X").by_eq_mp(SYM(sub_full), "rg_QcdQab")


# Definition 20 / 21:  >= and <= on rat.
RGE_DEF = define("rge", "rat -> rat -> bool",
    "\\X:rat Y:rat. rgt X Y \\/ X = Y", infix=(40, "non"))
RGE = mk_const("rge", [])

RLE_DEF = define("rle", "rat -> rat -> bool",
    "\\X:rat Y:rat. rlt X Y \\/ X = Y", infix=(40, "non"))
RLE = mk_const("rle", [])


# Satz 84:  rge X Y ==> rle Y X.
@proof
def SATZ_84(p):
    p.goal("!X Y. rge X Y ==> rle Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rge X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("disj: rgt X Y \\/ X = Y") \
        .by_eq_mp(UNFOLD(RGE_DEF, X_t, Y_t), "h")
    with p.thus("rle Y X").by_cases("disj"):
        with p.case("g: rgt X Y"):
            p.have("l: rlt Y X").by_match(SATZ_82, "g")
            p.have("orL: rlt Y X \\/ Y = X").by(DISJ1, "l", "Y = X")
            p.thus("rle Y X").by_eq_mp(SYM(UNFOLD(RLE_DEF, Y_t, X_t)), "orL")
        with p.case("e: X = Y"):
            p.have("eYX: Y = X").by_thm(SYM(p.fact("e")))
            p.have("orR: rlt Y X \\/ Y = X").by(DISJ2, "rlt Y X", "eYX")
            p.thus("rle Y X").by_eq_mp(SYM(UNFOLD(RLE_DEF, Y_t, X_t)), "orR")


# Satz 85:  rle X Y ==> rge Y X.
@proof
def SATZ_85(p):
    p.goal("!X Y. rle X Y ==> rge Y X", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rle X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("disj: rlt X Y \\/ X = Y") \
        .by_eq_mp(UNFOLD(RLE_DEF, X_t, Y_t), "h")
    with p.thus("rge Y X").by_cases("disj"):
        with p.case("l: rlt X Y"):
            p.have("g: rgt Y X").by_match(SATZ_83, "l")
            p.have("orL: rgt Y X \\/ Y = X").by(DISJ1, "g", "Y = X")
            p.thus("rge Y X").by_eq_mp(SYM(UNFOLD(RGE_DEF, Y_t, X_t)), "orL")
        with p.case("e: X = Y"):
            p.have("eYX: Y = X").by_thm(SYM(p.fact("e")))
            p.have("orR: rgt Y X \\/ Y = X").by(DISJ2, "rgt Y X", "eYX")
            p.thus("rge Y X").by_eq_mp(SYM(UNFOLD(RGE_DEF, Y_t, X_t)), "orR")


# Satz 86 (transitivity of <):  rlt X Y, rlt Y Z ==> rlt X Z.
@proof
def SATZ_86(p):
    p.goal("!X Y Z. rlt X Y ==> rlt Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h1: rlt X Y", "h2: rlt Y Z")
    X_t = p._parse("X"); Y_t = p._parse("Y"); Z_t = p._parse("Z")
    p.have("ex1: ?a b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d") \
        .by_eq_mp(UNFOLD(RLT_DEF, X_t, Y_t), "h1")
    p.choose("a: ?b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="ex1")
    p.choose("b: ?c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="a_eq")
    p.choose("c: ?d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="b_eq")
    p.choose("d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="c_eq")
    p.split("d_eq", "(hX, t1)")
    p.split("t1", "(hY1, hlt1)")
    # For the second hypothesis, we need a copy of Y's representation; it's
    # consistent with hY1, but the (e, f) representatives of Z are fresh.
    p.have("ex2: ?p q e f. Y = Q p q /\\ Z = Q e f /\\ flt p q e f") \
        .by_eq_mp(UNFOLD(RLT_DEF, Y_t, Z_t), "h2")
    p.choose("e1: ?q e f. Y = Q e1 q /\\ Z = Q e f /\\ flt e1 q e f", from_="ex2")
    p.choose("f1: ?e f. Y = Q e1 f1 /\\ Z = Q e f /\\ flt e1 f1 e f", from_="e1_eq")
    p.choose("g1: ?f. Y = Q e1 f1 /\\ Z = Q g1 f /\\ flt e1 f1 g1 f", from_="f1_eq")
    p.choose("h1n: Y = Q e1 f1 /\\ Z = Q g1 h1n /\\ flt e1 f1 g1 h1n", from_="g1_eq")
    p.split("h1n_eq", "(hY2, t2)")
    p.split("t2", "(hZ, hlt2)")
    # Y = Q c d = Q e1 f1 ; so Q c d = Q e1 f1, hence feq c d e1 f1.
    p.have("Qcd_eq_Qe1f1: Q c d = Q e1 f1") \
        .by_thm(TRANS(SYM(p.fact("hY1")), p.fact("hY2")))
    feq_cd_e1f1 = Q_eq_to_feq(p.fact("Qcd_eq_Qe1f1"))
    p.have("feq_eq: feq c d e1 f1").by_thm(feq_cd_e1f1)
    # SATZ_45: flt a b c d ==> feq a b c d ==> feq c d e f ==> flt e f e' f'.
    # Actually SATZ_45 is: flt x1 x2 y1 y2, feq x1 x2 z1 z2, feq y1 y2 u1 u2 ==> flt z1 z2 u1 u2.
    # We need a transit through (a, b)/(c, d) → use flt a b c d, transition c d → e1 f1 → flt a b e1 f1.
    # flt c d g1 h1n combined with feq e1 f1 c d (= sym of feq_eq) gives flt e1 f1 g1 h1n? No,
    # we have flt e1 f1 g1 h1n (hlt2). Transition e1 f1 → c d uses feq e1 f1 c d (from feq_eq).
    p.have("feq_e1f1_cd: feq e1 f1 c d").by_match(SATZ_38, "feq_eq")
    # SATZ_45: flt e1 f1 g1 h1n /\ feq e1 f1 c d /\ feq g1 h1n g1 h1n ==> flt c d g1 h1n.
    p.have("refl_gh: feq g1 h1n g1 h1n").by_match(SATZ_37)
    p.have("flt_cd_gh: flt c d g1 h1n") \
        .by_match(SATZ_45, "hlt2", "feq_e1f1_cd", "refl_gh")
    # Now combine flt a b c d (hlt1) and flt c d g1 h1n (flt_cd_gh) via SATZ_50.
    p.have("flt_ab_gh: flt a b g1 h1n").by_match(SATZ_50, "hlt1", "flt_cd_gh")
    # Lift to rlt (Q a b) (Q g1 h1n).
    p.have("rl: rlt (Q a b) (Q g1 h1n)").by_match(RLT_INTRO, "flt_ab_gh")
    # Bridge to rlt X Z via X = Q a b, Z = Q g1 h1n.
    sub_x = AP_TERM(RLT, p.fact("hX"))                          # rlt X = rlt (Q a b)
    sub_x2 = AP_THM(sub_x, p._parse("Q g1 h1n"))                  # rlt X (Q g1 h1n) = rlt (Q a b) (Q g1 h1n)
    sub_z = AP_TERM(mk_app(RLT, X_t), p.fact("hZ"))              # rlt X Z = rlt X (Q g1 h1n)
    sub_full = TRANS(sub_z, sub_x2)
    p.thus("rlt X Z").by_eq_mp(SYM(sub_full), "rl")


# Satz 89:  for any X there exists Z > X.
@proof
def SATZ_89(p):
    p.goal("!X. ?Z. rgt Z X", types=_R_TYPES)
    p.fix("X")
    p.have("ex: ?a b. X = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="ex")
    p.choose("b: X = Q a b", from_="a_eq")
    # Witness: Q (a+a) b. SATZ_53: fgt (x1+x1) x2 x1 x2.
    p.have("fg: fgt (a+a) b a b").by_match(SATZ_53)
    p.have("rg: rgt (Q (a+a) b) (Q a b)").by_match(RGT_INTRO, "fg")
    # rgt (Q (a+a) b) X via X = Q a b.
    Z_witness = p._parse("Q (a+a) b")
    X_t = p._parse("X")
    sub_l = AP_TERM(mk_app(RGT, Z_witness), p.fact("b_eq"))
    # |- rgt (Q (a+a) b) X = rgt (Q (a+a) b) (Q a b)
    p.have("rgZX: rgt (Q (a+a) b) X").by_eq_mp(SYM(sub_l), "rg")
    p.thus("?Z. rgt Z X").by_witness(Z_witness, "rgZX")


# Satz 90:  for any X there exists Z < X.
@proof
def SATZ_90(p):
    p.goal("!X. ?Z. rlt Z X", types=_R_TYPES)
    p.fix("X")
    p.have("ex: ?a b. X = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="ex")
    p.choose("b: X = Q a b", from_="a_eq")
    p.have("fl: flt a (b+b) a b").by_match(SATZ_54)
    p.have("rl: rlt (Q a (b+b)) (Q a b)").by_match(RLT_INTRO, "fl")
    Z_witness = p._parse("Q a (b+b)")
    sub_l = AP_TERM(mk_app(RLT, Z_witness), p.fact("b_eq"))
    p.have("rlZX: rlt (Q a (b+b)) X").by_eq_mp(SYM(sub_l), "rl")
    p.thus("?Z. rlt Z X").by_witness(Z_witness, "rlZX")


# Satz 87:  rle X Y /\ rlt Y Z  -or-  rlt X Y /\ rle Y Z  ==>  rlt X Z.
@proof
def SATZ_87A(p):
    p.goal("!X Y Z. rle X Y ==> rlt Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("hle: rle X Y", "hlt: rlt Y Z")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("disj: rlt X Y \\/ X = Y") \
        .by_eq_mp(UNFOLD(RLE_DEF, X_t, Y_t), "hle")
    with p.thus("rlt X Z").by_cases("disj"):
        with p.case("l: rlt X Y"):
            p.thus("rlt X Z").by_match(SATZ_86, "l", "hlt")
        with p.case("e: X = Y"):
            # rlt Y Z and X = Y => rlt X Z by substitution.
            sub = AP_TERM(RLT, p.fact("e"))   # rlt X = rlt Y
            sub2 = AP_THM(sub, p._parse("Z"))  # rlt X Z = rlt Y Z
            p.thus("rlt X Z").by_eq_mp(SYM(sub2), "hlt")


@proof
def SATZ_87B(p):
    p.goal("!X Y Z. rlt X Y ==> rle Y Z ==> rlt X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("hlt: rlt X Y", "hle: rle Y Z")
    Y_t = p._parse("Y"); Z_t = p._parse("Z")
    p.have("disj: rlt Y Z \\/ Y = Z") \
        .by_eq_mp(UNFOLD(RLE_DEF, Y_t, Z_t), "hle")
    with p.thus("rlt X Z").by_cases("disj"):
        with p.case("l: rlt Y Z"):
            p.thus("rlt X Z").by_match(SATZ_86, "hlt", "l")
        with p.case("e: Y = Z"):
            sub = AP_TERM(mk_app(RLT, p._parse("X")), p.fact("e"))
            # sub : |- rlt X Y = rlt X Z; forward EQ_MP from rlt X Y.
            p.thus("rlt X Z").by_eq_mp(sub, "hlt")


# Satz 88:  rle X Y /\ rle Y Z  ==>  rle X Z.
@proof
def SATZ_88(p):
    p.goal("!X Y Z. rle X Y ==> rle Y Z ==> rle X Z", types=_R_TYPES)
    p.fix("X Y Z")
    p.assume("h1: rle X Y", "h2: rle Y Z")
    X_t = p._parse("X"); Y_t = p._parse("Y"); Z_t = p._parse("Z")
    p.have("d1: rlt X Y \\/ X = Y") \
        .by_eq_mp(UNFOLD(RLE_DEF, X_t, Y_t), "h1")
    p.have("d2: rlt Y Z \\/ Y = Z") \
        .by_eq_mp(UNFOLD(RLE_DEF, Y_t, Z_t), "h2")
    with p.thus("rle X Z").by_cases("d1"):
        with p.case("l1: rlt X Y"):
            p.have("lt_XZ: rlt X Z").by_match(SATZ_87B, "l1", "h2")
            p.have("orL: rlt X Z \\/ X = Z").by(DISJ1, "lt_XZ", "X = Z")
            p.thus("rle X Z").by_eq_mp(SYM(UNFOLD(RLE_DEF, X_t, Z_t)), "orL")
        with p.case("e1: X = Y"):
            with p.thus("rle X Z").by_cases("d2"):
                with p.case("l2: rlt Y Z"):
                    sub = AP_TERM(RLT, p.fact("e1"))
                    sub2 = AP_THM(sub, Z_t)   # rlt X Z = rlt Y Z
                    p.have("lt_XZ: rlt X Z").by_eq_mp(SYM(sub2), "l2")
                    p.have("orL: rlt X Z \\/ X = Z").by(DISJ1, "lt_XZ", "X = Z")
                    p.thus("rle X Z").by_eq_mp(SYM(UNFOLD(RLE_DEF, X_t, Z_t)), "orL")
                with p.case("e2: Y = Z"):
                    p.have("eq_XZ: X = Z") \
                        .by_thm(TRANS(p.fact("e1"), p.fact("e2")))
                    p.have("orR: rlt X Z \\/ X = Z").by(DISJ2, "rlt X Z", "eq_XZ")
                    p.thus("rle X Z").by_eq_mp(SYM(UNFOLD(RLE_DEF, X_t, Z_t)), "orR")


# Satz 91 (density of rationals):  rlt X Y ==> ?Z. rlt X Z /\ rlt Z Y.
@proof
def SATZ_91(p):
    p.goal("!X Y. rlt X Y ==> ?Z. rlt X Z /\\ rlt Z Y", types=_R_TYPES)
    p.fix("X Y")
    p.assume("h: rlt X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("ex0: ?a b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d") \
        .by_eq_mp(UNFOLD(RLT_DEF, X_t, Y_t), "h")
    p.choose("a: ?b c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="ex0")
    p.choose("b: ?c d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="a_eq")
    p.choose("c: ?d. X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="b_eq")
    p.choose("d: X = Q a b /\\ Y = Q c d /\\ flt a b c d", from_="c_eq")
    p.split("d_eq", "(hX, h2)")
    p.split("h2", "(hY, hlt)")
    # Witness midpoint Q (a+c) (b+d).
    # Satz 55 gives flt a b (a+c) (b+d) /\ flt (a+c) (b+d) c d.
    # Actually Satz 55 returns the conjunction directly via ?-witness.
    # We use SATZ_55 statement: flt x1 x2 y1 y2 ==> ?z1 z2. flt x1 x2 z1 z2 /\ flt z1 z2 y1 y2.
    p.have("ex55: ?z1 z2. flt a b z1 z2 /\\ flt z1 z2 c d").by_match(SATZ_55, "hlt")
    p.choose("z1: ?z2. flt a b z1 z2 /\\ flt z1 z2 c d", from_="ex55")
    p.choose("z2: flt a b z1 z2 /\\ flt z1 z2 c d", from_="z1_eq")
    p.split("z2_eq", "(flt_a, flt_b)")
    p.have("rl1_QabQz: rlt (Q a b) (Q z1 z2)").by_match(RLT_INTRO, "flt_a")
    p.have("rl2_QzQcd: rlt (Q z1 z2) (Q c d)").by_match(RLT_INTRO, "flt_b")
    Z_witness = p._parse("Q z1 z2")
    # rlt X (Q z1 z2): use hX for X = Q a b.
    sub_x = AP_TERM(RLT, p.fact("hX"))             # rlt X = rlt (Q a b)
    sub_x2 = AP_THM(sub_x, Z_witness)               # rlt X (Q z1 z2) = rlt (Q a b) (Q z1 z2)
    p.have("rlt_XZ: rlt X (Q z1 z2)").by_eq_mp(SYM(sub_x2), "rl1_QabQz")
    sub_y = AP_TERM(mk_app(RLT, Z_witness), p.fact("hY"))   # rlt (Q z1 z2) Y = rlt (Q z1 z2) (Q c d)
    p.have("rlt_ZY: rlt (Q z1 z2) Y").by_eq_mp(SYM(sub_y), "rl2_QzQcd")
    p.have("conj: rlt X (Q z1 z2) /\\ rlt (Q z1 z2) Y").by(CONJ, "rlt_XZ", "rlt_ZY")
    p.thus("?Z. rlt X Z /\\ rlt Z Y").by_witness(Z_witness, "conj")


# ---------------------------------------------------------------------------
# §5 Part 3.  Definition 22 -- addition on rat.
#
#   X + Y := the unique class containing the sum of representatives.
# Operationally:
#   radd X Y := @Z. ?a b c d. X = Q a b /\ Y = Q c d /\ Z = Q (a*d + c*b) (b*d).
# ---------------------------------------------------------------------------

RADD_DEF = define("radd", "rat -> rat -> rat",
    "\\X:rat Y:rat. @Z:rat. ?a b c d. X = Q a b /\\ Y = Q c d "
    "/\\ Z = Q (a*d + c*b) (b*d)",
    infix=(50, "left"))
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
    a_t = p._parse("a"); b_t = p._parse("b")
    c_t = p._parse("c"); d_t = p._parse("d")
    Q_ab = mk_app(Q, a_t, b_t)
    Q_cd = mk_app(Q, c_t, d_t)
    canon = mk_app(Q, mk_add(mk_mul(a_t, d_t), mk_mul(c_t, b_t)),
                   mk_mul(b_t, d_t))
    radd_QQ = mk_app(RADD, Q_ab, Q_cd)
    # The predicate that radd-of-Q satisfies (after SELECT_AX): an existential
    # over a', b', c', d'.  Build the canonical-witness existential first, then
    # invoke SELECT_AX to get the same predicate at (@) of it.
    _qa = Var("qa", num_ty); _qb = Var("qb", num_ty)
    _qc = Var("qc", num_ty); _qd = Var("qd", num_ty)
    _qZ = Var("qZ", rat_ty)
    body_at_canon = CONJ(REFL(Q_ab), CONJ(REFL(Q_cd), REFL(canon)))
    # body_at_canon : |- Q a b = Q a b /\ Q c d = Q c d /\ canon = Q (a*d + c*b) (b*d).
    inner_d = EXISTS(
        mk_abs(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, c_t, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_add(mk_mul(a_t, _qd), mk_mul(c_t, b_t)),
                       mk_mul(b_t, _qd)))))),
        d_t, body_at_canon)
    inner_c = EXISTS(
        mk_abs(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_add(mk_mul(a_t, _qd), mk_mul(_qc, b_t)),
                       mk_mul(b_t, _qd))))))),
        c_t, inner_d)
    inner_b = EXISTS(
        mk_abs(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_add(mk_mul(a_t, _qd), mk_mul(_qc, _qb)),
                       mk_mul(_qb, _qd)))))))),
        b_t, inner_c)
    inner_a = EXISTS(
        mk_abs(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_add(mk_mul(_qa, _qd), mk_mul(_qc, _qb)),
                       mk_mul(_qb, _qd))))))))),
        a_t, inner_b)
    # inner_a : |- ?a' b' c' d'. Q a b = Q a' b' /\ Q c d = Q c' d'
    #              /\ canon = Q (a'*d'+c'*b') (b'*d').
    # Now: ?Z. Z = canon /\ ... — wait, we need to existentialize over Z too.
    # Wait, the @ predicate is `\Z. ?a' b' c' d'. ... /\ Z = Q (a'*d'+c'*b') (b'*d')`.
    # So `?Z. pred Z` is `?Z. ?a'b'c'd'. ... /\ Z = ...`. The Z existence at canon:
    pred_Z = mk_abs(_qZ, mk_exists(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
        mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
        mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
               mk_eq(_qZ, mk_app(Q,
                   mk_add(mk_mul(_qa, _qd), mk_mul(_qc, _qb)),
                   mk_mul(_qb, _qd))))))))))
    ex_Z = EXISTS(pred_Z, canon, inner_a)
    # CHOOSE_WITNESS gives pred_body[(@) pred_Z / Z] -- already beta-reduced.
    body_at_sel = CHOOSE_WITNESS(pred_Z, ex_Z)
    # body_at_sel : |- ?a' b' c' d'. Q a b = Q a' b' /\ Q c d = Q c' d'
    #                  /\ ((@) pred_Z) = Q (a'*d'+c'*b') (b'*d').
    # Rewrite ((@) pred_Z) → radd (Q a b) (Q c d) using SYM(radd_unfold).
    radd_unfold = UNFOLD(RADD_DEF, Q_ab, Q_cd)
    body_with_radd = REWRITE_RULE([SYM(radd_unfold)], body_at_sel)
    p.have("sel_body: ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
           " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)") \
        .by_thm(body_with_radd)
    p.choose("a1: ?b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)",
             from_="sel_body")
    p.choose("b1: ?c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)",
             from_="a1_eq")
    p.choose("c1: ?d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)",
             from_="b1_eq")
    p.choose("d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1)",
             from_="c1_eq")
    p.split("d1_eq", "(hQab, hrest)")
    p.split("hrest", "(hQcd, hradd)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    # Satz 56: feq (a*d + c*b) (b*d) (a1*d1 + c1*b1) (b1*d1).
    p.have("feq_sum: feq (a*d + c*b) (b*d) (a1*d1 + c1*b1) (b1*d1)") \
        .by_match(SATZ_56, "feq_ab", "feq_cd")
    p.have("Qsum: Q (a*d + c*b) (b*d) = Q (a1*d1 + c1*b1) (b1*d1)") \
        .by_thm(feq_to_Q_eq(p.fact("feq_sum")))
    # radd (Q a b) (Q c d) = Q (a1*d1 + c1*b1) (b1*d1) = Q (a*d + c*b) (b*d).
    p.thus("radd (Q a b) (Q c d) = Q (a*d + c*b) (b*d)") \
        .by_thm(TRANS(p.fact("hradd"), SYM(p.fact("Qsum"))))


# Helpers for lifting binary operations / relations on rat to representatives.
# `p_to_QQ` rewrites a goal/fact about ``op X Y`` where X = Q a b and Y = Q c d
# down to its ``op (Q a b) (Q c d)`` form, ready for RGT_INTRO/RADD_QQ etc.

def _bin_subst(p, op_const, hX, hY, X_t, Y_t):
    """ |- op X Y = op (Q a b) (Q c d), given hX : X = Q a b, hY : Y = Q c d. """
    sub_x = AP_TERM(op_const, hX)
    sub_x2 = AP_THM(sub_x, Y_t)              # |- op X Y = op (Q a b) Y
    sub_y = AP_TERM(mk_app(op_const, hX._concl.arg), hY)
    return TRANS(sub_x2, sub_y)


# Satz 92 (commutativity of rat addition):  X + Y = Y + X.
@proof
def SATZ_92(p):
    p.goal("!X Y. radd X Y = radd Y X", types=_R_TYPES)
    p.fix("X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="eX")
    p.choose("b: X = Q a b", from_="a_eq")
    p.choose("c: ?b. Y = Q c b", from_="eY")
    p.choose("d: Y = Q c d", from_="c_eq")
    # radd X Y = radd (Q a b) (Q c d) = Q (a*d + c*b) (b*d).
    sub_XY = _bin_subst(p, RADD, p.fact("b_eq"), p.fact("d_eq"), X_t, Y_t)
    radd_XY_eq_canon_LR = TRANS(sub_XY, SPECL(
        [p._parse("a"), p._parse("b"), p._parse("c"), p._parse("d")],
        RADD_QQ))
    # radd Y X = radd (Q c d) (Q a b) = Q (c*b + a*d) (d*b).
    sub_YX = _bin_subst(p, RADD, p.fact("d_eq"), p.fact("b_eq"), Y_t, X_t)
    radd_YX_eq_canon_RL = TRANS(sub_YX, SPECL(
        [p._parse("c"), p._parse("d"), p._parse("a"), p._parse("b")],
        RADD_QQ))
    # The two canonical forms are =-equal by Satz 58 (fraction-level commutativity).
    p.have("feq58: feq (a*d + c*b) (b*d) (c*b + a*d) (d*b)") \
        .by_match(SATZ_58)
    p.have("Qcomm: Q (a*d + c*b) (b*d) = Q (c*b + a*d) (d*b)") \
        .by_thm(feq_to_Q_eq(p.fact("feq58")))
    p.thus("radd X Y = radd Y X").by_thm(TRANS_CHAIN([
        radd_XY_eq_canon_LR,
        p.fact("Qcomm"),
        SYM(radd_YX_eq_canon_RL),
    ]))


# Satz 94:  X + Y > X.
@proof
def SATZ_94(p):
    p.goal("!X Y. rgt (radd X Y) X", types=_R_TYPES)
    p.fix("X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="eX")
    p.choose("b: X = Q a b", from_="a_eq")
    p.choose("c: ?b. Y = Q c b", from_="eY")
    p.choose("d: Y = Q c d", from_="c_eq")
    sub_XY = _bin_subst(p, RADD, p.fact("b_eq"), p.fact("d_eq"), X_t, Y_t)
    radd_eq_canon = TRANS(sub_XY, SPECL(
        [p._parse("a"), p._parse("b"), p._parse("c"), p._parse("d")],
        RADD_QQ))
    # radd_eq_canon : |- radd X Y = Q (a*d + c*b) (b*d).
    p.have("fg: fgt (a*d + c*b) (b*d) a b").by_match(SATZ_60)
    p.have("rg_canon: rgt (Q (a*d + c*b) (b*d)) (Q a b)") \
        .by_match(RGT_INTRO, "fg")
    # Bridge: rgt (radd X Y) X.
    sub_lhs = AP_TERM(RGT, radd_eq_canon)              # rgt (radd X Y) = rgt (Q (a*d+c*b) (b*d))
    sub_lhs2 = AP_THM(sub_lhs, p.fact("b_eq").rator(0)
                       if False else p._parse("X"))
    # We want rgt (radd X Y) X. Use SYM(sub_lhs) at Q a b: rgt (radd X Y) (Q a b)
    # rewriting back...
    # Simpler: rgt (radd X Y) X = rgt (Q (...)) (Q a b).
    sub_l = AP_TERM(RGT, radd_eq_canon)               # rgt (radd X Y) = rgt (Q (...))
    sub_l_at_X = AP_THM(sub_l, X_t)                   # rgt (radd X Y) X = rgt (Q (...)) X
    sub_r = AP_TERM(mk_app(RGT, mk_app(Q,
                p._parse("a*d + c*b"), p._parse("b*d"))), p.fact("b_eq"))
    # sub_r : rgt (Q (...)) X = rgt (Q (...)) (Q a b)
    full_eq = TRANS(sub_l_at_X, sub_r)
    p.thus("rgt (radd X Y) X").by_eq_mp(SYM(full_eq), "rg_canon")


# ---------------------------------------------------------------------------
# §5 Part 4.  Definition 24 -- multiplication on rat.
#
#   X * Y := the unique class containing the product of representatives.
# Operationally:
#   rmul X Y := @Z. ?a b c d. X = Q a b /\ Y = Q c d /\ Z = Q (a*c) (b*d).
# ---------------------------------------------------------------------------

RMUL_DEF = define("rmul", "rat -> rat -> rat",
    "\\X:rat Y:rat. @Z:rat. ?a b c d. X = Q a b /\\ Y = Q c d "
    "/\\ Z = Q (a*c) (b*d)",
    infix=(60, "left"))
RMUL = mk_const("rmul", [])


# Key canonical-form lemma (parallel to RADD_QQ):
#   rmul (Q a b) (Q c d) = Q (a*c) (b*d).
@proof
def RMUL_QQ(p):
    p.goal("!a b c d. rmul (Q a b) (Q c d) = Q (a*c) (b*d)")
    p.fix("a b c d")
    a_t = p._parse("a"); b_t = p._parse("b")
    c_t = p._parse("c"); d_t = p._parse("d")
    Q_ab = mk_app(Q, a_t, b_t)
    Q_cd = mk_app(Q, c_t, d_t)
    canon = mk_app(Q, mk_mul(a_t, c_t), mk_mul(b_t, d_t))
    _qa = Var("qa", num_ty); _qb = Var("qb", num_ty)
    _qc = Var("qc", num_ty); _qd = Var("qd", num_ty)
    _qZ = Var("qZ", rat_ty)
    body_at_canon = CONJ(REFL(Q_ab), CONJ(REFL(Q_cd), REFL(canon)))
    inner_d = EXISTS(
        mk_abs(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, c_t, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_mul(a_t, c_t), mk_mul(b_t, _qd)))))),
        d_t, body_at_canon)
    inner_c = EXISTS(
        mk_abs(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, b_t)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_mul(a_t, _qc), mk_mul(b_t, _qd))))))),
        c_t, inner_d)
    inner_b = EXISTS(
        mk_abs(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, a_t, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_mul(a_t, _qc), mk_mul(_qb, _qd)))))))),
        b_t, inner_c)
    inner_a = EXISTS(
        mk_abs(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
            mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
            mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
                   mk_eq(canon, mk_app(Q,
                       mk_mul(_qa, _qc), mk_mul(_qb, _qd))))))))),
        a_t, inner_b)
    pred_Z = mk_abs(_qZ, mk_exists(_qa, mk_exists(_qb, mk_exists(_qc, mk_exists(_qd,
        mk_and(mk_eq(Q_ab, mk_app(Q, _qa, _qb)),
        mk_and(mk_eq(Q_cd, mk_app(Q, _qc, _qd)),
               mk_eq(_qZ, mk_app(Q,
                   mk_mul(_qa, _qc), mk_mul(_qb, _qd))))))))))
    ex_Z = EXISTS(pred_Z, canon, inner_a)
    body_at_sel = CHOOSE_WITNESS(pred_Z, ex_Z)
    rmul_unfold = UNFOLD(RMUL_DEF, Q_ab, Q_cd)
    body_with_rmul = REWRITE_RULE([SYM(rmul_unfold)], body_at_sel)
    p.have("sel_body: ?a1 b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
           " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)") \
        .by_thm(body_with_rmul)
    p.choose("a1: ?b1 c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)", from_="sel_body")
    p.choose("b1: ?c1 d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)", from_="a1_eq")
    p.choose("c1: ?d1. Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)", from_="b1_eq")
    p.choose("d1: Q a b = Q a1 b1 /\\ Q c d = Q c1 d1"
             " /\\ rmul (Q a b) (Q c d) = Q (a1*c1) (b1*d1)", from_="c1_eq")
    p.split("d1_eq", "(hQab, hrest)")
    p.split("hrest", "(hQcd, hrmul)")
    p.have("feq_ab: feq a b a1 b1").by_thm(Q_eq_to_feq(p.fact("hQab")))
    p.have("feq_cd: feq c d c1 d1").by_thm(Q_eq_to_feq(p.fact("hQcd")))
    p.have("feq_prod: feq (a*c) (b*d) (a1*c1) (b1*d1)") \
        .by_match(SATZ_68, "feq_ab", "feq_cd")
    p.have("Qprod: Q (a*c) (b*d) = Q (a1*c1) (b1*d1)") \
        .by_thm(feq_to_Q_eq(p.fact("feq_prod")))
    p.thus("rmul (Q a b) (Q c d) = Q (a*c) (b*d)") \
        .by_thm(TRANS(p.fact("hrmul"), SYM(p.fact("Qprod"))))


# Satz 102 (commutativity of rat multiplication):  X * Y = Y * X.
@proof
def SATZ_102(p):
    p.goal("!X Y. rmul X Y = rmul Y X", types=_R_TYPES)
    p.fix("X Y")
    X_t = p._parse("X"); Y_t = p._parse("Y")
    p.have("eX: ?a b. X = Q a b").by_match(Q_SURJ)
    p.have("eY: ?a b. Y = Q a b").by_match(Q_SURJ)
    p.choose("a: ?b. X = Q a b", from_="eX")
    p.choose("b: X = Q a b", from_="a_eq")
    p.choose("c: ?b. Y = Q c b", from_="eY")
    p.choose("d: Y = Q c d", from_="c_eq")
    sub_XY = _bin_subst(p, RMUL, p.fact("b_eq"), p.fact("d_eq"), X_t, Y_t)
    rmul_XY = TRANS(sub_XY, SPECL(
        [p._parse("a"), p._parse("b"), p._parse("c"), p._parse("d")], RMUL_QQ))
    sub_YX = _bin_subst(p, RMUL, p.fact("d_eq"), p.fact("b_eq"), Y_t, X_t)
    rmul_YX = TRANS(sub_YX, SPECL(
        [p._parse("c"), p._parse("d"), p._parse("a"), p._parse("b")], RMUL_QQ))
    p.have("feq69: feq (a*c) (b*d) (c*a) (d*b)").by_match(SATZ_69)
    p.have("Qcomm: Q (a*c) (b*d) = Q (c*a) (d*b)") \
        .by_thm(feq_to_Q_eq(p.fact("feq69")))
    p.thus("rmul X Y = rmul Y X").by_thm(TRANS_CHAIN([
        rmul_XY, p.fact("Qcomm"), SYM(rmul_YX),
    ]))


# ---------------------------------------------------------------------------
# Remaining Sätze of Chapter 2 §5 (not formalised here):
#
#   Sätze 93, 95-101  -- associativity of +, monotonicity laws, subtraction
#                        (Definition 23). Each follows the "transport via
#                        Q-canonical-form, apply fraction-level Satz 59-67,
#                        re-Q" pattern shown above for Sätze 92, 94.
#   Sätze 103, 104, 105-110 -- associativity / distributivity / monotonicity
#                        of *, division existence (parallel to addition).
#   Satz 111-115, Definitions 25-27 -- integer-rationals subset, identification
#                        with naturals, division ``X/Y``, Satz 113 (integers
#                        satisfy the five Peano axioms).
#
# The infrastructure here (RAT_EQ, Q_SURJ, RGT_INTRO/RLT_INTRO, RADD_QQ,
# RMUL_QQ, the helper ``_bin_subst``) is sufficient to discharge each of the
# remaining lifts mechanically, in the same shape as Sätze 92, 94, 102 above.
# ---------------------------------------------------------------------------


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
    print("  SATZ_94:       ", pp_thm(SATZ_94))
    print("§5 §4 (multiplication):")
    print("  RMUL_QQ:       ", pp_thm(RMUL_QQ))
    print("  SATZ_102:      ", pp_thm(SATZ_102))
