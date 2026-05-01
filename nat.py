"""Formalisation of Landau's *Foundations of Analysis*, Chapter 1.

Module stack:
  ``fusion.py`` -- primitive HOL Light kernel.
  ``axioms.py`` -- bool definitions and the 3 logical axioms (ETA, SELECT, INFINITY).
  ``logic.py``  -- derived bool inference rules + Diaconescu's EM.
  ``num.py``    -- num carved from ind; Peano 3/4/5 derived as theorems;
                   INDUCT and NUM_RECURSION.
  ``nat.py``    -- this file: addition, multiplication, Landau Theorems 1-36.

The whole development rests on only the 3 logical axioms in axioms.py.
Each theorem is proved using only the 10 primitive inference rules
(REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE,
INST, INST_TYPE) plus rules imported from ``logic.py`` and ``num.py``.

Run ``python nat.py`` -- the kernel rejects any unsound step, so a clean
finish prints 20 step-confirmation lines and means every theorem is valid.

Coverage:
  #1  All 5 Peano axioms derived as theorems in num.py
      (Axiom 1 by typing; Axiom 2's existence by taking SUC as a total
      function; Axioms 3, 4, 5 from carving num out of ind via INFINITY_AX).
  #2  Theorems 1, 2, 3, 5, 6, 7, 8, 9 (both existence and mutual-exclusion
      halves of the trichotomy).  Definition 1 (addition): the recursion
      equations ADD_1, ADD_SUC are derived from NUM_RECURSION rather than
      admitted (Theorem 4's existence half is num.py's NUM_RECURSION;
      uniqueness half is ADD_UNIQUE).
  #3  Definitions 2, 3, 4, 5 and Theorems 10-17, 18, 19 (a/b/c), 20,
      21, 22 (a/b), 23, 24, 25, 26, 27.
  #4  Definition 6 (multiplication, parallel to Definition 1, equations
      MUL_1 and MUL_SUC likewise derived from NUM_RECURSION; uniqueness
      half MUL_UNIQUE) and Theorems 29, 30, 31, 32 (a/b/c), 33, 34, 35 (a/b), 36.
"""

from fusion import (
    Var, Comb, Abs,
    bool_ty, aty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    dest_eq, aconv, HolError,
    rator, rand,
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    hyp,
)
from axioms import (
    F,
    mk_and, mk_or, mk_imp, mk_forall, mk_exists, mk_not, mk_select,
)
from tactics import (
    AP_TERM, AP_THM, BETA_CONV, SYM, UNFOLD,
    SPEC, GEN, CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP,
    CONTR, NOT_ELIM, NOT_INTRO, NOT_CONST,
    DISJ1, DISJ2, DISJ_CASES,
    NE_SYM, REWRITE_NE, EXISTS,
    PROVE_HYP, ELIM_EX,
    SPECL, GENL, DISCHL, TRANS_CHAIN, CASE_OR,
    REWRITE_PROVE, REWRITE_RULE, REWRITE_CONV,
    AC_PROVE, AC_NORM, REWRITE_AC_PROVE,
)
from classical import EXCLUDED_MIDDLE, NOT_NOT_ELIM, NOT_EX_TO_FORALL_NOT
from num import (
    num_ty, ONE, SUC, mk_suc,
    x, y, z, u, v, w, P,
    AXIOM_3, AXIOM_4, INDUCTION, INDUCT,
    define_recursive,
)
from parser import parse, pp, define, pp_thm, DEFAULT_SIG
from proof import proof


# ---------------------------------------------------------------------------
# Theorem 1.   |- !x y. ~(x = y) ==> ~(x' = y')
# Proof (Landau): "Otherwise x' = y' would hold, hence by Axiom 4 x = y."
# Formally: contrapositive of Axiom 4.
# ---------------------------------------------------------------------------

@proof
def SATZ_1(p):
    p.goal("!x y. ~(x = y) ==> ~(SUC x = SUC y)")
    p.fix("x y")
    p.assume("hxy: ~(x = y)")
    with p.suppose("h: SUC x = SUC y"):
        p.have("xy: x = y").by(AXIOM_4, "x", "y", "h")
        p.have("imp: (x = y) ==> F").by(NOT_ELIM, "hxy")
        p.thus("F").by(MP, "imp", "xy")


# ---------------------------------------------------------------------------
# Theorem 2.   |- !x. ~(x' = x)
# Proof (Landau): induction on x.
#   I)  1' != 1 by Axiom 3.
#   II) From x' != x, Theorem 1 gives (x')' != x'.
# ---------------------------------------------------------------------------

@proof
def SATZ_2(p):
    p.goal("!x. ~(SUC x = x)")
    p.fix("x")
    with p.induction("x"):
        with p.base():
            p.thus("~(SUC 1 = 1)").by(AXIOM_3, "1")
        with p.step("IH"):
            p.thus("~(SUC (SUC x) = SUC x)").by(SATZ_1, "SUC x", "x", "IH")


# ---------------------------------------------------------------------------
# Theorem 3.   |- !x. ~(x = 1) ==> ?u. x = u'
# Proof (Landau): induction.  Trivial at x = 1 (the hypothesis is
#                 contradictory); in the step: at x' take u = x.
# ---------------------------------------------------------------------------

@proof
def SATZ_3(p):
    p.goal("!x. ~(x = 1) ==> ?u. x = SUC u")
    p.fix("x")
    with p.induction("x"):
        with p.base():
            p.assume("h: ~(1 = 1)")
            p.have("imp: (1 = 1) ==> F").by(NOT_ELIM, "h")
            p.absurd().by(MP, "imp", REFL(ONE))
        with p.step("IH"):
            p.assume("h: ~(SUC x = 1)")
            p.thus("?u. SUC x = SUC u").by_witness("x", REFL(mk_suc(x)))


# ---------------------------------------------------------------------------
# Theorem 4 / Definition 1.
#
# Landau proves: there is exactly one operation + : num x num -> num with
#   x + 1 = x'    and    x + y' = (x + y)'.
#
# Uniqueness follows by routine induction.  For existence, we use the
# primitive-recursion principle `NUM_RECURSION` proved in num.py:
#   |- !c h. ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
# Specialising at  c := SUC x,  h := \k a. SUC a,  yields a function fn
# with fn 1 = SUC x and fn (SUC y) = SUC (fn y).  Define
#   x + y := (@fn. fn 1 = SUC x /\ !n. fn (SUC n) = SUC (fn n)) y.
# Then ADD_1 and ADD_SUC become *theorems*.
# ---------------------------------------------------------------------------

_nnn = mk_fun_ty(num_ty, mk_fun_ty(num_ty, num_ty))
_k = Var("k", num_ty)
_a = Var("a", num_ty)

ADD_1, ADD_SUC = define_recursive(
    "+", _nnn, x,
    c = mk_suc(x),
    h = mk_abs(_k, mk_abs(_a, mk_suc(_a))),    # \k a. SUC a
    prec=50, assoc="left",
)
PLUS = mk_const("+", [])

def mk_add(a, b):
    return mk_comb(mk_comb(PLUS, a), b)

# Reversed orientation of ADD_1, used as a rewrite to canonicalize SUC into
# `+1`-form before AC reasoning.
ADD_1_REV = GEN(x, SYM(SPEC(x, ADD_1)))    # |- !x. SUC x = x + 1


# ---------------------------------------------------------------------------
# Theorem 4, Part A (uniqueness half).
# Landau: at fixed x, any two functions a_y, b_y satisfying  a_1 = x'  and
# a_{y'} = (a_y)'  agree on all y.  Routine induction on y.
#   ADD_UNIQUE :  |- !x f g.
#       f 1 = SUC x /\ (!y. f (SUC y) = SUC (f y)) /\
#       g 1 = SUC x /\ (!y. g (SUC y) = SUC (g y))
#       ==> !y. f y = g y.
# ---------------------------------------------------------------------------

_fn_ty = mk_fun_ty(num_ty, num_ty)

@proof
def ADD_UNIQUE(p):
    p.goal("!x f g. f 1 = SUC x /\\ (!y. f (SUC y) = SUC (f y)) /\\ "
                  "g 1 = SUC x /\\ (!y. g (SUC y) = SUC (g y)) "
                  "==> !y. f y = g y",
           types={"f": _fn_ty, "g": _fn_ty})
    p.fix("x f g")
    p.assume("h: f 1 = SUC x /\\ (!y. f (SUC y) = SUC (f y)) /\\ "
                "g 1 = SUC x /\\ (!y. g (SUC y) = SUC (g y))")
    p.split_conj("h", "h_f1", "h_fstep", "h_g1", "h_gstep")
    with p.induction("y"):
        with p.base():
            p.thus("f 1 = g 1").by_rewrite(["h_f1", "h_g1"])
        with p.step("IH"):
            p.thus("f (SUC y) = g (SUC y)")\
                .by_rewrite(["h_fstep", "h_gstep", "IH"])


# ---------------------------------------------------------------------------
# Theorem 5 (associative law of addition):
#   |- !x y z. (x + y) + z = x + (y + z).
# Proof (Landau): induction on z.
# ---------------------------------------------------------------------------

@proof
def SATZ_5(p):
    p.goal("!x y z. (x + y) + z = x + (y + z)")
    p.fix("x y z")
    with p.induction("z"):
        with p.base():
            p.thus("(x + y) + 1 = x + (y + 1)").by_rewrite([ADD_1, ADD_SUC])
        with p.step("IH"):
            p.thus("(x + y) + SUC z = x + (y + SUC z)")\
                .by_rewrite([ADD_SUC, "IH"])


# ---------------------------------------------------------------------------
# Helpers from "the construction in the proof of Theorem 4" -- facts about
# addition on the LEFT argument that are not part of Definition 1 directly.
#
# ONE_PLUS :  |- !y.    1 + y = SUC y
# SUC_PLUS :  |- !x y.  SUC x + y = SUC (x + y)
# ---------------------------------------------------------------------------

@proof
def ONE_PLUS(p):
    p.goal("!y. 1 + y = SUC y")
    p.fix("y")
    with p.induction("y"):
        with p.base():
            p.thus("1 + 1 = SUC 1").by_rewrite([ADD_1])
        with p.step("IH"):
            p.thus("1 + SUC y = SUC (SUC y)").by_rewrite([ADD_SUC, "IH"])

@proof
def SUC_PLUS(p):
    p.goal("!x y. SUC x + y = SUC (x + y)")
    p.fix("x y")
    with p.induction("y"):
        with p.base():
            p.thus("SUC x + 1 = SUC (x + 1)").by_rewrite([ADD_1])
        with p.step("IH"):
            p.thus("SUC x + SUC y = SUC (x + SUC y)")\
                .by_rewrite([ADD_SUC, "IH"])


# ---------------------------------------------------------------------------
# Theorem 6 (commutative law of addition):
#   |- !x y. x + y = y + x.
# Proof (Landau): induction on x with y fixed.
# ---------------------------------------------------------------------------

@proof
def SATZ_6(p):
    p.goal("!x y. x + y = y + x")
    p.fix("x y")
    with p.induction("x"):
        with p.base():
            p.thus("1 + y = y + 1").by_rewrite([ONE_PLUS, ADD_1])
        with p.step("IH"):
            p.thus("SUC x + y = y + SUC x")\
                .by_rewrite([SUC_PLUS, ADD_SUC, "IH"])


# AC-corollary used pervasively in the order proofs:  (a+b)+c = (a+c)+b.
@proof
def ADD_RIGHT_SWAP(p):
    p.goal("!a b c. (a + b) + c = (a + c) + b")
    p.fix("a b c")
    p.thus("(a + b) + c = (a + c) + b").by_ac(PLUS, SATZ_5, SATZ_6)


# ---------------------------------------------------------------------------
# Theorem 7.   |- !x y. ~(y = x + y).
# Proof (Landau): induction on y with x fixed.
#   I)  1 != x + 1, since x + 1 = x' and 1 != x'.
#   II) From y != x + y: y' != (x+y)' = x + y'  by Theorem 1 and ADD_SUC.
# ---------------------------------------------------------------------------

@proof
def SATZ_7(p):
    p.goal("!x y. ~(y = x + y)")
    p.fix("x y")
    with p.induction("y"):
        with p.base():
            p.have("ne_sx: ~(SUC x = 1)").by(AXIOM_3, "x")
            p.have("ne1: ~(1 = SUC x)").by(NE_SYM, "ne_sx")
            p.thus("~(1 = x + 1)")\
                .by_rewrite_ne("ne1", [REFL(ONE), SYM(SPEC(x, ADD_1))])
        with p.step("IH"):
            p.have("ne_succ: ~(SUC y = SUC (x + y))")\
                .by(SATZ_1, "y", "x + y", "IH")
            p.thus("~(SUC y = x + SUC y)")\
                .by_rewrite_ne("ne_succ",
                               [REFL(mk_suc(y)), SYM(SPECL([x, y], ADD_SUC))])


# ---------------------------------------------------------------------------
# Theorem 8.   |- !x y z. ~(y = z) ==> ~(x + y = x + z).
# Proof (Landau): induction on x with y, z fixed and y != z.
# ---------------------------------------------------------------------------

@proof
def SATZ_8(p):
    p.goal("!x y z. ~(y = z) ==> ~(x + y = x + z)")
    p.fix("x y z")
    p.assume("hyp_yz: ~(y = z)")
    with p.induction("x"):
        with p.base():
            p.have("ne_suc: ~(SUC y = SUC z)").by(SATZ_1, "y", "z", "hyp_yz")
            p.thus("~(1 + y = 1 + z)")\
                .by_rewrite_ne("ne_suc",
                               [SYM(SPEC(y, ONE_PLUS)), SYM(SPEC(z, ONE_PLUS))])
        with p.step("IH"):
            p.have("ne_sum: ~(SUC (x + y) = SUC (x + z))")\
                .by(SATZ_1, "x + y", "x + z", "IH")
            p.thus("~(SUC x + y = SUC x + z)")\
                .by_rewrite_ne("ne_sum",
                               [SYM(SPECL([x, y], SUC_PLUS)),
                                SYM(SPECL([x, z], SUC_PLUS))])


# ---------------------------------------------------------------------------
# Helper:  |- !x. (x = 1) \/ (?u. x = u').
# Every natural number is either 1 or the successor of some natural number.
# This is the "M = {1} u {x : ?u. x = u'}" lemma underpinning Landau's
# proof of Theorem 3 -- restated as a clean disjunction for use in Theorem 9.
# ---------------------------------------------------------------------------

@proof
def LEMMA_PRED(p):
    p.goal("!x. (x = 1) \\/ (?u. x = SUC u)")
    p.fix("x")
    with p.induction("x"):
        with p.base():
            p.have("e: 1 = 1").by_thm(REFL(ONE))
            p.thus("(1 = 1) \\/ (?u. 1 = SUC u)").by_disj("e")
        with p.step("IH"):
            p.have("ex: ?u. SUC x = SUC u")\
                .by_witness("x", REFL(mk_suc(x)))
            p.thus("(SUC x = 1) \\/ (?u. SUC x = SUC u)").by_disj("ex")


# ---------------------------------------------------------------------------
# Theorem 9.   |- !x y. (x = y) \/ (?u. x = y + u) \/ (?v. y = x + v).
#
# Landau states "exactly one"; part B (existence of at least one case)
# is proved here.  Part A (mutual exclusion) is left unproved.
# Together they would give the trichotomy in full strength.
#
# Proof B (Landau): induction on y with x fixed.
# ---------------------------------------------------------------------------

@proof
def SATZ_9(p):
    p.goal("!x y. (x = y) \\/ (?u. x = y + u) \\/ (?v. y = x + v)")
    p.fix("x y")
    with p.induction("y"):
        with p.base():
            with p.cases_on(LEMMA_PRED, "x"):
                with p.case("hx1: x = 1"):
                    p.thus("(x = 1) \\/ (?u. x = 1 + u) \\/ (?v. 1 = x + v)")\
                        .by_disj("hx1")
                with p.case("hxs: ?u. x = SUC u"):
                    p.have("eq: x = 1 + u").by_rewrite(["u_eq", ONE_PLUS])
                    p.have("ex: ?u. x = 1 + u").by_witness("u", "eq")
                    p.thus("(x = 1) \\/ (?u. x = 1 + u) \\/ (?v. 1 = x + v)")\
                        .by_disj("ex")
        with p.step("IH"):
            with p.cases_on("IH"):
                with p.case("h_eq: x = y"):
                    p.have("eq: SUC y = x + 1").by_rewrite(["h_eq", ADD_1])
                    p.have("ex: ?v. SUC y = x + v").by_witness("1", "eq")
                    p.thus("(x = SUC y) \\/ (?u. x = SUC y + u) "
                           "\\/ (?v. SUC y = x + v)").by_disj("ex")
                with p.case("h_gt: ?u. x = y + u"):
                    with p.cases_on(LEMMA_PRED, "u"):
                        with p.case("u_is_1: u = 1"):
                            p.have("eq: x = SUC y")\
                                .by_rewrite(["u_eq", "u_is_1", ADD_1])
                            p.thus("(x = SUC y) \\/ (?u. x = SUC y + u) "
                                   "\\/ (?v. SUC y = x + v)").by_disj("eq")
                        with p.case("u_succ: ?w. u = SUC w"):
                            p.have("eq: x = SUC y + w")\
                                .by_rewrite(["u_eq", "w_eq",
                                             ADD_SUC, SUC_PLUS])
                            p.have("ex: ?u. x = SUC y + u")\
                                .by_witness("w", "eq")
                            p.thus("(x = SUC y) \\/ (?u. x = SUC y + u) "
                                   "\\/ (?v. SUC y = x + v)").by_disj("ex")
                with p.case("h_lt: ?v. y = x + v"):
                    p.have("eq: SUC y = x + SUC v").by_rewrite(["v_eq", ADD_SUC])
                    p.have("ex: ?v. SUC y = x + v").by_witness("SUC v", "eq")
                    p.thus("(x = SUC y) \\/ (?u. x = SUC y + u) "
                           "\\/ (?v. SUC y = x + v)").by_disj("ex")


# ---------------------------------------------------------------------------
# #3 -- Ordnung
# ---------------------------------------------------------------------------

# Definition 2:  x > y  ≡  ?u. x = y + u
# Definition 3:  x < y  ≡  ?v. y = x + v
# ---------------------------------------------------------------------------

_nnb = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))

GT_DEF = define(">", _nnb, "\\x y. ?u. x = y + u", prec=40, assoc="non")
LT_DEF = define("<", _nnb, "\\x y. ?v. y = x + v", prec=40, assoc="non")

GT = mk_const(">", [])
LT = mk_const("<", [])

def mk_gt(a, b): return mk_comb(mk_comb(GT, a), b)
def mk_lt(a, b): return mk_comb(mk_comb(LT, a), b)

def UNFOLD_GT(a, b):
    """ |- (a > b) = (?u. a = b + u) """
    return UNFOLD(GT_DEF, a, b)

def UNFOLD_LT(a, b):
    """ |- (a < b) = (?v. b = a + v) """
    return UNFOLD(LT_DEF, a, b)

# Register with the proof DSL so `p.choose(name, from_=label)` accepts a fact
# whose conclusion is `> ` or `<`.
from proof import register_unfolder, register_disj_unfolder
register_unfolder(">", UNFOLD_GT)
register_unfolder("<", UNFOLD_LT)

def CHOOSE_GT(h_gt, body_fn):
    """h_gt : ... |- a > b.  Calls body_fn(eq, witness) with
       eq : ... |- a = b + witness.  Returns body_fn's result with the
       existential discharged."""
    a_t = rand(rator(h_gt._concl))
    b_t = rand(h_gt._concl)
    ex = EQ_MP(UNFOLD_GT(a_t, b_t), h_gt)
    pred = parse("\\u. ${a} = ${b} + u", a=a_t, b=b_t)
    return PROVE_HYP(ex, ELIM_EX(pred, ex._concl,
                                  lambda eq: body_fn(eq, rand(rand(eq._concl)))))


def CHOOSE_LT(h_lt, body_fn):
    """h_lt : ... |- a < b.  Calls body_fn(eq, witness) with
       eq : ... |- b = a + witness."""
    a_t = rand(rator(h_lt._concl))
    b_t = rand(h_lt._concl)
    ex = EQ_MP(UNFOLD_LT(a_t, b_t), h_lt)
    pred = parse("\\v. ${b} = ${a} + v", a=a_t, b=b_t)
    return PROVE_HYP(ex, ELIM_EX(pred, ex._concl,
                                  lambda eq: body_fn(eq, rand(rand(eq._concl)))))


# Theorem 10:  |- !x y. (x = y) \/ (x > y) \/ (x < y).    By Theorem 9 + Definitions 2, 3.

@proof
def SATZ_10(p):
    p.goal("!x y. (x = y) \\/ (x > y) \\/ (x < y)")
    p.fix("x y")
    p.thus("(x = y) \\/ (x > y) \\/ (x < y)")\
        .by_unfold(SPECL([x, y], SATZ_9), GT_DEF, LT_DEF)


# Theorem 11:  |- !x y. (x > y) ==> (y < x).   Both sides unfold to ?u. x = y + u.
# Theorem 12:  |- !x y. (x < y) ==> (y > x).   Symmetric.

@proof
def SATZ_11(p):
    p.goal("!x y. x > y ==> y < x")
    p.fix("x y")
    p.assume("h: x > y")
    p.have("ex: ?u. x = y + u").by_eq_mp(UNFOLD_GT(x, y), "h")
    p.thus("y < x").by_fold("ex")

@proof
def SATZ_12(p):
    p.goal("!x y. x < y ==> y > x")
    p.fix("x y")
    p.assume("h: x < y")
    p.have("ex: ?v. y = x + v").by_eq_mp(UNFOLD_LT(x, y), "h")
    p.thus("y > x").by_fold("ex")


# Definition 4:  x >= y  ≡  x > y \/ x = y.
# Definition 5:  x <= y  ≡  x < y \/ x = y.

GE_DEF = define(">=", _nnb, "\\x y. x > y \\/ x = y", prec=40, assoc="non")
LE_DEF = define("<=", _nnb, "\\x y. x < y \\/ x = y", prec=40, assoc="non")

GE = mk_const(">=", [])
LE = mk_const("<=", [])

def mk_ge(a, b): return mk_comb(mk_comb(GE, a), b)
def mk_le(a, b): return mk_comb(mk_comb(LE, a), b)

def UNFOLD_GE(a, b): return UNFOLD(GE_DEF, a, b)
def UNFOLD_LE(a, b): return UNFOLD(LE_DEF, a, b)

register_disj_unfolder(">=", UNFOLD_GE)
register_disj_unfolder("<=", UNFOLD_LE)


# Theorem 13:  |- !x y. (x >= y) ==> (y <= x).
# Theorem 14:  |- !x y. (x <= y) ==> (y >= x).

@proof
def SATZ_13(p):
    p.goal("!x y. x >= y ==> y <= x")
    p.fix("x y")
    p.assume("h: x >= y")
    with p.have("yx_or: (y < x) \\/ (y = x)").by_cases("h"):
        with p.case("h_gt: x > y"):
            p.have("yx_lt: y < x").by(SATZ_11, "x", "y", "h_gt")
            p.thus("(y < x) \\/ (y = x)").by_disj("yx_lt")
        with p.case("h_eq: x = y"):
            p.have("yx_eq: y = x").by(SYM, "h_eq")
            p.thus("(y < x) \\/ (y = x)").by_disj("yx_eq")
    p.thus("y <= x").by_fold("yx_or")


@proof
def SATZ_14(p):
    p.goal("!x y. x <= y ==> y >= x")
    p.fix("x y")
    p.assume("h: x <= y")
    with p.have("yx_or: (y > x) \\/ (y = x)").by_cases("h"):
        with p.case("h_lt: x < y"):
            p.have("yx_gt: y > x").by(SATZ_12, "x", "y", "h_lt")
            p.thus("(y > x) \\/ (y = x)").by_disj("yx_gt")
        with p.case("h_eq: x = y"):
            p.have("yx_eq: y = x").by(SYM, "h_eq")
            p.thus("(y > x) \\/ (y = x)").by_disj("yx_eq")
    p.thus("y >= x").by_fold("yx_or")


# Theorem 15 (transitivity of order):  |- !x y z. x < y ==> y < z ==> x < z.

@proof
def SATZ_15(p):
    p.goal("!x y z. x < y ==> y < z ==> x < z")
    p.fix("x y z")
    p.assume("hxy: x < y", "hyz: y < z")
    p.choose("v: y = x + v", from_="hxy")
    p.choose("w: z = y + w", from_="hyz")
    p.have("eq: z = x + (v + w)").by_rewrite(["w_eq", "v_eq", SATZ_5])
    p.thus("x < z").by_witness("v + w", "eq")


# Helpers turning < / = into <= and the analogues, used pervasively in #3.

def LT_TO_LE(th_lt):
    a = rand(rator(th_lt._concl)); b = rand(th_lt._concl)
    return EQ_MP(SYM(UNFOLD_LE(a, b)), DISJ1(th_lt, mk_eq(a, b)))

def EQ_TO_LE(th_eq):
    a, b = dest_eq(th_eq._concl)
    return EQ_MP(SYM(UNFOLD_LE(a, b)), DISJ2(mk_lt(a, b), th_eq))

def GT_TO_GE(th_gt):
    a = rand(rator(th_gt._concl)); b = rand(th_gt._concl)
    return EQ_MP(SYM(UNFOLD_GE(a, b)), DISJ1(th_gt, mk_eq(a, b)))

def EQ_TO_GE(th_eq):
    a, b = dest_eq(th_eq._concl)
    return EQ_MP(SYM(UNFOLD_GE(a, b)), DISJ2(mk_gt(a, b), th_eq))


# Theorem 16:   x <= y, y < z  =>  x < z   ;   x < y, y <= z  =>  x < z.
# We prove both forms (Landau's "or" is a disjunctive hypothesis).

@proof
def SATZ_16A(p):
    """ x <= y, y < z ==> x < z """
    p.goal("!x y z. x <= y ==> y < z ==> x < z")
    p.fix("x y z")
    p.assume("hxy: x <= y", "hyz: y < z")
    with p.cases_on("hxy"):
        with p.case("x < y"):
            p.thus("x < z").by(SATZ_15, "x", "y", "z", -1, "hyz")
        with p.case("x = y"):
            p.thus("x < z").by_rewrite_of("hyz", [SYM(p.fact(-1))])

@proof
def SATZ_16B(p):
    """ x < y, y <= z ==> x < z """
    p.goal("!x y z. x < y ==> y <= z ==> x < z")
    p.fix("x y z")
    p.assume("hxy: x < y", "hyz: y <= z")
    with p.cases_on("hyz"):
        with p.case("y < z"):
            p.thus("x < z").by(SATZ_15, "x", "y", "z", "hxy", -1)
        with p.case("y = z"):
            p.thus("x < z").by_rewrite_of("hxy", [-1])


# Theorem 17:   x <= y, y <= z  =>  x <= z.

@proof
def SATZ_17(p):
    p.goal("!x y z. x <= y ==> y <= z ==> x <= z")
    p.fix("x y z")
    p.assume("hxy: x <= y", "hyz: y <= z")
    with p.cases_on("hyz"):
        with p.case("y < z"):
            p.have("xz_lt: x < z").by(SATZ_16A, "x", "y", "z", "hxy", -1)
            p.thus("x <= z").by(LT_TO_LE, "xz_lt")
        with p.case("y = z"):
            p.thus("x <= z").by_rewrite_of("hxy", [-1])


# Theorem 18:  |- !x y. x + y > x.    Witness y in ?u. x+y = x+u.

@proof
def SATZ_18(p):
    p.goal("!x y. x + y > x")
    p.fix("x y")
    p.thus("x + y > x").by_witness("y", REFL(mk_add(x, y)))


# Theorem 19 (in three pieces -- Landau states it via "respectively"):
#   19a:  x > y      ==>  x + z > y + z
#   19b:  x = y      ==>  x + z = y + z
#   19c:  x < y      ==>  x + z < y + z

@proof
def SATZ_19A(p):
    p.goal("!x y z. x > y ==> x + z > y + z")
    p.fix("x y z")
    p.assume("h: x > y")
    p.choose("u: x = y + u", from_="h")
    p.have("eq: x + z = (y + z) + u")\
        .by_rewrite_ac(["u_eq"], PLUS, SATZ_5, SATZ_6)
    p.thus("x + z > y + z").by_witness("u", "eq")

@proof
def SATZ_19B(p):
    p.goal("!x y z. x = y ==> x + z = y + z")
    p.fix("x y z")
    p.assume("h: x = y")
    p.thus("x + z = y + z").by_rewrite(["h"])

@proof
def SATZ_19C(p):
    p.goal("!x y z. x < y ==> x + z < y + z")
    p.fix("x y z")
    p.assume("h: x < y")
    p.have("yx_gt: y > x").by(SATZ_12, "x", "y", "h")
    p.have("yz_gt_xz: y + z > x + z").by(SATZ_19A, "y", "x", "z", "yx_gt")
    p.thus("x + z < y + z").by(SATZ_11, "y + z", "x + z", "yz_gt_xz")


# Theorem 21:   x > y, z > u  ==>  x + z > y + u.
# Proof: x+z > y+z (Theorem 19a) and y+z > y+u (Theorem 19a w/ commutativity).

@proof
def SATZ_21(p):
    p.goal("!x y z u. x > y ==> z > u ==> x + z > y + u")
    p.fix("x y z u")
    p.assume("hxy: x > y", "hzu: z > u")
    p.have("xz_gt_yz: x + z > y + z").by(SATZ_19A, "x", "y", "z", "hxy")
    p.have("zy_gt_uy: z + y > u + y").by(SATZ_19A, "z", "u", "y", "hzu")
    p.have("yz_gt_yu: y + z > y + u")\
        .by_rewrite_of("zy_gt_uy",
                       [SPECL([z, y], SATZ_6), SPECL([u, y], SATZ_6)])
    p.have("yu_lt_yz: y + u < y + z").by(SATZ_11, "y + z", "y + u", "yz_gt_yu")
    p.have("yz_lt_xz: y + z < x + z").by(SATZ_11, "x + z", "y + z", "xz_gt_yz")
    p.have("yu_lt_xz: y + u < x + z")\
        .by(SATZ_15, "y + u", "y + z", "x + z", "yu_lt_yz", "yz_lt_xz")
    p.thus("x + z > y + u").by(SATZ_12, "y + u", "x + z", "yu_lt_xz")


# Theorem 22:   x >= y, z > u  ==>  x + z > y + u   (and the other "or" form).

@proof
def SATZ_22A(p):
    p.goal("!x y z u. x >= y ==> z > u ==> x + z > y + u")
    p.fix("x y z u")
    p.assume("hge: x >= y", "hgt: z > u")
    with p.cases_on("hge"):
        with p.case("x > y"):
            p.thus("x + z > y + u").by(SATZ_21, "x", "y", "z", "u", -1, "hgt")
        with p.case("hxy: x = y"):
            p.have("zy_gt_uy: z + y > u + y").by(SATZ_19A, "z", "u", "y", "hgt")
            p.have("yz_gt_yu: y + z > y + u")\
                .by_rewrite_of("zy_gt_uy",
                               [SPECL([z, y], SATZ_6), SPECL([u, y], SATZ_6)])
            p.thus("x + z > y + u").by_rewrite_of(
                "yz_gt_yu",
                [AP_THM(AP_TERM(PLUS, SYM(p.fact("hxy"))), z)])

@proof
def SATZ_22B(p):
    p.goal("!x y z u. x > y ==> z >= u ==> x + z > y + u")
    p.fix("x y z u")
    p.assume("hgt: x > y", "hge: z >= u")
    with p.cases_on("hge"):
        with p.case("z > u"):
            p.thus("x + z > y + u").by(SATZ_21, "x", "y", "z", "u", "hgt", -1)
        with p.case("hzu: z = u"):
            p.have("xz_gt_yz: x + z > y + z").by(SATZ_19A, "x", "y", "z", "hgt")
            p.thus("x + z > y + u").by_rewrite_of(
                "xz_gt_yz",
                [AP_TERM(mk_comb(PLUS, y), p.fact("hzu"))])


# Theorem 23:   x >= y, z >= u  ==>  x + z >= y + u.

@proof
def SATZ_23(p):
    p.goal("!x y z u. x >= y ==> z >= u ==> x + z >= y + u")
    p.fix("x y z u")
    p.assume("hxy: x >= y", "hzu: z >= u")
    with p.cases_on("hxy"):
        with p.case("hgt_xy: x > y"):
            p.have("gt: x + z > y + u").by(SATZ_22B, "x", "y", "z", "u",
                                            "hgt_xy", "hzu")
            p.thus("x + z >= y + u").by(GT_TO_GE, "gt")
        with p.case("heq_xy: x = y"):
            with p.cases_on("hzu"):
                with p.case("hgt_zu: z > u"):
                    p.have("gt: x + z > y + u").by(SATZ_22A, "x", "y", "z", "u",
                                                    "hxy", "hgt_zu")
                    p.thus("x + z >= y + u").by(GT_TO_GE, "gt")
                with p.case("heq_zu: z = u"):
                    p.have("eq: x + z = y + u").by_rewrite(["heq_xy", "heq_zu"])
                    p.thus("x + z >= y + u").by(EQ_TO_GE, "eq")


# Theorem 24:  |- !x. x >= 1.    Either x = 1 or x = u' = u + 1 > 1.

@proof
def SATZ_24(p):
    p.goal("!x. x >= 1")
    p.fix("x")
    p.have("lp: (x = 1) \\/ (?u. x = SUC u)").by(LEMMA_PRED, "x")
    with p.cases_on("lp"):
        with p.case("hx1: x = 1"):
            p.thus("x >= 1").by(EQ_TO_GE, "hx1")
        with p.case("hex: ?u. x = SUC u"):
            p.have("eq: x = 1 + u").by_rewrite(["u_eq", ONE_PLUS])
            p.have("gt1: x > 1").by_witness("u", "eq")
            p.thus("x >= 1").by(GT_TO_GE, "gt1")


# Theorem 25:   y > x  ==>  y >= x + 1.
# Proof: y = x + u, u >= 1, so y = x + u >= x + 1 (Theorem 23).

@proof
def SATZ_25(p):
    p.goal("!x y. y > x ==> y >= x + 1")
    p.fix("x y")
    p.assume("h: y > x")
    p.choose("u: y = x + u", from_="h")
    p.have("u_ge_1: u >= 1").by(SATZ_24, "u")
    p.have("sum_ge: x + u >= x + 1")\
        .by(SATZ_23, "x", "x", "u", "1", EQ_TO_GE(REFL(x)), "u_ge_1")
    p.thus("y >= x + 1").by_rewrite_of("sum_ge", [SYM(p.fact("u_eq"))])


# ---------------------------------------------------------------------------
# Contradiction helpers used by Theorems 26, 20, 33 (and Theorem 9 part A).
# Each builds F from a pair of inconsistent order facts, via Theorem 7 + 6.
# ---------------------------------------------------------------------------

def CONTRA_LT_GT(a_t, b_t, h_lt, h_gt):
    """ |- a < b,  |- a > b   =>   {a<b, a>b} |- F. """
    def _inner_v(eq_v, v0):
        def _inner_u(eq_u, u0):
            # Avoid rewriter loop (eq_v↔eq_u cycle): chain eq_v then rewrite RHS only.
            rhs_eq = REWRITE_PROVE([eq_u, SATZ_5],
                          parse("${a} + ${v0} = ${b} + (${u0} + ${v0})",
                                a=a_t, b=b_t, u0=u0, v0=v0))
            chain = TRANS(eq_v, rhs_eq)               # b = b + (u0+v0)
            ne   = SPECL([mk_add(u0, v0), b_t], SATZ_7)
            ne_f = REWRITE_NE(ne, REFL(b_t), SPECL([mk_add(u0, v0), b_t], SATZ_6))
            return MP(NOT_ELIM(ne_f), chain)
        return CHOOSE_GT(h_gt, _inner_u)
    return CHOOSE_LT(h_lt, _inner_v)


def CONTRA_LT_EQ(a_t, b_t, h_lt, h_eq):
    """ |- a < b,  |- a = b   =>   F. """
    th_bb = EQ_MP(MK_COMB(AP_TERM(LT, h_eq), REFL(b_t)), h_lt)
    def _inner(eq, v0):
        comm = SPECL([v0, b_t], SATZ_6)
        ne   = SPECL([v0, b_t], SATZ_7)
        ne_f = REWRITE_NE(ne, REFL(b_t), comm)
        return MP(NOT_ELIM(ne_f), eq)
    return CHOOSE_LT(th_bb, _inner)


def CONTRA_GT_EQ(a_t, b_t, h_gt, h_eq):
    """ |- a > b,  |- a = b   =>   F. """
    def _inner(eq_a, u0):
        chain = TRANS(SYM(h_eq), eq_a)                       # b = b + u0
        comm = SPECL([u0, b_t], SATZ_6)
        ne   = SPECL([u0, b_t], SATZ_7)
        ne_f = REWRITE_NE(ne, REFL(b_t), comm)
        return MP(NOT_ELIM(ne_f), chain)
    return CHOOSE_GT(h_gt, _inner)


# Wire the three contradictions into the proof DSL so call sites can use
# ``p.absurd().auto(h1, h2)`` instead of naming the lemma. Each finder
# extracts the term pair from its order fact; equality facts are accepted in
# either orientation (the finder applies SYM if needed).
from proof import register_contra_finder

def _dest_op(t):
    return rator(rator(t)), rand(rator(t)), rand(t)

def _contra_lt_gt(h_lt, h_gt):
    _, a, b = _dest_op(h_lt._concl)
    return CONTRA_LT_GT(a, b, h_lt, h_gt)

def _orient_eq(h_eq, a, b):
    l, r = dest_eq(h_eq._concl)
    if aconv(l, a) and aconv(r, b):
        return h_eq
    if aconv(l, b) and aconv(r, a):
        return SYM(h_eq)
    raise HolError(
        f"absurd.auto: equality {pp(h_eq._concl)} does not relate "
        f"{pp(a)} and {pp(b)}")

def _contra_lt_eq(h_lt, h_eq):
    _, a, b = _dest_op(h_lt._concl)
    return CONTRA_LT_EQ(a, b, h_lt, _orient_eq(h_eq, a, b))

def _contra_gt_eq(h_gt, h_eq):
    _, a, b = _dest_op(h_gt._concl)
    return CONTRA_GT_EQ(a, b, h_gt, _orient_eq(h_eq, a, b))

register_contra_finder("<", ">", _contra_lt_gt)
register_contra_finder("<", "=", _contra_lt_eq)
register_contra_finder(">", "=", _contra_gt_eq)


# Theorem 26:   y < x + 1  ==>  y <= x.    Contrapositive of Theorem 25.
# Landau: "Otherwise we'd have y > x, hence by Theorem 25 y >= x + 1."
# We prove it via Theorem 9 (trichotomy): if y > x, then y >= x + 1, contradicting y < x + 1.
# Otherwise y = x or y < x, both giving y <= x.

@proof
def SATZ_26(p):
    p.goal("!x y. y < x + 1 ==> y <= x")
    p.fix("x y")
    p.assume("h: y < x + 1")
    with p.cases_on(SATZ_10, "y", "x"):
        with p.case("h_eq: y = x"):
            p.thus("y <= x").by(EQ_TO_LE, "h_eq")
        with p.case("h_gt: y > x"):
            p.have("y_ge_x1: y >= x + 1").by(SATZ_25, "x", "y", "h_gt")
            with p.cases_on("y_ge_x1"):
                with p.case("h_g: y > x + 1"):
                    p.absurd().auto("h", "h_g")
                with p.case("h_e: y = x + 1"):
                    p.absurd().auto("h", "h_e")
        with p.case("h_lt: y < x"):
            p.thus("y <= x").by(LT_TO_LE, "h_lt")




# ---------------------------------------------------------------------------
# Theorem 27 (well-ordering).
#   |- !N. (?n. N n) ==> ?m. N m /\ (!k. N k ==> m <= k).
#
# Proof (Landau): let M(x) := !n. N n ==> x <= n.  Then 1 ∈ M (Theorem 24).
# For y ∈ N, y+1 ∉ M (since y+1 > y by Theorem 18).  Hence not every x ∈ M;
# so by Axiom 5 there is some m ∈ M with m+1 ∉ M.  Such m is ≤ every n ∈ N
# (since m ∈ M); and m ∈ N (else m < n for all n ∈ N, hence m+1 ≤ n by
# Theorem 25, hence m+1 ∈ M).  Both clauses of the conclusion follow.
# ---------------------------------------------------------------------------

_N_ty = mk_fun_ty(num_ty, bool_ty)
_N_var = Var("N", _N_ty)


# Sub-lemma for SATZ_27 (Step 2). Stated in unfolded M-form: if y is in N then
# the predicate ``M(y+1) := !n. N n ==> y+1 <= n`` cannot hold (would give
# ``y+1 <= y`` contradicting ``y+1 > y``). Used inside _prove_satz_27 with a
# BETA bridge to switch between the unfolded form and ``M_pred (y+1)``.

@proof
def _SATZ_27_NOT_M_SUCC(p):
    p.goal("!N y. N y ==> ~(!n. N n ==> y + 1 <= n)",
           types={"N": _N_ty})
    p.fix("N y")
    p.assume("hNy: N y")
    with p.suppose("hM: !n. N n ==> y + 1 <= n"):
        p.have("le: y + 1 <= y").by("hM", "y", "hNy")
        p.have("gt: y + 1 > y").by(SATZ_18, "y", "1")
        with p.cases_on("le"):
            with p.case("h_lt: y + 1 < y"):
                p.absurd().auto("h_lt", "gt")
            with p.case("h_eq: y + 1 = y"):
                p.absurd().auto("gt", "h_eq")


# Sub-lemma for SATZ_27 (Step 3). Generic well-ordering kernel: if a
# predicate ``P`` holds at 1, fails at the successor of every element of N,
# and N is non-empty, then there is some boundary ``m`` with ``P m`` and
# ``~ P (m+1)``.  This is the abstract content of Landau's Step 3.
# Proof: by contradiction. If no such m exists then ``!x. ~(P x /\\ ~P(x+1))``,
# which gives ``!x. P x ==> P (x+1)`` and (by induction on x in SUC form,
# bridged by ADD_1) ``!x. P x``. Pick n in N, then P(n+1) holds, contradicting
# ``hStepFail`` at y := n.

@proof
def _SATZ_27_EXISTS_M(p):
    p.goal("!P N. P 1 ==> "
           "(!y. N y ==> ~ P (y + 1)) ==> "
           "(?n. N n) ==> "
           "?m. P m /\\ ~ P (m + 1)",
           types={"P": _N_ty, "N": _N_ty})
    p.fix("P N")
    p.assume("hP1: P 1")
    p.assume("hStepFail: !y. N y ==> ~ P (y + 1)")
    p.assume("hNonempty: ?n. N n")
    with p.thus("?m. P m /\\ ~ P (m + 1)").by_cases(
            EXCLUDED_MIDDLE, "?m. P m /\\ ~ P (m + 1)"):
        with p.case("hex: ?m. P m /\\ ~ P (m + 1)"):
            p.thus("?m. P m /\\ ~ P (m + 1)").by_thm(p.fact("hex"))
        with p.case("hnex: ~ (?m. P m /\\ ~ P (m + 1))"):
            pred_Q = p._parse("\\x. P x /\\ ~ P (x + 1)")
            p.have("forall_nQ: !x. ~(P x /\\ ~ P (x + 1))")\
                .by_thm(NOT_EX_TO_FORALL_NOT(p.fact("hnex"), pred_Q))
            with p.have("forall_P: !x. P x").proof():
                with p.induction("x"):
                    with p.base():
                        p.thus("P 1").by_thm(p.fact("hP1"))
                    with p.step("IH"):
                        with p.cases_on(EXCLUDED_MIDDLE, "P (SUC x)"):
                            with p.case("hPS: P (SUC x)"):
                                p.thus("P (SUC x)").by_thm(p.fact("hPS"))
                            with p.case("hnPS: ~ P (SUC x)"):
                                p.have("hnP1: ~ P (x + 1)")\
                                    .by_rewrite_of("hnPS", [SYM(SPEC(x, ADD_1))])
                                p.have("conj: P x /\\ ~ P (x + 1)")\
                                    .by(CONJ, "IH", "hnP1")
                                p.have("not_conj: ~(P x /\\ ~ P (x + 1))")\
                                    .by("forall_nQ", "x")
                                p.absurd().by_conj("conj", "not_conj")
            p.choose("n0: N n0", from_="hNonempty")
            p.have("Pn1: P (n0 + 1)").by("forall_P", "n0 + 1")
            p.have("nPn1: ~ P (n0 + 1)").by("hStepFail", "n0", "n0_eq")
            p.absurd().by_conj("Pn1", "nPn1")


# Sub-lemma for SATZ_27 (Step 4). Given M(m) (= !n. N n ==> m <= n) and
# ~M(m+1) (= ~(!n. N n ==> m+1 <= n)), deduce that m itself satisfies
# ``N m /\ (!k. N k ==> m <= k)`` — i.e., m is the witness we need.
# Proof: the right conjunct is just M(m) renamed; for the left, suppose ~N m,
# then for each n in N we have m <= n and m != n (else N m), hence m < n,
# hence m+1 <= n (Sätze 12, 25, 13). That builds M(m+1), contradicting ~M(m+1).

@proof
def _SATZ_27_FROM_M(p):
    p.goal("!N m. (!n. N n ==> m <= n) ==> "
           "~(!n. N n ==> m + 1 <= n) ==> "
           "N m /\\ (!k. N k ==> m <= k)",
           types={"N": _N_ty})
    p.fix("N m")
    p.assume("hM: !n. N n ==> m <= n")
    p.assume("hnM1: ~(!n. N n ==> m + 1 <= n)")
    with p.have("Nm: N m").by_cases(EXCLUDED_MIDDLE, "N m"):
        with p.case("hN: N m"):
            p.thus("N m").by_thm(p.fact("hN"))
        with p.case("hnN: ~ N m"):
            with p.have("M_m1: !n. N n ==> m + 1 <= n").proof():
                p.fix("n")
                p.assume("hNn: N n")
                p.have("le: m <= n").by("hM", "n", "hNn")
                with p.have("ne: ~ (m = n)").proof():
                    with p.suppose("eq: m = n"):
                        p.have("Nm_via: N m")\
                            .by_rewrite_of("hNn", [SYM(p.fact("eq"))])
                        p.absurd().by_conj("Nm_via", "hnN")
                with p.have("lt: m < n").by_cases("le"):
                    with p.case("h_lt: m < n"):
                        p.thus("m < n").by_thm(p.fact("h_lt"))
                    with p.case("h_eq: m = n"):
                        p.absurd().by_conj("h_eq", "ne")
                p.have("gt: n > m").by(SATZ_12, "m", "n", "lt")
                p.have("ge: n >= m + 1").by(SATZ_25, "m", "n", "gt")
                p.thus("m + 1 <= n").by(SATZ_13, "n", "m + 1", "ge")
            p.absurd().by_conj("M_m1", "hnM1")
    p.thus("N m /\\ (!k. N k ==> m <= k)").by(CONJ, "Nm", "hM")


# Theorem 27 (well-ordering). Direct port of Landau's argument: introduce the
# schematic predicate ``M(x) := !n. N n ==> x <= n`` via ``p.let``, build M(1),
# show M fails at successors of N-elements, invoke the abstract well-ordering
# kernel _SATZ_27_EXISTS_M to get a boundary m, then conclude via _SATZ_27_FROM_M.
# Eager substitution at parse time means ``M m`` and the unfolded body share the
# same kernel term, so no BETA-bridge plumbing is needed at the boundaries.

@proof
def SATZ_27(p):
    p.goal("!N. (?n. N n) ==> (?m. N m /\\ (!k. N k ==> m <= k))",
           types={"N": _N_ty})
    p.fix("N")
    p.assume("hNonempty: ?n. N n")
    p.let("M(x) := !n. N n ==> x <= n")

    # Step 1: M 1, i.e. !n. N n ==> 1 <= n. Under the lazy let the
    # sub-frame goal mentions ``M 1`` in folded form (not a forall), so
    # we prove the unfolded body explicitly and refold via fold_let.
    with p.have("M_1_body: !n. N n ==> 1 <= n").proof():
        p.fix("n")
        p.assume("hNn: N n")
        p.have("ge1: n >= 1").by(SATZ_24, "n")
        p.thus("1 <= n").by(SATZ_13, "n", "1", "ge1")
    p.have("M_1: M 1").by_eq_mp(p.fold_let("M", ONE), "M_1_body")

    # Step 2: !y. N y ==> ~ M (y + 1).  _SATZ_27_NOT_M_SUCC is stated in the
    # unfolded form, which is exactly what ``M (y + 1)`` parses to via the let.
    p.have("step_fail: !y. N y ==> ~ M (y + 1)")\
        .by(_SATZ_27_NOT_M_SUCC, "N")

    # Step 3: ?m. M m /\ ~ M (m + 1).  _SATZ_27_EXISTS_M takes a higher-order
    # predicate P; by_select materializes the let `M` as a kernel lambda for
    # the SPEC, BETA_RULE-normalizes the resulting redexes back to the unfolded
    # form, then MPs the premise facts.
    p.have("ex: ?m. M m /\\ ~ M (m + 1)")\
        .by_select(_SATZ_27_EXISTS_M, "M", "N",
                    "M_1", "step_fail", "hNonempty")

    # Step 4: choose the boundary witness, decompose, conclude via _SATZ_27_FROM_M.
    p.choose("m: M m /\\ ~ M (m + 1)", from_="ex")
    p.split_conj("m_eq", "Mm", "nMm1")
    p.have("conj: N m /\\ (!k. N k ==> m <= k)")\
        .by(_SATZ_27_FROM_M, "N", "m", "Mm", "nMm1")
    p.thus("?m. N m /\\ (!k. N k ==> m <= k)")\
        .by_witness("m", "conj")


# ---------------------------------------------------------------------------
# #4 -- Multiplikation
# ---------------------------------------------------------------------------
#
# Following Definition 6 (justified by Theorem 28 in Landau, the existence
# half of which is admitted as we did for + in Definition 1).
# ---------------------------------------------------------------------------

# Multiplication is defined analogously, via NUM_RECURSION at  c := x, h := \k a. a + x.
# Then:  x * 1 = x  and  x * (SUC y) = x * y + x.

MUL_1, MUL_SUC = define_recursive(
    "*", _nnn, x,
    c = x,
    h = mk_abs(_k, mk_abs(_a, mk_add(_a, x))),   # \k a. a + x
    prec=60, assoc="left",
)
TIMES = mk_const("*", [])

def mk_mul(a, b):
    return mk_comb(mk_comb(TIMES, a), b)


# ---------------------------------------------------------------------------
# Theorem 28, Part A (uniqueness half).  Mirror of ADD_UNIQUE.
#   MUL_UNIQUE :  |- !x f g.
#       f 1 = x /\ (!y. f (SUC y) = f y + x) /\
#       g 1 = x /\ (!y. g (SUC y) = g y + x)
#       ==> !y. f y = g y.
# ---------------------------------------------------------------------------

@proof
def MUL_UNIQUE(p):
    p.goal("!x f g. f 1 = x /\\ (!y. f (SUC y) = f y + x) /\\ "
                  "g 1 = x /\\ (!y. g (SUC y) = g y + x) "
                  "==> !y. f y = g y",
           types={"f": _fn_ty, "g": _fn_ty})
    p.fix("x f g")
    p.assume("h: f 1 = x /\\ (!y. f (SUC y) = f y + x) /\\ "
                "g 1 = x /\\ (!y. g (SUC y) = g y + x)")
    p.split_conj("h", "h_f1", "h_fstep", "h_g1", "h_gstep")
    with p.induction("y"):
        with p.base():
            p.thus("f 1 = g 1").by_rewrite(["h_f1", "h_g1"])
        with p.step("IH"):
            p.thus("f (SUC y) = g (SUC y)")\
                .by_rewrite(["h_fstep", "h_gstep", "IH"])


# Helpers (from Landau's "construction in the proof of Theorem 28"):
# ONE_MUL :  |- !y. 1 * y = y.
# SUC_MUL :  |- !x y. (SUC x) * y = x * y + y.

@proof
def ONE_MUL(p):
    p.goal("!y. 1 * y = y")
    p.fix("y")
    with p.induction("y"):
        with p.base():
            p.thus("1 * 1 = 1").by_rewrite([MUL_1])
        with p.step("IH"):
            p.thus("1 * SUC y = SUC y").by_rewrite([MUL_SUC, ADD_1, "IH"])

@proof
def SUC_MUL(p):
    p.goal("!x y. SUC x * y = x * y + y")
    p.fix("x y")
    with p.induction("y"):
        with p.base():
            p.thus("SUC x * 1 = x * 1 + 1").by_rewrite([MUL_1, ADD_1_REV])
        with p.step("IH"):
            p.thus("SUC x * SUC y = x * SUC y + SUC y")\
                .by_rewrite_ac([MUL_SUC, "IH"], PLUS, SATZ_5, SATZ_6,
                                ac_rules=[ADD_1_REV])


# Theorem 29 (commutative law of multiplication):  |- !x y. x * y = y * x.

@proof
def SATZ_29(p):
    p.goal("!x y. x * y = y * x")
    p.fix("x y")
    with p.induction("x"):
        with p.base():
            p.thus("1 * y = y * 1").by_rewrite([ONE_MUL, MUL_1])
        with p.step("IH"):
            p.thus("SUC x * y = y * SUC x")\
                .by_rewrite([SUC_MUL, MUL_SUC, "IH"])


# Theorem 30 (distributive):  |- !x y z. x * (y + z) = x*y + x*z.   Induction on z.

@proof
def SATZ_30(p):
    p.goal("!x y z. x * (y + z) = x * y + x * z")
    p.fix("x y z")
    with p.induction("z"):
        with p.base():
            p.thus("x * (y + 1) = x * y + x * 1")\
                .by_rewrite([ADD_1, MUL_1, MUL_SUC])
        with p.step("IH"):
            p.thus("x * (y + SUC z) = x * y + x * SUC z")\
                .by_rewrite([ADD_SUC, MUL_SUC, SATZ_5, "IH"])


# Theorem 31 (associative law of multiplication):  |- !x y z. (x*y)*z = x*(y*z).

@proof
def SATZ_31(p):
    p.goal("!x y z. (x * y) * z = x * (y * z)")
    p.fix("x y z")
    with p.induction("z"):
        with p.base():
            p.thus("(x * y) * 1 = x * (y * 1)").by_rewrite([MUL_1])
        with p.step("IH"):
            p.thus("(x * y) * SUC z = x * (y * SUC z)")\
                .by_rewrite([MUL_SUC, SATZ_30, "IH"])


# Right-distributivity, the corollary Landau notes after Satz 30:
#   (a+b)*c = a*c + b*c.   Used as a rewrite in the order/multiplication proofs.
# Plain commutativity (SATZ_29) loops as a free rewrite rule, so we name the
# four intermediate equations explicitly and let `by_rewrite` chain them.
@proof
def RIGHT_DISTRIB(p):
    p.goal("!a b c. (a + b) * c = a * c + b * c")
    p.fix("a b c")
    p.have("flip: (a + b) * c = c * (a + b)").by(SATZ_29, "a + b", "c")
    p.have("dist: c * (a + b) = c * a + c * b").by(SATZ_30, "c", "a", "b")
    p.have("ca: c * a = a * c").by(SATZ_29, "c", "a")
    p.have("cb: c * b = b * c").by(SATZ_29, "c", "b")
    p.thus("(a + b) * c = a * c + b * c")\
        .by_rewrite(["flip", "dist", "ca", "cb"])


# Theorem 32 (3-fold "respectively"):  From  x>y / x=y / x<y  it follows  xz > yz / xz = yz / xz < yz.
# We prove the three pieces; same template as Theorem 19.

@proof
def SATZ_32A(p):
    p.goal("!x y z. x > y ==> x * z > y * z")
    p.fix("x y z")
    p.assume("h: x > y")
    p.choose("u: x = y + u", from_="h")
    p.have("eq: x * z = y * z + u * z").by_rewrite(["u_eq", RIGHT_DISTRIB])
    p.thus("x * z > y * z").by_witness("u * z", "eq")

@proof
def SATZ_32B(p):
    p.goal("!x y z. x = y ==> x * z = y * z")
    p.fix("x y z")
    p.assume("h: x = y")
    p.thus("x * z = y * z").by_rewrite(["h"])

@proof
def SATZ_32C(p):
    p.goal("!x y z. x < y ==> x * z < y * z")
    p.fix("x y z")
    p.assume("h: x < y")
    p.have("yx: y > x").by(SATZ_12, "x", "y", "h")
    p.have("yz_gt: y * z > x * z").by(SATZ_32A, "y", "x", "z", "yx")
    p.thus("x * z < y * z").by(SATZ_11, "y * z", "x * z", "yz_gt")


# Theorem 34:  x>y, z>u  ==>  x*z > y*u.   Mirror of Theorem 21.

@proof
def SATZ_34(p):
    p.goal("!x y z u. x > y ==> z > u ==> x * z > y * u")
    p.fix("x y z u")
    p.assume("hxy: x > y", "hzu: z > u")
    p.have("xz_gt_yz: x * z > y * z").by(SATZ_32A, "x", "y", "z", "hxy")
    p.have("zy_gt_uy: z * y > u * y").by(SATZ_32A, "z", "u", "y", "hzu")
    p.have("yz_gt_yu: y * z > y * u")\
        .by_rewrite_of("zy_gt_uy",
                       [SPECL([z, y], SATZ_29), SPECL([u, y], SATZ_29)])
    p.have("yu_lt_yz: y * u < y * z").by(SATZ_11, "y * z", "y * u", "yz_gt_yu")
    p.have("yz_lt_xz: y * z < x * z").by(SATZ_11, "x * z", "y * z", "xz_gt_yz")
    p.have("yu_lt_xz: y * u < x * z")\
        .by(SATZ_15, "y * u", "y * z", "x * z", "yu_lt_yz", "yz_lt_xz")
    p.thus("x * z > y * u").by(SATZ_12, "y * u", "x * z", "yu_lt_xz")


# Theorem 35:  x>=y, z>u (or x>y, z>=u)  ==>  x*z > y*u.

@proof
def SATZ_35A(p):
    p.goal("!x y z u. x >= y ==> z > u ==> x * z > y * u")
    p.fix("x y z u")
    p.assume("hge: x >= y", "hgt: z > u")
    with p.cases_on("hge"):
        with p.case("x > y"):
            p.thus("x * z > y * u").by(SATZ_34, "x", "y", "z", "u", -1, "hgt")
        with p.case("hxy: x = y"):
            p.have("zy_gt_uy: z * y > u * y").by(SATZ_32A, "z", "u", "y", "hgt")
            p.have("yz_gt_yu: y * z > y * u")\
                .by_rewrite_of("zy_gt_uy",
                               [SPECL([z, y], SATZ_29), SPECL([u, y], SATZ_29)])
            p.thus("x * z > y * u").by_rewrite_of(
                "yz_gt_yu",
                [AP_THM(AP_TERM(TIMES, SYM(p.fact("hxy"))), z)])

@proof
def SATZ_35B(p):
    p.goal("!x y z u. x > y ==> z >= u ==> x * z > y * u")
    p.fix("x y z u")
    p.assume("hgt: x > y", "hge: z >= u")
    with p.cases_on("hge"):
        with p.case("z > u"):
            p.thus("x * z > y * u").by(SATZ_34, "x", "y", "z", "u", "hgt", -1)
        with p.case("hzu: z = u"):
            p.have("xz_gt_yz: x * z > y * z").by(SATZ_32A, "x", "y", "z", "hgt")
            p.thus("x * z > y * u").by_rewrite_of(
                "xz_gt_yz",
                [AP_TERM(mk_comb(TIMES, y), p.fact("hzu"))])


# Theorem 36:  x>=y, z>=u  ==>  x*z >= y*u.

@proof
def SATZ_36(p):
    p.goal("!x y z u. x >= y ==> z >= u ==> x * z >= y * u")
    p.fix("x y z u")
    p.assume("hxy: x >= y", "hzu: z >= u")
    with p.cases_on("hxy"):
        with p.case("hgt_xy: x > y"):
            p.have("gt: x * z > y * u").by(SATZ_35B, "x", "y", "z", "u",
                                            "hgt_xy", "hzu")
            p.thus("x * z >= y * u").by(GT_TO_GE, "gt")
        with p.case("heq_xy: x = y"):
            with p.cases_on("hzu"):
                with p.case("hgt_zu: z > u"):
                    p.have("gt: x * z > y * u").by(SATZ_35A, "x", "y", "z", "u",
                                                    "hxy", "hgt_zu")
                    p.thus("x * z >= y * u").by(GT_TO_GE, "gt")
                with p.case("heq_zu: z = u"):
                    p.have("eq: x * z = y * u").by_rewrite(["heq_xy", "heq_zu"])
                    p.thus("x * z >= y * u").by(EQ_TO_GE, "eq")


# ---------------------------------------------------------------------------
# Theorem 9, part A (mutual exclusion of trichotomy):
#   |- !x y. ~(x = y     /\  ?u. x = y + u)
#         /\ ~(x = y     /\  ?v. y = x + v)
#         /\ ~((?u. x = y + u) /\ (?v. y = x + v))
# ---------------------------------------------------------------------------

@proof
def _SATZ_9_EXCL_12(p):
    p.goal("!x y. ~(x = y /\\ ?u. x = y + u)")
    p.fix("x y")
    with p.suppose("h: x = y /\\ ?u. x = y + u"):
        p.have("h_eq: x = y").by(CONJUNCT1, "h")
        p.have("h_ex: ?u. x = y + u").by(CONJUNCT2, "h")
        p.have("h_gt: x > y").by_fold("h_ex")
        p.absurd().auto("h_gt", "h_eq")


@proof
def _SATZ_9_EXCL_13(p):
    p.goal("!x y. ~(x = y /\\ ?v. y = x + v)")
    p.fix("x y")
    with p.suppose("h: x = y /\\ ?v. y = x + v"):
        p.have("h_eq: x = y").by(CONJUNCT1, "h")
        p.have("h_ex: ?v. y = x + v").by(CONJUNCT2, "h")
        p.have("h_lt: x < y").by_fold("h_ex")
        p.absurd().auto("h_lt", "h_eq")


@proof
def _SATZ_9_EXCL_23(p):
    p.goal("!x y. ~((?u. x = y + u) /\\ (?v. y = x + v))")
    p.fix("x y")
    with p.suppose("h: (?u. x = y + u) /\\ (?v. y = x + v)"):
        p.have("h_e2: ?u. x = y + u").by(CONJUNCT1, "h")
        p.have("h_e3: ?v. y = x + v").by(CONJUNCT2, "h")
        p.have("h_gt: x > y").by_fold("h_e2")
        p.have("h_lt: x < y").by_fold("h_e3")
        p.absurd().auto("h_lt", "h_gt")


SATZ_9_EXCL = GENL([x, y],
                   CONJ(SPECL([x, y], _SATZ_9_EXCL_12),
                        CONJ(SPECL([x, y], _SATZ_9_EXCL_13),
                             SPECL([x, y], _SATZ_9_EXCL_23))))


# ---------------------------------------------------------------------------
# Theorem 20.   |- !x y z. (x+z > y+z ==> x > y)
#                       /\ (x+z = y+z ==> x = y)
#                       /\ (x+z < y+z ==> x < y).
# Proof (Landau): from Theorem 19 + trichotomy, since the three cases of
# trichotomy mutually exclude each other.
# ---------------------------------------------------------------------------

@proof
def SATZ_20A(p):
    p.goal("!x y z. x + z > y + z ==> x > y")
    p.fix("x y z")
    p.assume("h_a: x + z > y + z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.have("eq_sum: x + z = y + z").by(SATZ_19B, "x", "y", "z", "h_eq")
            p.absurd().auto("h_a", "eq_sum")
        with p.case("h_gt: x > y"):
            p.thus("x > y").by_thm(p.fact("h_gt"))
        with p.case("h_lt: x < y"):
            p.have("lt_sum: x + z < y + z").by(SATZ_19C, "x", "y", "z", "h_lt")
            p.absurd().auto("lt_sum", "h_a")


@proof
def SATZ_20B(p):
    p.goal("!x y z. x + z = y + z ==> x = y")
    p.fix("x y z")
    p.assume("h_b: x + z = y + z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.thus("x = y").by_thm(p.fact("h_eq"))
        with p.case("h_gt: x > y"):
            p.have("gt_sum: x + z > y + z").by(SATZ_19A, "x", "y", "z", "h_gt")
            p.absurd().auto("gt_sum", "h_b")
        with p.case("h_lt: x < y"):
            p.have("lt_sum: x + z < y + z").by(SATZ_19C, "x", "y", "z", "h_lt")
            p.absurd().auto("lt_sum", "h_b")


@proof
def SATZ_20C(p):
    p.goal("!x y z. x + z < y + z ==> x < y")
    p.fix("x y z")
    p.assume("h_c: x + z < y + z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.have("eq_sum: x + z = y + z").by(SATZ_19B, "x", "y", "z", "h_eq")
            p.absurd().auto("h_c", "eq_sum")
        with p.case("h_gt: x > y"):
            p.have("gt_sum: x + z > y + z").by(SATZ_19A, "x", "y", "z", "h_gt")
            p.absurd().auto("h_c", "gt_sum")
        with p.case("h_lt: x < y"):
            p.thus("x < y").by_thm(p.fact("h_lt"))


SATZ_20 = GENL([x, y, z],
               CONJ(SPECL([x, y, z], SATZ_20A),
                    CONJ(SPECL([x, y, z], SATZ_20B),
                         SPECL([x, y, z], SATZ_20C))))


# ---------------------------------------------------------------------------
# Theorem 33.   Same template as Theorem 20, with multiplication.
#   |- !x y z. (xz > yz ==> x > y) /\ (xz = yz ==> x = y) /\ (xz < yz ==> x < y).
# ---------------------------------------------------------------------------

@proof
def SATZ_33A(p):
    p.goal("!x y z. x * z > y * z ==> x > y")
    p.fix("x y z")
    p.assume("h_a: x * z > y * z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.have("eq_prod: x * z = y * z").by(SATZ_32B, "x", "y", "z", "h_eq")
            p.absurd().auto("h_a", "eq_prod")
        with p.case("h_gt: x > y"):
            p.thus("x > y").by_thm(p.fact("h_gt"))
        with p.case("h_lt: x < y"):
            p.have("lt_prod: x * z < y * z").by(SATZ_32C, "x", "y", "z", "h_lt")
            p.absurd().auto("lt_prod", "h_a")


@proof
def SATZ_33B(p):
    p.goal("!x y z. x * z = y * z ==> x = y")
    p.fix("x y z")
    p.assume("h_b: x * z = y * z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.thus("x = y").by_thm(p.fact("h_eq"))
        with p.case("h_gt: x > y"):
            p.have("gt_prod: x * z > y * z").by(SATZ_32A, "x", "y", "z", "h_gt")
            p.absurd().auto("gt_prod", "h_b")
        with p.case("h_lt: x < y"):
            p.have("lt_prod: x * z < y * z").by(SATZ_32C, "x", "y", "z", "h_lt")
            p.absurd().auto("lt_prod", "h_b")


@proof
def SATZ_33C(p):
    p.goal("!x y z. x * z < y * z ==> x < y")
    p.fix("x y z")
    p.assume("h_c: x * z < y * z")
    with p.cases_on(SATZ_10, "x", "y"):
        with p.case("h_eq: x = y"):
            p.have("eq_prod: x * z = y * z").by(SATZ_32B, "x", "y", "z", "h_eq")
            p.absurd().auto("h_c", "eq_prod")
        with p.case("h_gt: x > y"):
            p.have("gt_prod: x * z > y * z").by(SATZ_32A, "x", "y", "z", "h_gt")
            p.absurd().auto("h_c", "gt_prod")
        with p.case("h_lt: x < y"):
            p.thus("x < y").by_thm(p.fact("h_lt"))


SATZ_33 = GENL([x, y, z],
               CONJ(SPECL([x, y, z], SATZ_33A),
                    CONJ(SPECL([x, y, z], SATZ_33B),
                         SPECL([x, y, z], SATZ_33C))))


if __name__ == "__main__":
    print("Step 1 OK -- Peano signature and Axioms 2–5 installed.")
    print("  AXIOM_3   :", pp_thm(AXIOM_3))
    print("  AXIOM_4   :", pp_thm(AXIOM_4))
    print("  INDUCTION :", pp_thm(INDUCTION))
    print("Step 2 OK -- derived inference rules verified by self-tests.")
    print("Step 3 OK -- Theorem 1 proved.")
    print("  SATZ_1    :", pp_thm(SATZ_1))
    print("Step 4 OK -- Theorem 2 proved.")
    print("  SATZ_2    :", pp_thm(SATZ_2))
    print("Step 5 OK -- Theorem 3 proved.")
    print("  SATZ_3    :", pp_thm(SATZ_3))
    print("Step 6 OK -- Definition 1 (addition) installed.")
    print("  ADD_1     :", pp_thm(ADD_1))
    print("  ADD_SUC   :", pp_thm(ADD_SUC))
    print("  ADD_UNIQUE:", pp_thm(ADD_UNIQUE))
    print("Step 7 OK -- Theorem 5 (associativity of addition) proved.")
    print("  SATZ_5    :", pp_thm(SATZ_5))
    print("Step 8 OK -- Theorem 6 (commutativity of addition) proved.")
    print("  ONE_PLUS  :", pp_thm(ONE_PLUS))
    print("  SUC_PLUS  :", pp_thm(SUC_PLUS))
    print("  SATZ_6    :", pp_thm(SATZ_6))
    print("Step 9 OK -- Theorem 7 proved.")
    print("  SATZ_7    :", pp_thm(SATZ_7))
    print("Step 10 OK -- Theorem 8 proved.")
    print("  SATZ_8    :", pp_thm(SATZ_8))
    print("Step 11 OK -- Theorem 9 (existence half of trichotomy) proved.")
    print("  LEMMA_PRED:", pp_thm(LEMMA_PRED))
    print("  SATZ_9    :", pp_thm(SATZ_9))
    print("Step 12 OK -- Definitions 2-3 + Theorems 10, 11, 12 proved.")
    print("  SATZ_10   :", pp_thm(SATZ_10))
    print("  SATZ_11   :", pp_thm(SATZ_11))
    print("  SATZ_12   :", pp_thm(SATZ_12))
    print("Step 13 OK -- Definitions 4-5 + Theorems 13, 14 proved.")
    print("  SATZ_13   :", pp_thm(SATZ_13))
    print("  SATZ_14   :", pp_thm(SATZ_14))
    print("Step 14 OK -- Theorem 15 (Transitivity).")
    print("  SATZ_15   :", pp_thm(SATZ_15))
    print("Step 15 OK -- Theorems 16, 17 proved.")
    print("  SATZ_16A  :", pp_thm(SATZ_16A))
    print("  SATZ_16B  :", pp_thm(SATZ_16B))
    print("  SATZ_17   :", pp_thm(SATZ_17))
    print("Step 16 OK -- Theorems 18, 19, 21, 22, 23 proved.")
    print("  SATZ_18   :", pp_thm(SATZ_18))
    print("  SATZ_19A  :", pp_thm(SATZ_19A))
    print("  SATZ_19B  :", pp_thm(SATZ_19B))
    print("  SATZ_19C  :", pp_thm(SATZ_19C))
    print("  SATZ_21   :", pp_thm(SATZ_21))
    print("  SATZ_22A  :", pp_thm(SATZ_22A))
    print("  SATZ_22B  :", pp_thm(SATZ_22B))
    print("  SATZ_23   :", pp_thm(SATZ_23))
    print("Step 17 OK -- Theorems 24, 25, 26 proved.")
    print("  SATZ_24   :", pp_thm(SATZ_24))
    print("  SATZ_25   :", pp_thm(SATZ_25))
    print("  SATZ_26   :", pp_thm(SATZ_26))
    print("Step 18 OK -- Definition 6 + Theorems 29-36 proved (Theorem 28 = Definition 6).")
    print("  MUL_UNIQUE:", pp_thm(MUL_UNIQUE))
    print("  ONE_MUL   :", pp_thm(ONE_MUL))
    print("  SUC_MUL   :", pp_thm(SUC_MUL))
    print("  SATZ_29   :", pp_thm(SATZ_29))
    print("  SATZ_30   :", pp_thm(SATZ_30))
    print("  SATZ_31   :", pp_thm(SATZ_31))
    print("  SATZ_32A  :", pp_thm(SATZ_32A))
    print("  SATZ_32B  :", pp_thm(SATZ_32B))
    print("  SATZ_32C  :", pp_thm(SATZ_32C))
    print("  SATZ_34   :", pp_thm(SATZ_34))
    print("  SATZ_35A  :", pp_thm(SATZ_35A))
    print("  SATZ_35B  :", pp_thm(SATZ_35B))
    print("  SATZ_36   :", pp_thm(SATZ_36))
    print("Step 19 OK -- mutual exclusion (Theorem 9 part A) and Theorems 20, 33.")
    print("  SATZ_9_EXCL:", pp_thm(SATZ_9_EXCL))
    print("  SATZ_20    :", pp_thm(SATZ_20))
    print("  SATZ_33    :", pp_thm(SATZ_33))
    print("Step 20 OK -- excluded middle + Theorem 27 (well-ordering).")
    print("  SATZ_27    :", pp_thm(SATZ_27))
