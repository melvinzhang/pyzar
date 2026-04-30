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
    mk_and, mk_imp, mk_forall, mk_exists, mk_not, mk_select,
)
from logic import (
    AP_TERM, AP_THM, BETA_CONV, SYM,
    SPEC, GEN, CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP,
    CONTR, NOT_ELIM, NOT_INTRO,
    mk_or, DISJ1, DISJ2, DISJ_CASES,
    NE_SYM, REWRITE_NE, EXISTS, EXISTS_AT,
    EXCLUDED_MIDDLE, NOT_NOT_ELIM, NOT_EX_TO_FORALL_NOT,
    PROVE_HYP, ELIM_EX,
    SPECL, GENL, DISCHL, TRANS_CHAIN, MP_LIST, CASE_OR,
)
from num import (
    num_ty, ONE, SUC, mk_suc,
    x, y, z, u, v, w, P,
    AXIOM_3, AXIOM_4, INDUCTION, INDUCT,
    define_recursive,
)
from tactics import (REWRITE_PROVE, REWRITE_RULE, REWRITE_CONV,
                       AC_PROVE, AC_NORM, REWRITE_AC_PROVE)
from parser import parse, pp, ParseEnv, define, pp_thm, DEFAULT_SIG
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

def _binop_unfold(def_th, a, b):
    """Given ``def_th : |- op = \\x y. body``, return ``|- op a b = body[a,b]``
    by two AP_THM/BETA_CONV steps."""
    eq1 = AP_THM(def_th, a)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, b)
    return TRANS(eq3, BETA_CONV(rand(eq3._concl)))

def UNFOLD_GT(a, b):
    """ |- (a > b) = (?u. a = b + u) """
    return _binop_unfold(GT_DEF, a, b)

def UNFOLD_LT(a, b):
    """ |- (a < b) = (?v. b = a + v) """
    return _binop_unfold(LT_DEF, a, b)

# Register with the proof DSL so `p.choose(name, from_=label)` accepts a fact
# whose conclusion is `> ` or `<`.
from proof import register_unfolder, register_disj_unfolder
register_unfolder(">", UNFOLD_GT)
register_unfolder("<", UNFOLD_LT)

def PROVE_GT(a_t, b_t, witness, eq_th):
    """From eq_th : ... |- a = b + witness, return ... |- a > b."""
    pred = parse("\\u. ${a} = ${b} + u", a=a_t, b=b_t)
    return EQ_MP(SYM(UNFOLD_GT(a_t, b_t)), EXISTS(pred, witness, eq_th))

def PROVE_LT(a_t, b_t, witness, eq_th):
    """From eq_th : ... |- b = a + witness, return ... |- a < b."""
    pred = parse("\\v. ${b} = ${a} + v", a=a_t, b=b_t)
    return EQ_MP(SYM(UNFOLD_LT(a_t, b_t)), EXISTS(pred, witness, eq_th))


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

def _prove_satz_10():
    th9 = SPEC(y, SPEC(x, SATZ_9))             # |- (x=y) \/ (?u. ...) \/ (?v. ...)
    case2 = mk_exists(u, mk_eq(x, mk_add(y, u)))
    case3 = mk_exists(v, mk_eq(y, mk_add(x, v)))
    # Rewrite case2 -> (x > y), case3 -> (x < y).
    eq_gt = SYM(UNFOLD_GT(x, y))               # |- ?u. x = y + u   = (x > y)
    eq_lt = SYM(UNFOLD_LT(x, y))               # |- ?v. y = x + v   = (x < y)
    # body9 = (x=y) \/ (case2 \/ case3); rewrite to (x=y) \/ (x>y \/ x<y).
    OR = DEFAULT_SIG["\\/"]
    inner_eq = MK_COMB(AP_TERM(OR, eq_gt), eq_lt)
    # |- (case2 \/ case3) = (x > y \/ x < y)
    outer_eq = AP_TERM(mk_comb(OR, mk_eq(x, y)), inner_eq)
    return GENL([x, y], EQ_MP(outer_eq, th9))

SATZ_10 = _prove_satz_10()


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

def UNFOLD_GE(a, b): return _binop_unfold(GE_DEF, a, b)
def UNFOLD_LE(a, b): return _binop_unfold(LE_DEF, a, b)

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
            p.thus("(y < x) \\/ (y = x)")\
                .by_thm(DISJ1(p.fact("yx_lt"), mk_eq(y, x)))
        with p.case("h_eq: x = y"):
            p.have("yx_eq: y = x").by(SYM, "h_eq")
            p.thus("(y < x) \\/ (y = x)")\
                .by_thm(DISJ2(mk_lt(y, x), p.fact("yx_eq")))
    p.thus("y <= x").by_fold("yx_or")


@proof
def SATZ_14(p):
    p.goal("!x y. x <= y ==> y >= x")
    p.fix("x y")
    p.assume("h: x <= y")
    with p.have("yx_or: (y > x) \\/ (y = x)").by_cases("h"):
        with p.case("h_lt: x < y"):
            p.have("yx_gt: y > x").by(SATZ_12, "x", "y", "h_lt")
            p.thus("(y > x) \\/ (y = x)")\
                .by_thm(DISJ1(p.fact("yx_gt"), mk_eq(y, x)))
        with p.case("h_eq: x = y"):
            p.have("yx_eq: y = x").by(SYM, "h_eq")
            p.thus("(y > x) \\/ (y = x)")\
                .by_thm(DISJ2(mk_gt(y, x), p.fact("yx_eq")))
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
        .by_thm(EQ_MP(MK_COMB(AP_TERM(GT, SPECL([z, y], SATZ_6)),
                              SPECL([u, y], SATZ_6)),
                      p.fact("zy_gt_uy")))
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
            p.have("yz_gt_yu: y + z > y + u").by_thm(EQ_MP(
                MK_COMB(AP_TERM(GT, SPECL([z, y], SATZ_6)),
                        SPECL([u, y], SATZ_6)),
                p.fact("zy_gt_uy")))
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
                    p.thus("x + z >= y + u").by(EQ_TO_GE,
                        MK_COMB(AP_TERM(PLUS, p.fact("heq_xy")),
                                p.fact("heq_zu")))


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

def _prove_satz_27():
    N_ty = mk_fun_ty(num_ty, bool_ty)
    N_var = Var("N", N_ty)
    n_var = Var("n", num_ty)
    k_var = Var("k", num_ty)
    m_var = Var("m", num_ty)
    P = ParseEnv(N=N_ty)

    hyp_nonempty = P.parse("?n. N n")
    M_pred = P.parse("\\x. !n. N n ==> x <= n")

    def M_at(t):
        return mk_comb(M_pred, t)

    conclusion = P.parse("?m. N m /\\ (!k. N k ==> m <= k)")

    # === Step 1: M(1). ===
    s24_n = SPEC(n_var, SATZ_24)
    one_le_n = MP(SPEC(ONE, SPEC(n_var, SATZ_13)), s24_n)
    M1_inner = GEN(n_var, DISCH(mk_comb(N_var, n_var), one_le_n))
    M1 = EQ_MP(SYM(BETA_CONV(M_at(ONE))), M1_inner)

    # === Step 2: !y. N y ==> ~M(y+1). ===
    h_Ny = ASSUME(P.parse("N y"))
    h_M_yp1 = ASSUME(M_at(mk_add(y, ONE)))
    M_unfolded = EQ_MP(BETA_CONV(M_at(mk_add(y, ONE))), h_M_yp1)
    spec_y = SPEC(y, M_unfolded)
    le_y1_y = MP(spec_y, h_Ny)
    s18_y1 = SPEC(ONE, SPEC(y, SATZ_18))
    le_unfold = EQ_MP(UNFOLD_LE(mk_add(y, ONE), y), le_y1_y)
    branch_lt = DISCH(parse("y + 1 < y"),
                      CONTRA_LT_GT(mk_add(y, ONE), y,
                                   ASSUME(parse("y + 1 < y")), s18_y1))
    branch_eq = DISCH(parse("y + 1 = y"),
                      CONTRA_GT_EQ(mk_add(y, ONE), y, s18_y1,
                                   ASSUME(parse("y + 1 = y"))))
    th_F = DISJ_CASES(le_unfold, branch_lt, branch_eq)
    th_imp_F = DISCH(M_at(mk_add(y, ONE)), th_F)
    not_M_yp1 = NOT_INTRO(th_imp_F)
    Ny_imp_notM = DISCH(P.parse("N y"), not_M_yp1)           # {} |- N y ==> ~M(y+1)

    # === Step 3: ?m. M(m) /\ ~M(m+1). ===
    Q_pred = parse("\\x. ${M} x /\\ ~${M} (x + 1)", M=M_pred)
    target_3 = parse("?x. ${M} x /\\ ~${M} (x + 1)", M=M_pred)
    not_target_3 = mk_not(target_3)

    # Under not_target_3, derive contradiction using non-emptiness of N.
    # First: !x. ~Q(x).
    forall_not_Q = NOT_EX_TO_FORALL_NOT(ASSUME(not_target_3), Q_pred)
    # Next: !x. M(x) ==> M(x+1).
    # Pick x.  Goal: M(x) ==> M(x+1).
    # From not_Q(x) = ~(M(x) /\ ~M(x+1)), and EM on M(x+1):
    #   if M(x+1): trivially M(x) ==> M(x+1).
    #   if ~M(x+1): then ~M(x) (else contradiction with not_Q(x)).  So M(x) ==> M(x+1) trivially.
    spec_not_Q = SPEC(x, forall_not_Q)
    not_Q_x_unfold_eq = BETA_CONV(mk_comb(Q_pred, x))     # |- Q_pred x = (M(x) /\ ~M(x+1))
    not_Q_x_term = mk_not(rand(not_Q_x_unfold_eq._concl))  # ~(M(x) /\ ~M(x+1))
    # Hmm spec_not_Q._concl is ~Q_pred(x) but after SPEC's beta it should be ~(M(x)/\~M(x+1)).
    # Let me rely on that.
    em_Mxp1 = SPEC(M_at(mk_add(x, ONE)), EXCLUDED_MIDDLE)   # |- M(x+1) \/ ~M(x+1)
    branch_M = DISCH(M_at(mk_add(x, ONE)),
                     DISCH(M_at(x), ASSUME(M_at(mk_add(x, ONE)))))
    # Sub-branch ~M(x+1): show M(x) ==> M(x+1).  Approach: show ~M(x), then M(x) ==> anything.
    h_notM_xp1 = ASSUME(mk_not(M_at(mk_add(x, ONE))))
    h_M_x = ASSUME(M_at(x))
    conj_x = CONJ(h_M_x, h_notM_xp1)            # {M(x), ~M(x+1)} |- M(x) /\ ~M(x+1)
    th_F_inner = MP(NOT_ELIM(spec_not_Q), conj_x)        # {..., ~target_3} |- F
    branch_NM_inner = CONTR(M_at(mk_add(x, ONE)), th_F_inner)   # {..., ~target_3} |- M(x+1)
    branch_NM = DISCH(mk_not(M_at(mk_add(x, ONE))),
                       DISCH(M_at(x), branch_NM_inner))
    M_imp_M_succ = DISJ_CASES(em_Mxp1, branch_M, branch_NM)
    forall_M_succ = GEN(x, M_imp_M_succ)                  # {~target_3} |- !x. M(x) ==> M(x+1)

    # Apply Axiom 5 to M_pred.
    ind_inst = SPEC(M_pred, INDUCTION)                    # |- (M_pred 1 /\ !x. M_pred x ==> M_pred x') ==> !x. M_pred x
    # Convert forall_M_succ to use M_pred form (currently written as M_at).
    # M_at(x) IS M_pred x = (\x. body) x — same as in INDUCT.
    # We need:  !x. M_pred x ==> M_pred x'.   M_at(x) = M_pred x already (literally same term).
    forall_step_pred = forall_M_succ                       # already in pred form: M(x) ==> M(x+1)
    # Build conjunction.
    conj_for_ind = CONJ(M1, forall_step_pred)              # {~target_3} |- M_pred 1 /\ !x. M_pred x ==> M_pred x'
    # Wait, the step in Axiom 5 uses x' = SUC x, not x+1.
    # M_at(x+1) versus M_pred (SUC x) — they differ by ADD_1.  Need to convert.
    # SUC x and x+1 are equal by ADD_1: |- !x. x + 1 = SUC x.  So SUC x = x + 1, and
    # M_at(SUC x) = M_at(x+1) as terms after substitution... but they are NOT syntactically equal.
    # We need to bridge.
    # Build !x. M_pred x ==> M_pred (SUC x)   from   !x. M_pred x ==> M_pred (x+1).
    # via AP_TERM(M_pred, ADD_1 spec): |- M_pred (x+1) = M_pred (SUC x).
    add_1_x = SPEC(x, ADD_1)                              # |- x + 1 = SUC x
    M_eq = AP_TERM(M_pred, add_1_x)                       # |- M_pred (x+1) = M_pred (SUC x)
    # Take spec of forall_step_pred at x: M_pred x ==> M_pred (x+1).
    spec_step = SPEC(x, forall_step_pred)
    # Convert RHS via M_eq.
    # spec_step : |- M_pred x ==> M_pred (x+1).  We want |- M_pred x ==> M_pred (SUC x).
    h_M_x2 = ASSUME(M_at(x))
    th_M_xp1 = MP(spec_step, h_M_x2)                       # {M(x)} |- M_pred (x+1)
    th_M_sx = EQ_MP(M_eq, th_M_xp1)                        # {M(x)} |- M_pred (SUC x)
    spec_step_suc = DISCH(M_at(x), th_M_sx)                # |- M_pred x ==> M_pred (SUC x)
    forall_step_suc = GEN(x, spec_step_suc)                # {~target_3} |- !x. M_pred x ==> M_pred (SUC x)
    conj_for_ind2 = CONJ(M1, forall_step_suc)
    forall_M_all = MP(ind_inst, conj_for_ind2)             # {~target_3} |- !x. M_pred x

    # Now derive contradiction with hyp_nonempty.
    # Pick n ∈ N (witness of hyp_nonempty), apply forall_M_all to n+1 to get M(n+1),
    # then by Step 2 (Ny_imp_notM specialised), ~M(n+1).
    n_pred = P.parse("\\n. N n")
    def _from_n(eq_Nn):     # {N w} |- N w  for w = SELECT witness
        w_t = rand(eq_Nn._concl)
        spec_M = SPEC(mk_add(w_t, ONE), forall_M_all)          # M_at(w+1)
        not_M_w1 = MP(INST([(w_t, y)], Ny_imp_notM), eq_Nn)    # ~M(w+1)
        return MP(NOT_ELIM(not_M_w1), spec_M)                   # F
    th_F_step3 = ELIM_EX(n_pred, hyp_nonempty, _from_n)
    th_F_step3 = PROVE_HYP(ASSUME(hyp_nonempty), th_F_step3)
    # th_F_step3 : {~target_3, hyp_nonempty} |- F
    th_target3 = NOT_NOT_ELIM(NOT_INTRO(DISCH(not_target_3, th_F_step3)))
    # th_target3 : {hyp_nonempty} |- target_3   (= ?m. M(m) /\ ~M(m+1))

    # === Step 4: from m with M(m) /\ ~M(m+1), conclude m ∈ N and m ≤ k for all k ∈ N. ===
    def _from_m(eq_Q):
        # eq_Q : {body[w/x]} |- M(w) /\ ~M(w+1).  Extract w from M(w).
        Mm_w   = CONJUNCT1(eq_Q)                               # M(w)
        notM_w1 = CONJUNCT2(eq_Q)                              # ~M(w+1)
        w_t = rand(Mm_w._concl)
        Mm_unfold = EQ_MP(BETA_CONV(M_at(w_t)), Mm_w)          # !n. N n ==> w <= n
        # Sub-claim a: !k. N k ==> w <= k (rename n_var to k_var).
        sub_a = GEN(k_var,
                     DISCH(mk_comb(N_var, k_var),
                           MP(SPEC(k_var, Mm_unfold),
                              ASSUME(mk_comb(N_var, k_var)))))
        # Sub-claim b: N w, by contradiction.  If ~N w, then for n in N: w<n by
        # M(w)+w!=n, so n>=w+1 (Satz 25), giving M(w+1) — contradicts ~M(w+1).
        Pw = P.extend(w=w_t)
        h_not_Nw = ASSUME(Pw.parse("~ N ${w}"))
        h_Nn2 = ASSUME(Pw.parse("N n"))
        w_le_n = MP(SPEC(n_var, Mm_unfold), h_Nn2)             # w <= n
        h_w_eq_n = ASSUME(Pw.parse("${w} = n"))
        Nw_th = EQ_MP(AP_TERM(N_var, SYM(h_w_eq_n)), h_Nn2)    # N w from N n via w=n
        th_F_b = MP(NOT_ELIM(h_not_Nw), Nw_th)
        not_w_eq_n = NOT_INTRO(DISCH(Pw.parse("${w} = n"), th_F_b))
        w_le_unfold = EQ_MP(UNFOLD_LE(w_t, n_var), w_le_n)
        branch_lt_b = DISCH(Pw.parse("${w} < n"),
                             ASSUME(Pw.parse("${w} < n")))
        branch_eq_b = DISCH(Pw.parse("${w} = n"),
                             CONTR(Pw.parse("${w} < n"),
                                   MP(NOT_ELIM(not_w_eq_n),
                                      ASSUME(Pw.parse("${w} = n")))))
        w_lt_n = DISJ_CASES(w_le_unfold, branch_lt_b, branch_eq_b)
        n_gt_w = MP_LIST(SATZ_12, [w_t, n_var, w_lt_n])
        n_ge_wp1 = MP_LIST(SATZ_25, [w_t, n_var, n_gt_w])
        wp1_le_n = MP_LIST(SATZ_13, [n_var, mk_add(w_t, ONE), n_ge_wp1])
        forall_wp1_le = GEN(n_var, DISCH(Pw.parse("N n"), wp1_le_n))
        M_wp1 = EQ_MP(SYM(BETA_CONV(M_at(mk_add(w_t, ONE)))), forall_wp1_le)
        th_F_b2 = MP(NOT_ELIM(notM_w1), M_wp1)
        Nw_th_final = NOT_NOT_ELIM(NOT_INTRO(
            DISCH(Pw.parse("~ N ${w}"), th_F_b2)))
        return EXISTS_AT(w_t, CONJ(Nw_th_final, sub_a))
    th_concl_inner = ELIM_EX(Q_pred, target_3, _from_m)
    # Discharge target_3 using th_target3:
    th_concl = PROVE_HYP(th_target3, th_concl_inner)
    # th_concl : {hyp_nonempty} |- conclusion
    return GEN(N_var, DISCH(hyp_nonempty, th_concl))


SATZ_27 = _prove_satz_27()


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
def _prove_right_distrib():
    a, b, c = Var("a", num_ty), Var("b", num_ty), Var("c", num_ty)
    return GENL([a, b, c], TRANS_CHAIN([
        SPECL([mk_add(a, b), c], SATZ_29),
        SPECL([c, a, b], SATZ_30),
        AP_THM(AP_TERM(PLUS, SPECL([c, a], SATZ_29)), mk_mul(c, b)),
        AP_TERM(mk_comb(PLUS, mk_mul(a, c)), SPECL([c, b], SATZ_29)),
    ]))

RIGHT_DISTRIB = _prove_right_distrib()


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
    p.have("yz_gt_yu: y * z > y * u").by_thm(EQ_MP(
        MK_COMB(AP_TERM(GT, SPECL([z, y], SATZ_29)),
                SPECL([u, y], SATZ_29)),
        p.fact("zy_gt_uy")))
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
            p.have("yz_gt_yu: y * z > y * u").by_thm(EQ_MP(
                MK_COMB(AP_TERM(GT, SPECL([z, y], SATZ_29)),
                        SPECL([u, y], SATZ_29)),
                p.fact("zy_gt_uy")))
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
                    p.thus("x * z >= y * u").by(EQ_TO_GE,
                        MK_COMB(AP_TERM(TIMES, p.fact("heq_xy")),
                                p.fact("heq_zu")))


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
