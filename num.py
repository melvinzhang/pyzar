"""Peano signature and induction.

Introduces the natural-number type `num`, the constants `1` and `SUC`,
admits Peano's axioms 3-5 (distinctness of successors, injectivity, induction),
and provides the convenience rule `INDUCT` that packages Axiom 5 for
Landau-style proofs.

Primitive recursion (`num_RECURSION`) is the natural next inhabitant of this
module: once it is proved here, addition and multiplication can be introduced
in `nat.py` via specification rather than admitted as axioms.
"""

from fusion import (
    Var, Abs,
    bool_ty, mk_comb, mk_const, mk_eq, mk_fun_ty,
    mk_type, new_axiom, new_constant, new_type,
    ASSUME, EQ_MP, HolError,
)
from axioms import (
    mk_and, mk_imp, mk_forall, mk_not,
)
from logic import (
    BETA_CONV, SYM, SPEC, GEN, CONJ, DISCH, MP,
)


# ---------------------------------------------------------------------------
# num signature.
# ---------------------------------------------------------------------------

new_type("num", 0)
num_ty = mk_type("num", [])

new_constant("1", num_ty)
ONE = mk_const("1", [])

new_constant("SUC", mk_fun_ty(num_ty, num_ty))
SUC = mk_const("SUC", [])

def mk_suc(t):
    return mk_comb(SUC, t)


# Standard variable names re-used throughout the arithmetic development.
x = Var("x", num_ty)
y = Var("y", num_ty)
z = Var("z", num_ty)
u = Var("u", num_ty)
v = Var("v", num_ty)
w = Var("w", num_ty)
P = Var("P", mk_fun_ty(num_ty, bool_ty))


# ---------------------------------------------------------------------------
# Peano Axioms 3, 4, 5.
# ---------------------------------------------------------------------------

# Axiom 3:   |- !x. ~(x' = 1)
AXIOM_3 = new_axiom(mk_forall(x, mk_not(mk_eq(mk_suc(x), ONE))))

# Axiom 4:   |- !x y. x' = y' ==> x = y
AXIOM_4 = new_axiom(
    mk_forall(x, mk_forall(y,
        mk_imp(mk_eq(mk_suc(x), mk_suc(y)),
               mk_eq(x, y)))))

# Axiom 5 (induction):
#   |- !P. P 1 /\ (!x. P x ==> P (x')) ==> !x. P x
INDUCTION = new_axiom(
    mk_forall(P,
        mk_imp(
            mk_and(mk_comb(P, ONE),
                   mk_forall(x, mk_imp(mk_comb(P, x),
                                       mk_comb(P, mk_suc(x))))),
            mk_forall(x, mk_comb(P, x)))))


# ---------------------------------------------------------------------------
# Induction helper -- packages Axiom 5 for Landau-style proofs.
#
# Given a predicate  pred = \v. body[v]  and theorems
#       base_th : |- body[1/v]
#       step_th : |- !v. body[v] ==> body[v'/v]
# returns           |- !v. body[v].
# ---------------------------------------------------------------------------

def INDUCT(pred, base_th, step_th):
    if not isinstance(pred, Abs):
        raise HolError("INDUCT: pred must be an Abs")
    v_var = pred.bvar
    pred_1  = mk_comb(pred, ONE)
    pred_v  = mk_comb(pred, v_var)
    pred_vs = mk_comb(pred, mk_suc(v_var))
    base_pred = EQ_MP(SYM(BETA_CONV(pred_1)), base_th)
    inst_step    = SPEC(v_var, step_th)
    body_assume  = EQ_MP(BETA_CONV(pred_v), ASSUME(pred_v))
    body_succ    = MP(inst_step, body_assume)
    pred_vs_th   = EQ_MP(SYM(BETA_CONV(pred_vs)), body_succ)
    step_pred    = GEN(v_var, DISCH(pred_v, pred_vs_th))
    ind_inst     = SPEC(pred, INDUCTION)
    forall_pred  = MP(ind_inst, CONJ(base_pred, step_pred))
    body_th = EQ_MP(BETA_CONV(pred_v), SPEC(v_var, forall_pred))
    return GEN(v_var, body_th)
