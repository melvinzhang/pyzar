"""Standard HOL Light boolean definitions and the 3 axioms.

Mirrors bool.ml, class.ml, and the relevant parts of ind.ml from
the original HOL Light distribution.
"""

from fusion import (
    Var,
    aty, bool_ty,
    mk_comb, mk_type,
    new_axiom, new_basic_definition, new_constant, new_type,
)
from basics import (
    bty,
    dest_binder, dest_binop, dest_unop, is_binder, is_binop, is_unop,
    mk_abs, mk_app, mk_const, mk_eq, mk_fun_ty,
)
from parser import add_type, add_infix, add_prefix, add_binder

# Surface syntax for the kernel-level concepts that predate the parser:
# `bool` is from fusion, `=` and `\` from basics.  Everything below this
# line registers itself inline next to where the operator is defined.
add_type("bool", bool_ty)
add_infix("=", 40, mk_eq, assoc="non")
add_binder("\\", mk_abs)

# ---------------------------------------------------------------------------
# Boolean connectives (bool.ml)
# ---------------------------------------------------------------------------

p = Var("p", bool_ty)
q = Var("q", bool_ty)

# T = ((\p. p) = (\p. p))
T_DEF = new_basic_definition(
    mk_eq(Var("T", bool_ty),
          mk_eq(mk_abs(p, p), mk_abs(p, p))))
T = mk_const("T", [])

# (/\) = \p q. (\f. f p q) = (\f. f T T)
bbb_ty = mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty))
f_bbb = Var("f", bbb_ty)
AND_DEF = new_basic_definition(
    mk_eq(Var("/\\", bbb_ty),
          mk_abs(p, mk_abs(q,
              mk_eq(mk_abs(f_bbb, mk_app(f_bbb, p, q)),
                    mk_abs(f_bbb, mk_app(f_bbb, T, T)))))))

def mk_and(a, b):
    return mk_app(mk_const("/\\", []), a, b)
add_infix("/\\", 30, mk_and, assoc="right")

# (==>) = \p q. p /\ q <=> p
IMP_DEF = new_basic_definition(
    mk_eq(Var("==>", bbb_ty),
          mk_abs(p, mk_abs(q, mk_eq(mk_and(p, q), p)))))

def mk_imp(a, b):
    return mk_app(mk_const("==>", []), a, b)
add_infix("==>", 10, mk_imp, assoc="right")

# (!) = \P:A->bool. P = \x. T
abty = mk_fun_ty(aty, bool_ty)
P_ab = Var("P", abty)
x_a = Var("x", aty)
FORALL_DEF = new_basic_definition(
    mk_eq(Var("!", mk_fun_ty(abty, bool_ty)),
          mk_abs(P_ab, mk_eq(P_ab, mk_abs(x_a, T)))))

def mk_forall(v, body):
    return mk_comb(mk_const("!", [(v.ty, aty)]), mk_abs(v, body))
add_binder("!", mk_forall)

# (?) = \P:A->bool. !q. (!x. P x ==> q) ==> q
EXISTS_DEF = new_basic_definition(
    mk_eq(Var("?", mk_fun_ty(abty, bool_ty)),
          mk_abs(P_ab,
              mk_forall(q,
                  mk_imp(mk_forall(x_a, mk_imp(mk_comb(P_ab, x_a), q)),
                         q)))))

def mk_exists(v, body):
    return mk_comb(mk_const("?", [(v.ty, aty)]), mk_abs(v, body))
add_binder("?", mk_exists)

# (\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r
r_b = Var("r", bool_ty)
OR_DEF = new_basic_definition(
    mk_eq(Var("\\/", bbb_ty),
          mk_abs(p, mk_abs(q,
              mk_forall(r_b,
                  mk_imp(mk_imp(p, r_b),
                         mk_imp(mk_imp(q, r_b), r_b)))))))

def mk_or(a, b):
    return mk_app(mk_const("\\/", []), a, b)
add_infix("\\/", 20, mk_or, assoc="right")

# F = !p:bool. p
F_DEF = new_basic_definition(
    mk_eq(Var("F", bool_ty), mk_forall(p, p)))
F = mk_const("F", [])

# (~) = \p. p ==> F
NOT_DEF = new_basic_definition(
    mk_eq(Var("~", mk_fun_ty(bool_ty, bool_ty)),
          mk_abs(p, mk_imp(p, F))))

def mk_not(t):
    return mk_comb(mk_const("~", []), t)
add_prefix("~", mk_not)

# Bool-specific shape helpers: thin aliases over the kernel ``is_*``/
# ``dest_*`` connective helpers so tactic call sites can ask
# "is this a conjunction?" without re-rolling the AST pattern.

def is_conj(tm):    return is_binop("/\\", tm)
def dest_conj(tm):  return dest_binop("/\\", tm)
def is_disj(tm):    return is_binop("\\/", tm)
def dest_disj(tm):  return dest_binop("\\/", tm)
def is_imp(tm):     return is_binop("==>", tm)
def dest_imp(tm):   return dest_binop("==>", tm)
def is_neg(tm):     return is_unop("~", tm)
def dest_neg(tm):   return dest_unop("~", tm)
def is_forall(tm):  return is_binder("!", tm)
def dest_forall(tm): return dest_binder("!", tm)
def is_exists(tm):  return is_binder("?", tm)
def dest_exists(tm): return dest_binder("?", tm)

# ---------------------------------------------------------------------------
# Axiom 1: ETA_AX (bool.ml)        |- !t:A->B. (\x. t x) = t
# ---------------------------------------------------------------------------

_ab_ty = mk_fun_ty(aty, bty)
_t = Var("t", _ab_ty)
_x = Var("x", aty)
ETA_AX = new_axiom(
    mk_forall(_t, mk_eq(mk_abs(_x, mk_comb(_t, _x)), _t)))

# ---------------------------------------------------------------------------
# Axiom 2: SELECT_AX (class.ml)    |- !P (x:A). P x ==> P((@) P)
# ---------------------------------------------------------------------------

new_constant("@", mk_fun_ty(abty, aty))
_P = Var("P", abty)
_xs = Var("x", aty)
_select = mk_const("@", [])

def mk_select(v, body):
    """Build ``@v. body`` -- the SELECT-binder term picking some `v` of the
    same type with `body[v]` true (or any `v` if no such exists)."""
    return mk_comb(mk_const("@", [(v.ty, aty)]), mk_abs(v, body))
add_binder("@", mk_select)

SELECT_AX = new_axiom(
    mk_forall(_P, mk_forall(_xs,
        mk_imp(mk_comb(_P, _xs),
               mk_comb(_P, mk_comb(_select, _P))))))

# ---------------------------------------------------------------------------
# Axiom 3: INFINITY_AX (ind.ml)    |- ?f:ind->ind. ONE_ONE f /\ ~(ONTO f)
# ---------------------------------------------------------------------------

new_type("ind", 0)
ind_ty = mk_type("ind", [])

# ONE_ONE = \f:A->B. !x1 x2. f x1 = f x2 ==> x1 = x2
_fab_ty = mk_fun_ty(aty, bty)
_f = Var("f", _fab_ty)
_x1 = Var("x1", aty)
_x2 = Var("x2", aty)
ONE_ONE_DEF = new_basic_definition(
    mk_eq(Var("ONE_ONE", mk_fun_ty(_fab_ty, bool_ty)),
          mk_abs(_f,
              mk_forall(_x1, mk_forall(_x2,
                  mk_imp(mk_eq(mk_comb(_f, _x1), mk_comb(_f, _x2)),
                         mk_eq(_x1, _x2)))))))

# ONTO = \f:A->B. !y. ?x. y = f x
_y = Var("y", bty)
_xo = Var("x", aty)
ONTO_DEF = new_basic_definition(
    mk_eq(Var("ONTO", mk_fun_ty(_fab_ty, bool_ty)),
          mk_abs(_f,
              mk_forall(_y,
                  mk_exists(_xo, mk_eq(_y, mk_comb(_f, _xo)))))))

_ind_ind = mk_fun_ty(ind_ty, ind_ty)
_fi = Var("f", _ind_ind)
_one_one = mk_const("ONE_ONE", [(ind_ty, aty), (ind_ty, bty)])
_onto = mk_const("ONTO", [(ind_ty, aty), (ind_ty, bty)])
INFINITY_AX = new_axiom(
    mk_exists(_fi,
        mk_and(mk_comb(_one_one, _fi),
               mk_not(mk_comb(_onto, _fi)))))
