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
    mk_abs, mk_app, mk_const, mk_eq,
)
from parser import (
    add_type, add_infix, add_binder, infix, prefix, binder, parse, parse_type,
)

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
bbb_ty = parse_type("bool -> bool -> bool")
AND_DEF = new_basic_definition(
    mk_eq(Var("/\\", bbb_ty),
          parse("\\p q. (\\f:Bbb. f p q) = (\\f:Bbb. f T T)",
                p=p, q=q, T=T, Bbb=bbb_ty)))

@infix("/\\", 30, assoc="right")
def mk_and(a, b):
    return mk_app(mk_const("/\\", []), a, b)

# (==>) = \p q. p /\ q <=> p
IMP_DEF = new_basic_definition(
    mk_eq(Var("==>", bbb_ty),
          mk_abs(p, mk_abs(q, mk_eq(mk_and(p, q), p)))))

@infix("==>", 10, assoc="right")
def mk_imp(a, b):
    return mk_app(mk_const("==>", []), a, b)

# (!) = \P:A->bool. P = \x. T
FORALL_DEF = new_basic_definition(
    mk_eq(Var("!", parse_type("(A -> bool) -> bool")),
          parse("\\P:A->bool. P = \\x:A. T", T=T)))

@binder("!")
def mk_forall(v, body):
    return mk_comb(mk_const("!", [(v.ty, aty)]), mk_abs(v, body))

# (?) = \P:A->bool. !q. (!x. P x ==> q) ==> q
EXISTS_DEF = new_basic_definition(
    mk_eq(Var("?", parse_type("(A -> bool) -> bool")),
          parse("\\P:A->bool. !q:bool. (!x:A. P x ==> q) ==> q")))

@binder("?")
def mk_exists(v, body):
    return mk_comb(mk_const("?", [(v.ty, aty)]), mk_abs(v, body))

# (\/) = \p q. !r. (p ==> r) ==> (q ==> r) ==> r
r_b = Var("r", bool_ty)
OR_DEF = new_basic_definition(
    mk_eq(Var("\\/", bbb_ty),
          mk_abs(p, mk_abs(q,
              mk_forall(r_b,
                  mk_imp(mk_imp(p, r_b),
                         mk_imp(mk_imp(q, r_b), r_b)))))))

@infix("\\/", 20, assoc="right")
def mk_or(a, b):
    return mk_app(mk_const("\\/", []), a, b)

# F = !p:bool. p
F_DEF = new_basic_definition(
    mk_eq(Var("F", bool_ty), mk_forall(p, p)))
F = mk_const("F", [])

# (~) = \p. p ==> F
NOT_DEF = new_basic_definition(
    mk_eq(Var("~", parse_type("bool -> bool")),
          parse("\\p:bool. p ==> F", F=F)))

@prefix("~")
def mk_not(t):
    return mk_comb(mk_const("~", []), t)

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

ETA_AX = new_axiom(parse("!t:A->B. (\\x:A. t x) = t"))

# ---------------------------------------------------------------------------
# Axiom 2: SELECT_AX (class.ml)    |- !P (x:A). P x ==> P((@) P)
# ---------------------------------------------------------------------------

new_constant("@", parse_type("(A -> bool) -> A"))

@binder("@")
def mk_select(v, body):
    """Build ``@v. body`` -- the SELECT-binder term picking some `v` of the
    same type with `body[v]` true (or any `v` if no such exists)."""
    return mk_comb(mk_const("@", [(v.ty, aty)]), mk_abs(v, body))

SELECT_AX = new_axiom(parse(
    "!P:A->bool. !x:A. P x ==> P (${sel} P)",
    sel=mk_const("@", [])))

# ---------------------------------------------------------------------------
# Axiom 3: INFINITY_AX (ind.ml)    |- ?f:ind->ind. ONE_ONE f /\ ~(ONTO f)
# ---------------------------------------------------------------------------

new_type("ind", 0)
ind_ty = mk_type("ind", [])

# ONE_ONE = \f:A->B. !x1 x2. f x1 = f x2 ==> x1 = x2
ONE_ONE_DEF = new_basic_definition(parse(
    "ONE_ONE = (\\f:A->B. !x1:A x2:A. f x1 = f x2 ==> x1 = x2)",
    ONE_ONE=parse_type("(A -> B) -> bool")))

# ONTO = \f:A->B. !y. ?x. y = f x
ONTO_DEF = new_basic_definition(parse(
    "ONTO = (\\f:A->B. !y:B. ?x:A. y = f x)",
    ONTO=parse_type("(A -> B) -> bool")))

INFINITY_AX = new_axiom(parse(
    "?f:ind->ind. ${oo} f /\\ ~(${onto} f)",
    oo=mk_const("ONE_ONE", [(ind_ty, aty), (ind_ty, bty)]),
    onto=mk_const("ONTO", [(ind_ty, aty), (ind_ty, bty)])))
