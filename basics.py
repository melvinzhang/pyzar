# Derived term/type syntax built on the HOL Light kernel.
# Mirrors the helpers in https://github.com/jrh13/hol-light/blob/master/basics.ml

from fusion import (
    Tyvar, Tyapp,
    Var, Comb, Const, Abs,
    HolError,
    aty,
    alphaorder,
    dest_thm,
    frees,
    get_const_type,
    inst,
    mk_comb, mk_type,
    type_of, type_subst,
    term, hol_type, thm,
)

# ---------------------------------------------------------------------------
# Type discriminators / constructors / destructors
# ---------------------------------------------------------------------------

def mk_vartype(v: str) -> hol_type:
    return Tyvar(v)

def dest_type(ty: hol_type):
    match ty:
        case Tyapp(tyop, args):
            return tyop, list(args)
    raise HolError("dest_type: type variable not a constructor")

def dest_vartype(ty: hol_type) -> str:
    match ty:
        case Tyvar(name):
            return name
    raise HolError("dest_vartype: type constructor not a variable")

def is_type(ty: hol_type) -> bool:
    return isinstance(ty, Tyapp)

def is_vartype(ty: hol_type) -> bool:
    return isinstance(ty, Tyvar)

# ---------------------------------------------------------------------------
# Term constructors
# ---------------------------------------------------------------------------

def mk_var(v: str, ty: hol_type) -> term:
    return Var(v, ty)

def mk_const(name: str, theta: list) -> term:
    try:
        uty = get_const_type(name)
    except KeyError:
        raise HolError("mk_const: not a constant name")
    return Const(name, type_subst(theta, uty))

def mk_abs(bvar: term, body: term) -> term:
    if not isinstance(bvar, Var):
        raise HolError("mk_abs: not a variable")
    return Abs(bvar, body)

# ---------------------------------------------------------------------------
# Term discriminators
# ---------------------------------------------------------------------------

def is_var(tm: term) -> bool:   return isinstance(tm, Var)
def is_const(tm: term) -> bool: return isinstance(tm, Const)
def is_abs(tm: term) -> bool:   return isinstance(tm, Abs)
def is_comb(tm: term) -> bool:  return isinstance(tm, Comb)

# ---------------------------------------------------------------------------
# Term destructors
# ---------------------------------------------------------------------------

def dest_var(tm: term):
    if isinstance(tm, Var):
        return tm.name, tm.ty
    raise HolError("dest_var: not a variable")

def dest_const(tm: term):
    if isinstance(tm, Const):
        return tm.name, tm.ty
    raise HolError("dest_const: not a constant")

def dest_comb(tm: term):
    if isinstance(tm, Comb):
        return tm.fun, tm.arg
    raise HolError("dest_comb: not a combination")

def dest_abs(tm: term):
    if isinstance(tm, Abs):
        return tm.bvar, tm.body
    raise HolError("dest_abs: not an abstraction")

# ---------------------------------------------------------------------------
# Iterated combination
# ---------------------------------------------------------------------------

def mk_app(f: term, *args: term) -> term:
    """Left-associated application: ``mk_app(f, a, b, c) == f a b c``."""
    for a in args:
        f = mk_comb(f, a)
    return f

# ---------------------------------------------------------------------------
# Connective shape helpers: name-parametric structural checks for terms of
# the form ``op a b`` (binop), ``op x`` (unop), or ``op (\\v. body)``
# (binder). ``is_*`` returns bool; ``dest_*`` returns the unpacked pieces
# on match and ``None`` otherwise, so callers can write
# ``if (parts := dest_binop(name, tm)) is not None: a, b = parts``.
# ---------------------------------------------------------------------------

def is_binop(name: str, tm: term) -> bool:
    return (isinstance(tm, Comb) and isinstance(tm.fun, Comb)
            and isinstance(tm.fun.fun, Const) and tm.fun.fun.name == name)

def dest_binop(name: str, tm: term):
    if is_binop(name, tm):
        return (tm.fun.arg, tm.arg)
    return None

def dest_binop_any(tm: term):
    """If tm = op a b for some Const op, return (op_name, a, b); else None."""
    if (isinstance(tm, Comb) and isinstance(tm.fun, Comb)
            and isinstance(tm.fun.fun, Const)):
        return (tm.fun.fun.name, tm.fun.arg, tm.arg)
    return None

def is_unop(name: str, tm: term) -> bool:
    return (isinstance(tm, Comb) and isinstance(tm.fun, Const)
            and tm.fun.name == name)

def dest_unop(name: str, tm: term):
    if is_unop(name, tm):
        return tm.arg
    return None

def is_binder(name: str, tm: term) -> bool:
    return is_unop(name, tm) and isinstance(tm.arg, Abs)

def dest_binder(name: str, tm: term):
    """If tm = `name` (\\v. body), return the Abs (\\v. body); else None."""
    if is_binder(name, tm):
        return tm.arg
    return None

# ---------------------------------------------------------------------------
# Free variables (list-of-terms convenience)
# ---------------------------------------------------------------------------

def freesl(tml: list) -> list:
    seen = []
    for tm in tml:
        for v in frees(tm):
            if v not in seen:
                seen.append(v)
    return seen

# ---------------------------------------------------------------------------
# Combination accessors
# ---------------------------------------------------------------------------

def rator(tm: term) -> term:
    if isinstance(tm, Comb):
        return tm.fun
    raise HolError("rator: Not a combination")

def rand(tm: term) -> term:
    if isinstance(tm, Comb):
        return tm.arg
    raise HolError("rand: Not a combination")

# ---------------------------------------------------------------------------
# Function types
# ---------------------------------------------------------------------------

def mk_fun_ty(ty1: hol_type, ty2: hol_type) -> hol_type:
    return mk_type("fun", [ty1, ty2])

bty: hol_type = mk_vartype("B")

# ---------------------------------------------------------------------------
# Equality
# ---------------------------------------------------------------------------

def is_eq(tm: term) -> bool:
    match tm:
        case Comb(Comb(Const("=", _), _), _):
            return True
        case _:
            return False

def dest_eq(tm: term):
    match tm:
        case Comb(Comb(Const("=", _), l), r):
            return l, r
    raise HolError("dest_eq")

_eq_const = mk_const("=", [])

def mk_eq(l: term, r: term) -> term:
    try:
        ty = type_of(l)
        eq_tm = inst([(ty, aty)])(_eq_const)
        return mk_app(eq_tm, l, r)
    except Exception:
        raise HolError("mk_eq")

# ---------------------------------------------------------------------------
# Alpha equivalence and theorem equality
# ---------------------------------------------------------------------------

def aconv(s: term, t: term) -> bool:
    return alphaorder(s, t) == 0

def equals_thm(th: thm, th2: thm) -> bool:
    return dest_thm(th) == dest_thm(th2)
