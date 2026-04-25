# HOL Light kernel of types, terms and theorems
# based on https://github.com/jrh13/hol-light/blob/master/fusion.ml

from __future__ import annotations
import sys
from dataclasses import dataclass
from typing import Callable

sys.setrecursionlimit(10000)

# ---------------------------------------------------------------------------
# Kernel exceptions
# ---------------------------------------------------------------------------

class HolError(Exception):
    pass

class Clash(Exception):
    def __init__(self, tm):
        super().__init__()
        self.tm = tm

# ---------------------------------------------------------------------------
# HOL Types
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Tyvar:
    name: str

@dataclass(frozen=True, slots=True)
class Tyapp:
    tyop: str
    args: tuple

    def __post_init__(self):
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))

hol_type = Tyvar | Tyapp

# ---------------------------------------------------------------------------
# HOL Terms
# ---------------------------------------------------------------------------

@dataclass(frozen=True, slots=True)
class Var:
    name: str
    ty: hol_type

@dataclass(frozen=True, slots=True)
class Const:
    name: str
    ty: hol_type

@dataclass(frozen=True, slots=True)
class Comb:
    fun: "term"
    arg: "term"

@dataclass(frozen=True, slots=True)
class Abs:
    bvar: Var
    body: "term"

term = Var | Const | Comb | Abs

# ---------------------------------------------------------------------------
# HOL Theorems (opaque outside kernel)
# ---------------------------------------------------------------------------

class thm:
    __slots__ = ("_asl", "_concl")

    def __init__(self, asl, concl):
        self._asl = list(asl)
        self._concl = concl

    def __repr__(self):
        return f"Sequent({self._asl!r}, {self._concl!r})"

    def __eq__(self, other):
        return (isinstance(other, thm)
                and self._asl == other._asl
                and self._concl == other._concl)

    def __hash__(self):
        return hash((tuple(self._asl), self._concl))

# ---------------------------------------------------------------------------
# Identity-preserving map (used to share subterms across substitution)
# ---------------------------------------------------------------------------

def _qmap_tuple(f, items):
    out = []
    changed = False
    for x in items:
        y = f(x)
        out.append(y)
        if y is not x:
            changed = True
    return tuple(out) if changed else items

# ---------------------------------------------------------------------------
# Type constants
# ---------------------------------------------------------------------------

the_type_constants: list = [("bool", 0), ("fun", 2)]

def types() -> list:
    return list(the_type_constants)

def get_type_arity(s: str) -> int:
    for name, arity in the_type_constants:
        if name == s:
            return arity
    raise KeyError(s)

def new_type(name: str, arity: int) -> None:
    if any(n == name for n, _ in the_type_constants):
        raise HolError(f"new_type: type {name} has already been declared")
    the_type_constants.insert(0, (name, arity))

# ---------------------------------------------------------------------------
# Basic type constructors / destructors / discriminators
# ---------------------------------------------------------------------------

def mk_type(tyop: str, args: list) -> hol_type:
    try:
        arity = get_type_arity(tyop)
    except KeyError:
        raise HolError(f"mk_type: type {tyop} has not been defined")
    if arity != len(args):
        raise HolError(f"mk_type: wrong number of arguments to {tyop}")
    return Tyapp(tyop, tuple(args))

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
# Type variables and substitution
# ---------------------------------------------------------------------------

def tyvars(ty: hol_type) -> list:
    match ty:
        case Tyapp(_, args):
            seen = []
            for a in args:
                for tv in tyvars(a):
                    if tv not in seen:
                        seen.append(tv)
            return seen
        case _:
            return [ty]

def type_subst(i: list, ty: hol_type) -> hol_type:
    match ty:
        case Tyapp(tyop, args):
            new_args = _qmap_tuple(lambda a: type_subst(i, a), args)
            return ty if new_args is args else Tyapp(tyop, new_args)
        case _:
            for src, dst in i:
                if dst == ty:
                    return src
            return ty

bool_ty: hol_type = Tyapp("bool", ())
aty: hol_type = Tyvar("A")

# ---------------------------------------------------------------------------
# Term constants
# ---------------------------------------------------------------------------

the_term_constants: list = [
    ("=", Tyapp("fun", (aty, Tyapp("fun", (aty, bool_ty))))),
]

def constants() -> list:
    return list(the_term_constants)

def get_const_type(s: str) -> hol_type:
    for name, ty in the_term_constants:
        if name == s:
            return ty
    raise KeyError(s)

def new_constant(name: str, ty: hol_type) -> None:
    if any(n == name for n, _ in the_term_constants):
        raise HolError(f"new_constant: constant {name} has already been declared")
    the_term_constants.insert(0, (name, ty))

# ---------------------------------------------------------------------------
# Type of a term
# ---------------------------------------------------------------------------

def type_of(tm: term) -> hol_type:
    match tm:
        case Var(_, ty) | Const(_, ty):
            return ty
        case Comb(fun, _):
            s_ty = type_of(fun)
            if isinstance(s_ty, Tyapp) and s_ty.tyop == "fun":
                return s_ty.args[1]
            raise HolError("type_of: ill-typed combination")
        case Abs(Var(_, vty), body):
            return Tyapp("fun", (vty, type_of(body)))
    raise HolError("type_of: ill-typed term")

# ---------------------------------------------------------------------------
# Primitive discriminators / constructors / destructors
# ---------------------------------------------------------------------------

def is_var(tm: term) -> bool:   return isinstance(tm, Var)
def is_const(tm: term) -> bool: return isinstance(tm, Const)
def is_abs(tm: term) -> bool:   return isinstance(tm, Abs)
def is_comb(tm: term) -> bool:  return isinstance(tm, Comb)

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

def mk_comb(f: term, a: term) -> term:
    f_ty = type_of(f)
    if (isinstance(f_ty, Tyapp) and f_ty.tyop == "fun"
            and f_ty.args[0] == type_of(a)):
        return Comb(f, a)
    raise HolError("mk_comb: types do not agree")

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
# Free variables
# ---------------------------------------------------------------------------

def frees(tm: term) -> list:
    match tm:
        case Var():
            return [tm]
        case Const():
            return []
        case Abs(bvar, body):
            return [v for v in frees(body) if v != bvar]
        case Comb(fun, arg):
            seen = list(frees(fun))
            for v in frees(arg):
                if v not in seen:
                    seen.append(v)
            return seen
    raise HolError("frees: ill-formed term")

def freesl(tml: list) -> list:
    seen = []
    for tm in tml:
        for v in frees(tm):
            if v not in seen:
                seen.append(v)
    return seen

def freesin(acc: list, tm: term) -> bool:
    match tm:
        case Var():
            return tm in acc
        case Const():
            return True
        case Abs(bvar, body):
            return freesin([bvar, *acc], body)
        case Comb(fun, arg):
            return freesin(acc, fun) and freesin(acc, arg)
    raise HolError("freesin: ill-formed term")

def vfree_in(v: term, tm: term) -> bool:
    match tm:
        case Abs(bvar, body):
            return v != bvar and vfree_in(v, body)
        case Comb(fun, arg):
            return vfree_in(v, fun) or vfree_in(v, arg)
        case _:
            return tm == v

def type_vars_in_term(tm: term) -> list:
    match tm:
        case Var(_, ty) | Const(_, ty):
            return tyvars(ty)
        case Comb(fun, arg):
            seen = list(type_vars_in_term(fun))
            for tv in type_vars_in_term(arg):
                if tv not in seen:
                    seen.append(tv)
            return seen
        case Abs(Var(_, vty), body):
            seen = list(tyvars(vty))
            for tv in type_vars_in_term(body):
                if tv not in seen:
                    seen.append(tv)
            return seen
    raise HolError("type_vars_in_term: ill-formed term")

# ---------------------------------------------------------------------------
# Variant (fresh variable)
# ---------------------------------------------------------------------------

def variant(avoid: list, v: term) -> term:
    if not any(vfree_in(v, t) for t in avoid):
        return v
    if isinstance(v, Var):
        return variant(avoid, Var(v.name + "'", v.ty))
    raise HolError("variant: not a variable")

# ---------------------------------------------------------------------------
# Variable substitution
# ---------------------------------------------------------------------------

def _vsubst(ilist: list, tm: term) -> term:
    match tm:
        case Var():
            for src, dst in ilist:
                if dst == tm:
                    return src
            return tm
        case Const():
            return tm
        case Comb(fun, arg):
            f2 = _vsubst(ilist, fun)
            a2 = _vsubst(ilist, arg)
            if f2 is fun and a2 is arg:
                return tm
            return Comb(f2, a2)
        case Abs(bvar, body):
            ilist2 = [(t, x) for (t, x) in ilist if x != bvar]
            if not ilist2:
                return tm
            body2 = _vsubst(ilist2, body)
            if body2 is body:
                return tm
            if any(vfree_in(bvar, t) and vfree_in(x, body) for t, x in ilist2):
                v2 = variant([body2], bvar)
                return Abs(v2, _vsubst([(v2, bvar), *ilist2], body))
            return Abs(bvar, body2)
    raise HolError("vsubst: ill-formed term")

def vsubst(theta: list) -> Callable[[term], term]:
    if not theta:
        return lambda tm: tm
    if not all(isinstance(x, Var) and type_of(t) == x.ty for t, x in theta):
        raise HolError("vsubst: Bad substitution list")
    return lambda tm: _vsubst(theta, tm)

# ---------------------------------------------------------------------------
# Type instantiation
# ---------------------------------------------------------------------------

def _inst(env: list, tyin: list, tm: term) -> term:
    match tm:
        case Var(name, ty):
            ty2 = type_subst(tyin, ty)
            tm2 = tm if ty2 is ty else Var(name, ty2)
            for orig, new in env:
                if new == tm2:
                    if orig != tm:
                        raise Clash(tm2)
                    return tm2
            return tm2
        case Const(name, ty):
            ty2 = type_subst(tyin, ty)
            return tm if ty2 is ty else Const(name, ty2)
        case Comb(fun, arg):
            f2 = _inst(env, tyin, fun)
            a2 = _inst(env, tyin, arg)
            if f2 is fun and a2 is arg:
                return tm
            return Comb(f2, a2)
        case Abs(bvar, body):
            bvar2 = _inst([], tyin, bvar)
            env2 = [(bvar, bvar2), *env]
            try:
                body2 = _inst(env2, tyin, body)
                if bvar2 is bvar and body2 is body:
                    return tm
                return Abs(bvar2, body2)
            except Clash as ex:
                if ex.tm != bvar2:
                    raise
                ifrees = [_inst([], tyin, v) for v in frees(body)]
                bvar3 = variant(ifrees, bvar2)
                z = Var(bvar3.name, bvar.ty)
                return _inst(env, tyin, Abs(z, _vsubst([(z, bvar)], body)))
    raise HolError("inst: ill-formed term")

def inst(tyin: list) -> Callable[[term], term]:
    if not tyin:
        return lambda tm: tm
    return lambda tm: _inst([], tyin, tm)

# ---------------------------------------------------------------------------
# Derived syntax
# ---------------------------------------------------------------------------

def rator(tm: term) -> term:
    if isinstance(tm, Comb):
        return tm.fun
    raise HolError("rator: Not a combination")

def rand(tm: term) -> term:
    if isinstance(tm, Comb):
        return tm.arg
    raise HolError("rand: Not a combination")

def safe_mk_eq(l: term, r: term) -> term:
    ty = type_of(l)
    eq = Const("=", Tyapp("fun", (ty, Tyapp("fun", (ty, bool_ty)))))
    return Comb(Comb(eq, l), r)

def dest_eq(tm: term):
    match tm:
        case Comb(Comb(Const("=", _), l), r):
            return l, r
    raise HolError("dest_eq")

# ---------------------------------------------------------------------------
# Alpha ordering
# ---------------------------------------------------------------------------

def _type_compare(ty1: hol_type, ty2: hol_type) -> int:
    match ty1, ty2:
        case Tyvar(n1), Tyvar(n2):
            return (n1 > n2) - (n1 < n2)
        case Tyapp(op1, args1), Tyapp(op2, args2):
            if op1 != op2:
                return (op1 > op2) - (op1 < op2)
            for a, b in zip(args1, args2):
                c = _type_compare(a, b)
                if c != 0:
                    return c
            return (len(args1) > len(args2)) - (len(args1) < len(args2))
        case Tyvar(), _:
            return -1
        case _, Tyvar():
            return 1
    return 0

_TERM_ORDER = {Const: 0, Var: 1, Comb: 2, Abs: 3}

def _term_compare(tm1: term, tm2: term) -> int:
    o1 = _TERM_ORDER[type(tm1)]
    o2 = _TERM_ORDER[type(tm2)]
    if o1 != o2:
        return (o1 > o2) - (o1 < o2)
    match tm1, tm2:
        case (Var(n1, ty1), Var(n2, ty2)) | (Const(n1, ty1), Const(n2, ty2)):
            c = (n1 > n2) - (n1 < n2)
            return c if c != 0 else _type_compare(ty1, ty2)
        case Comb(f1, a1), Comb(f2, a2):
            c = _term_compare(f1, f2)
            return c if c != 0 else _term_compare(a1, a2)
        case Abs(b1, body1), Abs(b2, body2):
            c = _term_compare(b1, b2)
            return c if c != 0 else _term_compare(body1, body2)
    return 0

def _ordav(env: list, x1: term, x2: term) -> int:
    for t1, t2 in env:
        if x1 == t1:
            return 0 if x2 == t2 else -1
        if x2 == t2:
            return 1
    return _term_compare(x1, x2)

def _orda(env: list, tm1: term, tm2: term) -> int:
    if tm1 is tm2 and all(x == y for x, y in env):
        return 0
    match tm1, tm2:
        case Var(), Var():
            return _ordav(env, tm1, tm2)
        case Const(), Const():
            return _term_compare(tm1, tm2)
        case Comb(f1, a1), Comb(f2, a2):
            c = _orda(env, f1, f2)
            return c if c != 0 else _orda(env, a1, a2)
        case (Abs(Var(_, ty1) as b1, body1),
              Abs(Var(_, ty2) as b2, body2)):
            c = _type_compare(ty1, ty2)
            return c if c != 0 else _orda([(b1, b2), *env], body1, body2)
        case _:
            o1 = _TERM_ORDER.get(type(tm1), 4)
            o2 = _TERM_ORDER.get(type(tm2), 4)
            return (o1 > o2) - (o1 < o2)

def alphaorder(tm1: term, tm2: term) -> int:
    return _orda([], tm1, tm2)

# ---------------------------------------------------------------------------
# Term set operations (assumption lists, alpha-aware sorted lists)
# ---------------------------------------------------------------------------

def term_union(l1: list, l2: list) -> list:
    result = []
    i, j = 0, 0
    while i < len(l1) and j < len(l2):
        c = alphaorder(l1[i], l2[j])
        if c == 0:
            result.append(l1[i])
            i += 1
            j += 1
        elif c < 0:
            result.append(l1[i])
            i += 1
        else:
            result.append(l2[j])
            j += 1
    result.extend(l1[i:])
    result.extend(l2[j:])
    return result

def term_remove(t: term, lst: list) -> list:
    for i, s in enumerate(lst):
        c = alphaorder(t, s)
        if c == 0:
            return lst[:i] + lst[i + 1:]
        if c < 0:
            return lst
    return lst

def term_image(f: Callable[[term], term], lst: list) -> list:
    mapped = [f(x) for x in lst]
    if all(m is x for m, x in zip(mapped, lst)):
        return lst
    result: list = []
    for x in mapped:
        result = term_union([x], result)
    return result

# ---------------------------------------------------------------------------
# Basic theorem destructors
# ---------------------------------------------------------------------------

def dest_thm(th: thm):
    return list(th._asl), th._concl

def hyp(th: thm) -> list:
    return list(th._asl)

def concl(th: thm) -> term:
    return th._concl

# ---------------------------------------------------------------------------
# Basic equality rules
# ---------------------------------------------------------------------------

def REFL(tm: term) -> thm:
    return thm([], safe_mk_eq(tm, tm))

def TRANS(th1: thm, th2: thm) -> thm:
    match th1._concl, th2._concl:
        case (Comb(Comb(Const("=", _), _) as eql, m1),
              Comb(Comb(Const("=", _), m2), r)) if alphaorder(m1, m2) == 0:
            return thm(term_union(th1._asl, th2._asl), Comb(eql, r))
    raise HolError("TRANS")

# ---------------------------------------------------------------------------
# Congruence rules
# ---------------------------------------------------------------------------

def MK_COMB(th1: thm, th2: thm) -> thm:
    match th1._concl, th2._concl:
        case (Comb(Comb(Const("=", _), l1), r1),
              Comb(Comb(Const("=", _), l2), r2)):
            r1_ty = type_of(r1)
            if (isinstance(r1_ty, Tyapp) and r1_ty.tyop == "fun"
                    and r1_ty.args[0] == type_of(r2)):
                return thm(term_union(th1._asl, th2._asl),
                           safe_mk_eq(Comb(l1, l2), Comb(r1, r2)))
            raise HolError("MK_COMB: types do not agree")
    raise HolError("MK_COMB: not both equations")

def ABS(v: term, th: thm) -> thm:
    if not isinstance(v, Var):
        raise HolError("ABS")
    match th._concl:
        case Comb(Comb(Const("=", _), l), r) if not any(vfree_in(v, t) for t in th._asl):
            return thm(th._asl, safe_mk_eq(Abs(v, l), Abs(v, r)))
    raise HolError("ABS")

# ---------------------------------------------------------------------------
# Beta conversion
# ---------------------------------------------------------------------------

def BETA(tm: term) -> thm:
    match tm:
        case Comb(Abs(bvar, body), arg) if arg == bvar:
            return thm([], safe_mk_eq(tm, body))
    raise HolError("BETA: not a trivial beta-redex")

# ---------------------------------------------------------------------------
# Deduction rules
# ---------------------------------------------------------------------------

def ASSUME(tm: term) -> thm:
    if type_of(tm) != bool_ty:
        raise HolError("ASSUME: not a proposition")
    return thm([tm], tm)

def EQ_MP(th1: thm, th2: thm) -> thm:
    match th1._concl:
        case Comb(Comb(Const("=", _), l), r) if alphaorder(l, th2._concl) == 0:
            return thm(term_union(th1._asl, th2._asl), r)
    raise HolError("EQ_MP")

def DEDUCT_ANTISYM_RULE(th1: thm, th2: thm) -> thm:
    asl1 = term_remove(th2._concl, th1._asl)
    asl2 = term_remove(th1._concl, th2._asl)
    return thm(term_union(asl1, asl2), safe_mk_eq(th1._concl, th2._concl))

# ---------------------------------------------------------------------------
# Instantiation rules
# ---------------------------------------------------------------------------

def INST_TYPE(theta: list, th: thm) -> thm:
    inst_fn = inst(theta)
    return thm(term_image(inst_fn, th._asl), inst_fn(th._concl))

def INST(theta: list, th: thm) -> thm:
    inst_fn = vsubst(theta)
    return thm(term_image(inst_fn, th._asl), inst_fn(th._concl))

# ---------------------------------------------------------------------------
# Axioms
# ---------------------------------------------------------------------------

the_axioms: list = []

def axioms() -> list:
    return list(the_axioms)

def new_axiom(tm: term) -> thm:
    if type_of(tm) != bool_ty:
        raise HolError("new_axiom: Not a proposition")
    th = thm([], tm)
    the_axioms.append(th)
    return th

# ---------------------------------------------------------------------------
# Definitions
# ---------------------------------------------------------------------------

the_definitions: list = []

def definitions() -> list:
    return list(the_definitions)

def new_basic_definition(tm: term) -> thm:
    match tm:
        case Comb(Comb(Const("=", _), Var(cname, ty)), r):
            if not freesin([], r):
                fv_names = [v.name for v in frees(r)]
                raise HolError(
                    "new_definition: term not closed: " + ", ".join(fv_names))
            allowed = tyvars(ty)
            if not all(tv in allowed for tv in type_vars_in_term(r)):
                raise HolError(
                    "new_definition: Type variables not reflected in constant")
            new_constant(cname, ty)
            c = Const(cname, ty)
            dth = thm([], safe_mk_eq(c, r))
            the_definitions.append(dth)
            return dth
        case Comb(Comb(Const("=", _), Const(cname, _)), _):
            raise HolError(f"new_basic_definition: '{cname}' is already defined")
    raise HolError("new_basic_definition")

# ---------------------------------------------------------------------------
# Type definitions
#
#          |- P t
#   ---------------------------
#       |- abs(rep a) = a
#    |- P r = (rep(abs r) = r)
# ---------------------------------------------------------------------------

def new_basic_type_definition(tyname: str, absname_repname,
                              existence_thm: thm):
    absname, repname = absname_repname
    defined_consts = {n for n, _ in the_term_constants}
    if absname in defined_consts or repname in defined_consts:
        raise HolError("new_basic_type_definition: Constant(s) already in use")
    if existence_thm._asl:
        raise HolError("new_basic_type_definition: Assumptions in theorem")
    if not isinstance(existence_thm._concl, Comb):
        raise HolError("new_basic_type_definition: Not a combination")
    P = existence_thm._concl.fun
    x = existence_thm._concl.arg
    if not freesin([], P):
        raise HolError("new_basic_type_definition: Predicate is not closed")
    tvs = sorted(type_vars_in_term(P), key=lambda tv: tv.name)
    if any(n == tyname for n, _ in the_type_constants):
        raise HolError("new_basic_type_definition: Type already defined")
    new_type(tyname, len(tvs))
    new_aty = Tyapp(tyname, tuple(tvs))
    rty = type_of(x)
    absty = Tyapp("fun", (rty, new_aty))
    repty = Tyapp("fun", (new_aty, rty))
    new_constant(absname, absty)
    new_constant(repname, repty)
    abs_c = Const(absname, absty)
    rep_c = Const(repname, repty)
    a = Var("a", new_aty)
    r = Var("r", rty)
    th1 = thm([], safe_mk_eq(Comb(abs_c, mk_comb(rep_c, a)), a))
    th2 = thm([], safe_mk_eq(Comb(P, r),
                             safe_mk_eq(mk_comb(rep_c, mk_comb(abs_c, r)), r)))
    return th1, th2

# ---------------------------------------------------------------------------
# Additional derived syntax (from end of fusion.ml)
# ---------------------------------------------------------------------------

def mk_fun_ty(ty1: hol_type, ty2: hol_type) -> hol_type:
    return mk_type("fun", [ty1, ty2])

bty: hol_type = mk_vartype("B")

def is_eq(tm: term) -> bool:
    match tm:
        case Comb(Comb(Const("=", _), _), _):
            return True
        case _:
            return False

_eq_const = mk_const("=", [])

def mk_eq(l: term, r: term) -> term:
    try:
        ty = type_of(l)
        eq_tm = inst([(ty, aty)])(_eq_const)
        return mk_comb(mk_comb(eq_tm, l), r)
    except Exception:
        raise HolError("mk_eq")

def aconv(s: term, t: term) -> bool:
    return alphaorder(s, t) == 0

def equals_thm(th: thm, th2: thm) -> bool:
    return dest_thm(th) == dest_thm(th2)
