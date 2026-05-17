# DHOL kernel spike: Dependently-Typed Higher-Order Logic
#
# Based on the formulation in Rothgang, Rabe, Benzmueller,
# "Dependently-Typed Higher-Order Logic" (2023): HOL extended with
# dependent function types and term-indexed type families.
#
# Differences vs. fusion.py (HOL):
#
#   1. Dependent function type `Pi(x:A, B)` replaces the special "fun"
#      type constant. Non-dependent A -> B is `Pi(Var("_", A), B)` with
#      the bound variable not free in B.
#
#   2. Type constants carry a *kind*: a type-arity (number of type-variable
#      parameters) AND a tuple of term-parameter types. So `vec : nat -> tp`
#      is `new_type("vec", type_arity=0, term_params=(nat_ty,))`, and
#      `vec(3)` is `Tyapp("vec", (), (numeral_3,))`.
#
#   3. `type_of(Comb(f, a))` substitutes `a` for the Pi binder in the body,
#      so applying `f : Pi(n:nat, vec n)` to `3` yields `vec 3`.
#
#   4. `Abs(v, body)` has type `Pi(v, type_of(body))` -- abstraction always
#      yields a (possibly dependent) Pi.
#
#   5. INST / INST_TYPE propagate substitutions into type annotations
#      (Var.ty, Const.ty, Pi.bvar.ty, Tyapp.term_args), since types
#      themselves mention terms in DHOL.
#
# Deliberate simplifications vs. full DHOL (clearly marked as TODO):
#
#   - Type equality is purely *definitional* (alpha + structural). Full
#     DHOL needs *provable* type equality (e.g. `vec (n+0) == vec n` via
#     a derivation), which entangles typing and the deduction system.
#     A `TYPE_EQ` rule that lifts term equalities into type equalities
#     is sketched but does not feed back into mk_comb's domain check.
#
#   - Type-constant kinds have a flat list of term-parameter types;
#     later params cannot depend on earlier ones in a kind. (Real DHOL
#     kinds are themselves dependent: K ::= tp | (x:A) -> K.)
#
#   - No predicate subtyping, no eta in alpha-equivalence at Pi.

from __future__ import annotations
import sys
from dataclasses import dataclass
from typing import Callable

sys.setrecursionlimit(10000)


class HolError(Exception):
    pass


class Clash(Exception):
    def __init__(self, tm):
        super().__init__()
        self.tm = tm


# ---------------------------------------------------------------------------
# Types: Tyvar, Tyapp (with type AND term arguments), Pi (dependent function)
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Tyvar:
    name: str


@dataclass(frozen=True, slots=True)
class Tyapp:
    tyop: str
    type_args: tuple  # tuple[hol_type]
    term_args: tuple  # tuple[term]

    def __post_init__(self):
        if not isinstance(self.type_args, tuple):
            object.__setattr__(self, "type_args", tuple(self.type_args))
        if not isinstance(self.term_args, tuple):
            object.__setattr__(self, "term_args", tuple(self.term_args))


@dataclass(frozen=True, slots=True)
class Pi:
    bvar: "Var"
    body: "hol_type"


hol_type = Tyvar | Tyapp | Pi


# ---------------------------------------------------------------------------
# Terms (unchanged from HOL)
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
# Theorems
# ---------------------------------------------------------------------------


class thm:
    __slots__ = ("_asl", "_concl")

    def __init__(self, asl, concl):
        self._asl = list(asl)
        self._concl = concl

    def __repr__(self):
        asl = ", ".join(_pp_tm(a) for a in self._asl)
        return f"Sequent([{asl}], {_pp_tm(self._concl)})"

    def __eq__(self, other):
        return (
            isinstance(other, thm)
            and self._asl == other._asl
            and self._concl == other._concl
        )

    def __hash__(self):
        return hash((tuple(self._asl), self._concl))


# ---------------------------------------------------------------------------
# Type constants: each carries a *kind* = (type_arity, term_param_types)
# ---------------------------------------------------------------------------

# Built-in: bool is nullary. There is NO built-in "fun" -- Pi replaces it.
the_type_constants: list = [("bool", 0, ())]


def types() -> list:
    return list(the_type_constants)


def get_type_kind(s: str):
    for name, arity, params in the_type_constants:
        if name == s:
            return arity, params
    raise KeyError(s)


def new_type(name: str, type_arity: int = 0, term_params: tuple = ()) -> None:
    if any(n == name for n, _, _ in the_type_constants):
        raise HolError(f"new_type: type {name} has already been declared")
    the_type_constants.insert(0, (name, type_arity, tuple(term_params)))


# ---------------------------------------------------------------------------
# Type / term constructors
# ---------------------------------------------------------------------------


def mk_type(tyop: str, type_args: list, term_args: list = ()) -> hol_type:
    try:
        arity, term_params = get_type_kind(tyop)
    except KeyError:
        raise HolError(f"mk_type: type {tyop} has not been defined")
    if arity != len(type_args):
        raise HolError(f"mk_type: wrong number of type arguments to {tyop}")
    if len(term_params) != len(term_args):
        raise HolError(f"mk_type: wrong number of term arguments to {tyop}")
    # Check each term argument has the declared parameter type.
    # NOTE: definitional equality only; provable equality is not consulted.
    for expected, given in zip(term_params, term_args):
        if not type_eq(expected, type_of(given)):
            raise HolError(
                f"mk_type: term argument to {tyop} has wrong type "
                f"(expected {_pp_ty(expected)}, got {_pp_ty(type_of(given))})"
            )
    return Tyapp(tyop, tuple(type_args), tuple(term_args))


def mk_pi(v: "Var", body: hol_type) -> hol_type:
    return Pi(v, body)


def mk_arrow(a: hol_type, b: hol_type) -> hol_type:
    """Non-dependent function type A -> B."""
    # Use a fresh placeholder name; alpha-equivalence at Pi ignores it.
    return Pi(Var("_", a), b)


bool_ty: hol_type = Tyapp("bool", (), ())
aty: hol_type = Tyvar("A")


# ---------------------------------------------------------------------------
# Term constants
# ---------------------------------------------------------------------------

# Equality: = : A -> A -> bool, encoded as Pi(_:A, Pi(_:A, bool)).
the_term_constants: list = [
    ("=", mk_arrow(aty, mk_arrow(aty, bool_ty))),
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
# Definitional type equality (alpha at Pi, structural elsewhere)
#
# TODO: full DHOL needs *propositional* type equality. Lifting a term
# equality `|- s = t : A` to type equality `vec s == vec t` requires the
# deduction system to feed back into typing. See TYPE_EQ stub below.
# ---------------------------------------------------------------------------


def type_eq(t1: hol_type, t2: hol_type) -> bool:
    return _ty_eq([], t1, t2)


def _ty_eq(env: list, t1: hol_type, t2: hol_type) -> bool:
    if isinstance(t1, Tyvar) and isinstance(t2, Tyvar):
        return t1.name == t2.name
    if isinstance(t1, Tyapp) and isinstance(t2, Tyapp):
        if t1.tyop != t2.tyop:
            return False
        if len(t1.type_args) != len(t2.type_args):
            return False
        if len(t1.term_args) != len(t2.term_args):
            return False
        if not all(_ty_eq(env, a, b) for a, b in zip(t1.type_args, t2.type_args)):
            return False
        return all(_tm_alpha(env, a, b) for a, b in zip(t1.term_args, t2.term_args))
    if isinstance(t1, Pi) and isinstance(t2, Pi):
        if not _ty_eq(env, t1.bvar.ty, t2.bvar.ty):
            return False
        return _ty_eq([(t1.bvar, t2.bvar), *env], t1.body, t2.body)
    return False


def _tm_alpha(env: list, a: term, b: term) -> bool:
    """Alpha-equivalence of terms under a binder environment that mixes
    Pi-bound type variables and Abs-bound term variables."""
    if isinstance(a, Var) and isinstance(b, Var):
        for x, y in env:
            if a == x:
                return b == y
            if b == y:
                return False
        return a == b
    if isinstance(a, Const) and isinstance(b, Const):
        return a.name == b.name and _ty_eq(env, a.ty, b.ty)
    if isinstance(a, Comb) and isinstance(b, Comb):
        return _tm_alpha(env, a.fun, b.fun) and _tm_alpha(env, a.arg, b.arg)
    if isinstance(a, Abs) and isinstance(b, Abs):
        if not _ty_eq(env, a.bvar.ty, b.bvar.ty):
            return False
        return _tm_alpha([(a.bvar, b.bvar), *env], a.body, b.body)
    return False


# ---------------------------------------------------------------------------
# Term substitution into TYPES
#
# Needed because Tyapp now carries term arguments and Pi bodies mention
# the binder. type_of(Comb(f, a)) must substitute `a` for the Pi binder.
# ---------------------------------------------------------------------------


def subst_in_type(theta: list, ty: hol_type) -> hol_type:
    """theta : list of (replacement_term, var_to_replace)."""
    if not theta:
        return ty
    if isinstance(ty, Tyvar):
        return ty
    if isinstance(ty, Tyapp):
        new_type_args = tuple(subst_in_type(theta, a) for a in ty.type_args)
        new_term_args = tuple(_vsubst(theta, a) for a in ty.term_args)
        if (
            all(a is b for a, b in zip(new_type_args, ty.type_args))
            and all(a is b for a, b in zip(new_term_args, ty.term_args))
        ):
            return ty
        return Tyapp(ty.tyop, new_type_args, new_term_args)
    if isinstance(ty, Pi):
        # Drop any substitution targeting the bound variable.
        theta2 = [(t, x) for t, x in theta if x != ty.bvar]
        new_bvar_ty = subst_in_type(theta2, ty.bvar.ty)
        if not theta2:
            return Pi(Var(ty.bvar.name, new_bvar_ty), ty.body) if new_bvar_ty is not ty.bvar.ty else ty
        # Capture avoidance: if any replacement term has bvar free,
        # alpha-rename the binder.
        if any(vfree_in(ty.bvar, t) and _occurs_in_type(x, ty.body) for t, x in theta2):
            fresh = variant([t for t, _ in theta2] + [Var("dummy", ty.body) if False else ty.bvar for _ in [0]], ty.bvar)
            # Replace bound var with fresh in the body, then substitute.
            fresh_var = Var(fresh.name, new_bvar_ty)
            body2 = subst_in_type([(fresh_var, ty.bvar)], ty.body)
            return Pi(fresh_var, subst_in_type(theta2, body2))
        new_body = subst_in_type(theta2, ty.body)
        new_bvar = Var(ty.bvar.name, new_bvar_ty)
        return Pi(new_bvar, new_body)
    raise HolError("subst_in_type: ill-formed type")


def _occurs_in_type(v: "Var", ty: hol_type) -> bool:
    if isinstance(ty, Tyvar):
        return False
    if isinstance(ty, Tyapp):
        return any(_occurs_in_type(v, a) for a in ty.type_args) or any(
            vfree_in(v, a) for a in ty.term_args
        )
    if isinstance(ty, Pi):
        if ty.bvar == v:
            return _occurs_in_type(v, ty.bvar.ty)
        return _occurs_in_type(v, ty.bvar.ty) or _occurs_in_type(v, ty.body)
    return False


# ---------------------------------------------------------------------------
# Type variable substitution (still needed -- DHOL has type polymorphism)
# ---------------------------------------------------------------------------


def tyvars(ty: hol_type) -> list:
    if isinstance(ty, Tyvar):
        return [ty]
    if isinstance(ty, Tyapp):
        seen = []
        for a in ty.type_args:
            for tv in tyvars(a):
                if tv not in seen:
                    seen.append(tv)
        for a in ty.term_args:
            for tv in type_vars_in_term(a):
                if tv not in seen:
                    seen.append(tv)
        return seen
    if isinstance(ty, Pi):
        seen = list(tyvars(ty.bvar.ty))
        for tv in tyvars(ty.body):
            if tv not in seen:
                seen.append(tv)
        return seen
    raise HolError("tyvars: ill-formed type")


def type_subst(i: list, ty: hol_type) -> hol_type:
    """i : list of (replacement_type, tyvar_to_replace)."""
    if isinstance(ty, Tyvar):
        for src, dst in i:
            if dst == ty:
                return src
        return ty
    if isinstance(ty, Tyapp):
        new_type_args = tuple(type_subst(i, a) for a in ty.type_args)
        new_term_args = tuple(_inst_in_term(i, a) for a in ty.term_args)
        return Tyapp(ty.tyop, new_type_args, new_term_args)
    if isinstance(ty, Pi):
        new_bvar_ty = type_subst(i, ty.bvar.ty)
        new_body = type_subst(i, ty.body)
        # Refresh bvar with new type; no name capture for type vars.
        return Pi(Var(ty.bvar.name, new_bvar_ty), new_body)
    raise HolError("type_subst: ill-formed type")


def _inst_in_term(tyin: list, tm: term) -> term:
    """Apply a type-variable substitution to type annotations inside a term.
    Simplified: assumes no name clashes (sufficient for spike)."""
    if isinstance(tm, Var):
        return Var(tm.name, type_subst(tyin, tm.ty))
    if isinstance(tm, Const):
        return Const(tm.name, type_subst(tyin, tm.ty))
    if isinstance(tm, Comb):
        return Comb(_inst_in_term(tyin, tm.fun), _inst_in_term(tyin, tm.arg))
    if isinstance(tm, Abs):
        return Abs(
            Var(tm.bvar.name, type_subst(tyin, tm.bvar.ty)),
            _inst_in_term(tyin, tm.body),
        )
    raise HolError("_inst_in_term: ill-formed term")


# ---------------------------------------------------------------------------
# type_of: with Pi substitution at Comb, Pi formation at Abs
# ---------------------------------------------------------------------------


def type_of(tm: term) -> hol_type:
    if isinstance(tm, Var) or isinstance(tm, Const):
        return tm.ty
    if isinstance(tm, Comb):
        f_ty = type_of(tm.fun)
        if isinstance(f_ty, Pi):
            # Substitute the argument into the codomain.
            return subst_in_type([(tm.arg, f_ty.bvar)], f_ty.body)
        raise HolError("type_of: head of application is not a Pi")
    if isinstance(tm, Abs):
        return Pi(tm.bvar, type_of(tm.body))
    raise HolError("type_of: ill-typed term")


# ---------------------------------------------------------------------------
# mk_comb: dependent domain check + dependent codomain
# ---------------------------------------------------------------------------


def mk_comb(f: term, a: term) -> term:
    f_ty = type_of(f)
    a_ty = type_of(a)
    if not isinstance(f_ty, Pi):
        raise HolError(
            f"mk_comb: head is not a function (type {_pp_ty(f_ty)})"
        )
    if not type_eq(f_ty.bvar.ty, a_ty):
        raise HolError(
            f"mk_comb: types do not agree -- "
            f"function expects {_pp_ty(f_ty.bvar.ty)} but got {_pp_ty(a_ty)}\n"
            f"  head : {_pp_tm(f)} :: {_pp_ty(f_ty)}\n"
            f"  arg  : {_pp_tm(a)} :: {_pp_ty(a_ty)}"
        )
    return Comb(f, a)


# ---------------------------------------------------------------------------
# Pretty-printing
# ---------------------------------------------------------------------------


def _pp_ty(ty, _max=160):
    s = _pp_ty_raw(ty)
    return s if len(s) <= _max else s[: _max - 3] + "..."


def _pp_ty_raw(ty):
    if isinstance(ty, Tyvar):
        return ty.name
    if isinstance(ty, Tyapp):
        parts = []
        if ty.type_args:
            parts.append(", ".join(_pp_ty_raw(a) for a in ty.type_args))
        if ty.term_args:
            parts.append(", ".join(_pp_tm_raw(a) for a in ty.term_args))
        if not parts:
            return ty.tyop
        return f"{ty.tyop}({'; '.join(parts)})"
    if isinstance(ty, Pi):
        # Display non-dependent Pi as plain arrow.
        if not _occurs_in_type(ty.bvar, ty.body) and not _occurs_in_type_through_terms(ty.bvar, ty.body):
            return f"({_pp_ty_raw(ty.bvar.ty)} -> {_pp_ty_raw(ty.body)})"
        return f"(Pi {ty.bvar.name}:{_pp_ty_raw(ty.bvar.ty)}. {_pp_ty_raw(ty.body)})"
    return repr(ty)


def _occurs_in_type_through_terms(v: Var, ty: hol_type) -> bool:
    if isinstance(ty, Tyapp):
        return any(vfree_in(v, a) for a in ty.term_args) or any(
            _occurs_in_type_through_terms(v, a) for a in ty.type_args
        )
    if isinstance(ty, Pi):
        if ty.bvar == v:
            return False
        return _occurs_in_type_through_terms(v, ty.bvar.ty) or _occurs_in_type_through_terms(v, ty.body)
    return False


def _pp_tm(tm, _max=200):
    s = _pp_tm_raw(tm)
    return s if len(s) <= _max else s[: _max - 3] + "..."


def _pp_tm_raw(tm):
    if isinstance(tm, (Var, Const)):
        return tm.name
    if isinstance(tm, Abs):
        return f"(\\{tm.bvar.name}:{_pp_ty_raw(tm.bvar.ty)}. {_pp_tm_raw(tm.body)})"
    if isinstance(tm, Comb):
        return f"({_pp_tm_raw(tm.fun)} {_pp_tm_raw(tm.arg)})"
    return repr(tm)


# ---------------------------------------------------------------------------
# Free variables, type variables in terms
# ---------------------------------------------------------------------------


def frees(tm: term) -> list:
    if isinstance(tm, Var):
        return [tm]
    if isinstance(tm, Const):
        return []
    if isinstance(tm, Abs):
        return [v for v in frees(tm.body) if v != tm.bvar]
    if isinstance(tm, Comb):
        seen = list(frees(tm.fun))
        for v in frees(tm.arg):
            if v not in seen:
                seen.append(v)
        return seen
    raise HolError("frees: ill-formed term")


def freesin(acc: list, tm: term) -> bool:
    if isinstance(tm, Var):
        return tm in acc
    if isinstance(tm, Const):
        return True
    if isinstance(tm, Abs):
        return freesin([tm.bvar, *acc], tm.body)
    if isinstance(tm, Comb):
        return freesin(acc, tm.fun) and freesin(acc, tm.arg)
    raise HolError("freesin: ill-formed term")


def vfree_in(v: term, tm: term) -> bool:
    if isinstance(tm, Abs):
        return v != tm.bvar and vfree_in(v, tm.body)
    if isinstance(tm, Comb):
        return vfree_in(v, tm.fun) or vfree_in(v, tm.arg)
    return tm == v


def type_vars_in_term(tm: term) -> list:
    if isinstance(tm, Var) or isinstance(tm, Const):
        return tyvars(tm.ty)
    if isinstance(tm, Comb):
        seen = list(type_vars_in_term(tm.fun))
        for tv in type_vars_in_term(tm.arg):
            if tv not in seen:
                seen.append(tv)
        return seen
    if isinstance(tm, Abs):
        seen = list(tyvars(tm.bvar.ty))
        for tv in type_vars_in_term(tm.body):
            if tv not in seen:
                seen.append(tv)
        return seen
    raise HolError("type_vars_in_term: ill-formed term")


# ---------------------------------------------------------------------------
# Fresh variables
# ---------------------------------------------------------------------------


def variant(avoid: list, v: term) -> term:
    if not any(vfree_in(v, t) for t in avoid):
        return v
    if isinstance(v, Var):
        return variant(avoid, Var(v.name + "'", v.ty))
    raise HolError("variant: not a variable")


# ---------------------------------------------------------------------------
# Term substitution (capture-avoiding). Note: types of remaining vars may
# also change if the substitution mentions term vars used in dependent types
# -- but here we only substitute closed terms (per vsubst's contract).
# ---------------------------------------------------------------------------


def _vsubst(ilist: list, tm: term) -> term:
    if isinstance(tm, Var):
        for src, dst in ilist:
            if dst == tm:
                return src
        return tm
    if isinstance(tm, Const):
        return tm
    if isinstance(tm, Comb):
        f2 = _vsubst(ilist, tm.fun)
        a2 = _vsubst(ilist, tm.arg)
        if f2 is tm.fun and a2 is tm.arg:
            return tm
        return Comb(f2, a2)
    if isinstance(tm, Abs):
        ilist2 = [(t, x) for (t, x) in ilist if x != tm.bvar]
        if not ilist2:
            return tm
        body2 = _vsubst(ilist2, tm.body)
        if body2 is tm.body:
            return tm
        if any(vfree_in(tm.bvar, t) and vfree_in(x, tm.body) for t, x in ilist2):
            v2 = variant([body2], tm.bvar)
            return Abs(v2, _vsubst([(v2, tm.bvar), *ilist2], tm.body))
        return Abs(tm.bvar, body2)
    raise HolError("vsubst: ill-formed term")


def vsubst(theta: list) -> Callable[[term], term]:
    if not theta:
        return lambda tm: tm
    if not all(isinstance(x, Var) and type_eq(type_of(t), x.ty) for t, x in theta):
        raise HolError("vsubst: bad substitution list")
    return lambda tm: _vsubst(theta, tm)


# ---------------------------------------------------------------------------
# Type instantiation: substitute Tyvars for Types throughout a term,
# including in type annotations on Vars/Consts/Abs.
# ---------------------------------------------------------------------------


def _inst(env: list, tyin: list, tm: term) -> term:
    if isinstance(tm, Var):
        ty2 = type_subst(tyin, tm.ty)
        tm2 = tm if ty2 is tm.ty else Var(tm.name, ty2)
        for orig, new in env:
            if new == tm2:
                if orig != tm:
                    raise Clash(tm2)
                return tm2
        return tm2
    if isinstance(tm, Const):
        ty2 = type_subst(tyin, tm.ty)
        return tm if ty2 is tm.ty else Const(tm.name, ty2)
    if isinstance(tm, Comb):
        f2 = _inst(env, tyin, tm.fun)
        a2 = _inst(env, tyin, tm.arg)
        if f2 is tm.fun and a2 is tm.arg:
            return tm
        return Comb(f2, a2)
    if isinstance(tm, Abs):
        bvar2 = _inst([], tyin, tm.bvar)
        env2 = [(tm.bvar, bvar2), *env]
        try:
            body2 = _inst(env2, tyin, tm.body)
            if bvar2 is tm.bvar and body2 is tm.body:
                return tm
            return Abs(bvar2, body2)
        except Clash as ex:
            if ex.tm != bvar2:
                raise
            ifrees = [_inst([], tyin, v) for v in frees(tm.body)]
            bvar3 = variant(ifrees, bvar2)
            z = Var(bvar3.name, tm.bvar.ty)
            return _inst(env, tyin, Abs(z, _vsubst([(z, tm.bvar)], tm.body)))
    raise HolError("inst: ill-formed term")


def inst(tyin: list) -> Callable[[term], term]:
    if not tyin:
        return lambda tm: tm
    return lambda tm: _inst([], tyin, tm)


# ---------------------------------------------------------------------------
# Equality construction
# ---------------------------------------------------------------------------


def safe_mk_eq(lhs: term, r: term) -> term:
    ty = type_of(lhs)
    eq = Const("=", mk_arrow(ty, mk_arrow(ty, bool_ty)))
    return Comb(Comb(eq, lhs), r)


# ---------------------------------------------------------------------------
# Alpha ordering for term-union assumption lists
# ---------------------------------------------------------------------------


def alphaorder(tm1: term, tm2: term) -> int:
    if _tm_alpha([], tm1, tm2):
        return 0
    # Fall back to a total order via repr; sufficient for this spike.
    r1, r2 = repr(tm1), repr(tm2)
    return (r1 > r2) - (r1 < r2)


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
    for k, s in enumerate(lst):
        if alphaorder(t, s) == 0:
            return lst[:k] + lst[k + 1 :]
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
# Theorem destructors
# ---------------------------------------------------------------------------


def dest_thm(th: thm):
    return list(th._asl), th._concl


def hyp(th: thm) -> list:
    return list(th._asl)


def concl(th: thm) -> term:
    return th._concl


# ---------------------------------------------------------------------------
# Inference rules. Each closely mirrors fusion.py; the changes are in the
# typing primitives they call (mk_comb, type_of, etc.).
# ---------------------------------------------------------------------------


def REFL(tm: term) -> thm:
    return thm([], safe_mk_eq(tm, tm))


def TRANS(th1: thm, th2: thm) -> thm:
    c1, c2 = th1._concl, th2._concl
    if (
        isinstance(c1, Comb) and isinstance(c1.fun, Comb)
        and isinstance(c1.fun.fun, Const) and c1.fun.fun.name == "="
        and isinstance(c2, Comb) and isinstance(c2.fun, Comb)
        and isinstance(c2.fun.fun, Const) and c2.fun.fun.name == "="
        and alphaorder(c1.arg, c2.fun.arg) == 0
    ):
        return thm(term_union(th1._asl, th2._asl), Comb(c1.fun, c2.arg))
    raise HolError("TRANS")


def MK_COMB(th1: thm, th2: thm) -> thm:
    c1, c2 = th1._concl, th2._concl
    if not (
        isinstance(c1, Comb) and isinstance(c1.fun, Comb)
        and isinstance(c1.fun.fun, Const) and c1.fun.fun.name == "="
        and isinstance(c2, Comb) and isinstance(c2.fun, Comb)
        and isinstance(c2.fun.fun, Const) and c2.fun.fun.name == "="
    ):
        raise HolError("MK_COMB: not both equations")
    l1, r1 = c1.fun.arg, c1.arg
    l2, r2 = c2.fun.arg, c2.arg
    f_ty = type_of(l1)
    if isinstance(f_ty, Pi) and type_eq(f_ty.bvar.ty, type_of(l2)):
        return thm(
            term_union(th1._asl, th2._asl),
            safe_mk_eq(Comb(l1, l2), Comb(r1, r2)),
        )
    raise HolError("MK_COMB: types do not agree")


def ABS(v: term, th: thm) -> thm:
    if not isinstance(v, Var):
        raise HolError("ABS: not a variable")
    c = th._concl
    if (
        isinstance(c, Comb) and isinstance(c.fun, Comb)
        and isinstance(c.fun.fun, Const) and c.fun.fun.name == "="
        and not any(vfree_in(v, t) for t in th._asl)
    ):
        l, r = c.fun.arg, c.arg
        return thm(th._asl, safe_mk_eq(Abs(v, l), Abs(v, r)))
    raise HolError("ABS")


def BETA(tm: term) -> thm:
    if (
        isinstance(tm, Comb) and isinstance(tm.fun, Abs)
        and tm.arg == tm.fun.bvar
    ):
        return thm([], safe_mk_eq(tm, tm.fun.body))
    raise HolError("BETA: not a trivial beta-redex")


def ASSUME(tm: term) -> thm:
    if not type_eq(type_of(tm), bool_ty):
        raise HolError("ASSUME: not a proposition")
    return thm([tm], tm)


def EQ_MP(th1: thm, th2: thm) -> thm:
    c = th1._concl
    if (
        isinstance(c, Comb) and isinstance(c.fun, Comb)
        and isinstance(c.fun.fun, Const) and c.fun.fun.name == "="
        and alphaorder(c.fun.arg, th2._concl) == 0
    ):
        return thm(term_union(th1._asl, th2._asl), c.arg)
    raise HolError("EQ_MP")


def DEDUCT_ANTISYM_RULE(th1: thm, th2: thm) -> thm:
    asl1 = term_remove(th2._concl, th1._asl)
    asl2 = term_remove(th1._concl, th2._asl)
    return thm(term_union(asl1, asl2), safe_mk_eq(th1._concl, th2._concl))


def INST_TYPE(theta: list, th: thm) -> thm:
    inst_fn = inst(theta)
    return thm(term_image(inst_fn, th._asl), inst_fn(th._concl))


def INST(theta: list, th: thm) -> thm:
    inst_fn = vsubst(theta)
    return thm(term_image(inst_fn, th._asl), inst_fn(th._concl))


# ---------------------------------------------------------------------------
# TYPE_EQ: sketch of lifting term equality to type equality.
#
# In full DHOL, from `|- s = t : A` one can derive `T(s) == T(t)` for any
# type family T. The kernel would need a rule like:
#
#     |- s = t : A     T : A -> tp
#     ----------------------------    (TYPE_EQ_CONG)
#         |- T(s) == T(t)
#
# Then mk_comb / type_of would consult provable type equalities. Wiring
# that in cleanly means either:
#   (a) Making typing a derivation (judgement-as-theorem), OR
#   (b) A confluent rewriting system on types that the kernel runs.
#
# For this spike we leave the rule unimplemented and stick to definitional
# type equality. Downstream proof scripts must α-rename / β-normalize
# indices themselves before applying rules.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Axioms and definitions (HOL Light style)
# ---------------------------------------------------------------------------

the_axioms: list = []


def axioms() -> list:
    return list(the_axioms)


def new_axiom(tm: term) -> thm:
    if not type_eq(type_of(tm), bool_ty):
        raise HolError("new_axiom: not a proposition")
    th = thm([], tm)
    the_axioms.append(th)
    return th


the_definitions: list = []


def definitions() -> list:
    return list(the_definitions)


def new_basic_definition(tm: term) -> thm:
    if not (
        isinstance(tm, Comb) and isinstance(tm.fun, Comb)
        and isinstance(tm.fun.fun, Const) and tm.fun.fun.name == "="
    ):
        raise HolError("new_basic_definition: not an equation")
    lhs, r = tm.fun.arg, tm.arg
    if isinstance(lhs, Const):
        raise HolError(f"new_basic_definition: '{lhs.name}' is already defined")
    if not isinstance(lhs, Var):
        raise HolError("new_basic_definition: lhs is not a variable")
    if not freesin([], r):
        fv_names = [v.name for v in frees(r)]
        raise HolError(
            "new_definition: term not closed: " + ", ".join(fv_names)
        )
    allowed = tyvars(lhs.ty)
    if not all(tv in allowed for tv in type_vars_in_term(r)):
        raise HolError("new_definition: type variables not reflected in constant")
    new_constant(lhs.name, lhs.ty)
    c = Const(lhs.name, lhs.ty)
    dth = thm([], safe_mk_eq(c, r))
    the_definitions.append(dth)
    return dth


# new_basic_type_definition is omitted for this spike. The HOL-style
# version goes through; the only change is that `abs`/`rep` constants
# now have Pi types `Pi(r:rty, new_aty)` rather than `rty -> new_aty`,
# and `new_aty` is `Tyapp(tyname, tvs, ())` (or with term args if the
# definition introduces a term-indexed family).


# ---------------------------------------------------------------------------
# Demo: vectors indexed by nat
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    # Declare nat as a base type and 0, S, vec, nil, cons as constants.
    new_type("nat", type_arity=0, term_params=())
    nat_ty = Tyapp("nat", (), ())

    new_constant("0", nat_ty)
    new_constant("S", mk_arrow(nat_ty, nat_ty))

    zero = Const("0", nat_ty)
    succ = Const("S", mk_arrow(nat_ty, nat_ty))
    one = Comb(succ, zero)
    two = Comb(succ, one)

    # vec : nat -> tp   (a term-indexed type family)
    new_type("vec", type_arity=0, term_params=(nat_ty,))

    def vec(n):
        return mk_type("vec", [], [n])

    # nil : vec 0
    new_constant("nil", vec(zero))
    nil = Const("nil", vec(zero))

    # cons : Pi (n:nat). nat -> vec n -> vec (S n)
    n_var = Var("n", nat_ty)
    cons_ty = Pi(
        n_var,
        mk_arrow(nat_ty, mk_arrow(vec(n_var), vec(Comb(succ, n_var)))),
    )
    new_constant("cons", cons_ty)
    cons = Const("cons", cons_ty)

    # Build cons 0 (the head element) nil  -- but cons takes n first.
    # cons applied to 0 has type:  nat -> vec 0 -> vec (S 0)
    cons_0 = mk_comb(cons, zero)
    print("cons 0  ::", _pp_ty(type_of(cons_0)))

    # cons 0 5? we don't have a numeral; pretend cons 0 zero nil makes sense.
    cons_0_zero = mk_comb(cons_0, zero)
    print("cons 0 0  ::", _pp_ty(type_of(cons_0_zero)))

    v1 = mk_comb(cons_0_zero, nil)
    print("cons 0 0 nil  ::", _pp_ty(type_of(v1)))

    # And a longer one: cons 1 0 (cons 0 0 nil)  :  vec (S (S 0))
    cons_1 = mk_comb(cons, one)
    cons_1_zero = mk_comb(cons_1, zero)
    v2 = mk_comb(cons_1_zero, v1)
    print("cons 1 0 (cons 0 0 nil)  ::", _pp_ty(type_of(v2)))

    # Domain check: feeding a vec 0 where a vec (S 0) is expected fails.
    try:
        mk_comb(cons_1_zero, nil)  # expects vec (S 0), got vec 0
    except HolError as e:
        print("expected failure:", str(e).splitlines()[0])
