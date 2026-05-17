# DHOL kernel with typing as derivation
#
# Based on Rothgang/Rabe/Benzmueller, "Dependently-Typed Higher-Order Logic"
# (ACM TOCL, 2025; arXiv:2305.15382). Term well-typedness is itself a
# judgement, not a meta-level function. The kernel exposes three families
# of certificates:
#
#   typing_thm    Gamma |- t : A           (well-typed term)
#   type_eq_thm   Gamma |- A == B          (propositional type equality)
#   thm           Gamma |- F               (validity, as in HOL)
#
# Every term that enters a theorem has been built by typing rules, so its
# well-typedness is witnessed by a typing_thm whose asl already contains
# whatever boolean assumptions Gamma needs. The dependent application rule
# (appl' in the paper):
#
#     Gamma |- f : Pi(x:A). B    Gamma |- a : A
#     ------------------------------------------
#                Gamma |- f a : B[x/a]
#
# is implemented as APP(f_th, a_th, eq=None) where eq witnesses the
# propositional bridge expected ~ got when typing wouldn't otherwise agree
# definitionally. Type equality is derived from term equality via
# TY_CONG_BASE (congBase' in the paper) and Pi-congruence via TY_CONG_PI.
#
# Variables carry their types intrinsically (Var.name, Var.ty), so the
# "x:A in Gamma" portion of a context is implicit -- a typing_thm produced
# by VAR(Var("x", A)) is justified under any Gamma that binds x at A.
# The boolean portion of Gamma lives in typing_thm._asl, just like thm._asl.
#
# Deliberate spike-level simplifications:
#   - INST / INST_TYPE require definitionally-matching types; substitutions
#     that need propositional bridges must be built via APP + CONV.
#   - new_basic_type_definition is omitted.
#   - eta is not part of alpha at Pi.

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
# Types
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Tyvar:
    name: str


@dataclass(frozen=True, slots=True)
class Tyapp:
    tyop: str
    type_args: tuple
    term_args: tuple

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
# Terms
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
# Certificates
# ---------------------------------------------------------------------------


class typing_thm:
    """Gamma |- t : A."""

    __slots__ = ("_asl", "_tm", "_ty")

    def __init__(self, asl, tm, ty):
        self._asl = list(asl)
        self._tm = tm
        self._ty = ty

    def __repr__(self):
        a = ", ".join(_pp_tm(x) for x in self._asl)
        return f"[{a}] |- {_pp_tm(self._tm)} : {_pp_ty(self._ty)}"


class type_eq_thm:
    """Gamma |- A == B."""

    __slots__ = ("_asl", "_lhs", "_rhs")

    def __init__(self, asl, lhs, rhs):
        self._asl = list(asl)
        self._lhs = lhs
        self._rhs = rhs

    def __repr__(self):
        a = ", ".join(_pp_tm(x) for x in self._asl)
        return f"[{a}] |- {_pp_ty(self._lhs)} == {_pp_ty(self._rhs)}"


class thm:
    """Gamma |- F  (boolean validity)."""

    __slots__ = ("_asl", "_concl")

    def __init__(self, asl, concl):
        self._asl = list(asl)
        self._concl = concl

    def __repr__(self):
        a = ", ".join(_pp_tm(x) for x in self._asl)
        return f"Sequent([{a}], {_pp_tm(self._concl)})"

    def __eq__(self, other):
        return (
            isinstance(other, thm)
            and self._asl == other._asl
            and self._concl == other._concl
        )

    def __hash__(self):
        return hash((tuple(self._asl), self._concl))


# ---------------------------------------------------------------------------
# Type constants (kinded) and term constants
# ---------------------------------------------------------------------------

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


bool_ty: hol_type = Tyapp("bool", (), ())
aty: hol_type = Tyvar("A")

the_term_constants: list = [
    ("=", Pi(Var("_", aty), Pi(Var("_", aty), bool_ty))),
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


def mk_arrow(a: hol_type, b: hol_type) -> hol_type:
    return Pi(Var("_", a), b)


def mk_type(tyop: str, type_args: list, term_arg_typings: list = ()) -> hol_type:
    """Build a Tyapp from a type-constant name and certified term arguments.
    Each entry in term_arg_typings must be a typing_thm. For this spike the
    asls of those typing_thms must be empty (so the resulting type is
    well-formed absolutely)."""
    try:
        arity, params = get_type_kind(tyop)
    except KeyError:
        raise HolError(f"mk_type: type {tyop} has not been defined")
    if arity != len(type_args):
        raise HolError(f"mk_type: wrong number of type arguments to {tyop}")
    if len(params) != len(term_arg_typings):
        raise HolError(f"mk_type: wrong number of term arguments to {tyop}")
    args = []
    for expected, ath in zip(params, term_arg_typings):
        if not isinstance(ath, typing_thm):
            raise HolError("mk_type: term arguments must be typing_thms")
        if ath._asl:
            raise HolError("mk_type: term-argument typing must be unconditional")
        if not type_eq(expected, ath._ty):
            raise HolError(
                f"mk_type: term argument has wrong type "
                f"(expected {_pp_ty(expected)}, got {_pp_ty(ath._ty)})"
            )
        args.append(ath._tm)
    return Tyapp(tyop, tuple(type_args), tuple(args))


# ---------------------------------------------------------------------------
# Free variables, type variables
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


def tyvars(ty: hol_type) -> list:
    if isinstance(ty, Tyvar):
        return [ty]
    if isinstance(ty, Tyapp):
        seen: list = []
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


def variant(avoid: list, v: term) -> term:
    if not any(vfree_in(v, t) for t in avoid):
        return v
    if isinstance(v, Var):
        return variant(avoid, Var(v.name + "'", v.ty))
    raise HolError("variant: not a variable")


# ---------------------------------------------------------------------------
# Definitional type equality (alpha at Pi, alpha at term indices)
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
# Term substitution into types (capture avoiding)
# ---------------------------------------------------------------------------


def subst_in_type(theta: list, ty: hol_type) -> hol_type:
    if not theta:
        return ty
    if isinstance(ty, Tyvar):
        return ty
    if isinstance(ty, Tyapp):
        new_type_args = tuple(subst_in_type(theta, a) for a in ty.type_args)
        new_term_args = tuple(_vsubst(theta, a) for a in ty.term_args)
        return Tyapp(ty.tyop, new_type_args, new_term_args)
    if isinstance(ty, Pi):
        theta2 = [(t, x) for t, x in theta if x != ty.bvar]
        new_bvar_ty = subst_in_type(theta2, ty.bvar.ty)
        if not theta2:
            return Pi(Var(ty.bvar.name, new_bvar_ty), ty.body)
        if any(
            vfree_in(ty.bvar, t) and _occurs_in_type(x, ty.body)
            for t, x in theta2
        ):
            avoid = [t for t, _ in theta2]
            fresh = variant(avoid, ty.bvar)
            fresh_var = Var(fresh.name, new_bvar_ty)
            body2 = subst_in_type([(fresh_var, ty.bvar)], ty.body)
            return Pi(fresh_var, subst_in_type(theta2, body2))
        new_body = subst_in_type(theta2, ty.body)
        return Pi(Var(ty.bvar.name, new_bvar_ty), new_body)
    raise HolError("subst_in_type: ill-formed type")


def _occurs_in_type(v: Var, ty: hol_type) -> bool:
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
# Type-variable substitution
# ---------------------------------------------------------------------------


def type_subst(i: list, ty: hol_type) -> hol_type:
    if not i:
        return ty
    if isinstance(ty, Tyvar):
        for src, dst in i:
            if dst == ty:
                return src
        return ty
    if isinstance(ty, Tyapp):
        return Tyapp(
            ty.tyop,
            tuple(type_subst(i, a) for a in ty.type_args),
            tuple(_inst_in_term([], i, a) for a in ty.term_args),
        )
    if isinstance(ty, Pi):
        return Pi(
            Var(ty.bvar.name, type_subst(i, ty.bvar.ty)),
            type_subst(i, ty.body),
        )
    raise HolError("type_subst: ill-formed type")


def _inst_in_term(env: list, tyin: list, tm: term) -> term:
    """Type-variable instantiation with capture-avoiding rename. env
    pairs original bound variables with their type-instantiated images;
    when a free variable in the body collides with a renamed binder we
    raise Clash, which the Abs case catches and recovers by alpha-
    renaming the binder before retrying."""
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
        f2 = _inst_in_term(env, tyin, tm.fun)
        a2 = _inst_in_term(env, tyin, tm.arg)
        if f2 is tm.fun and a2 is tm.arg:
            return tm
        return Comb(f2, a2)
    if isinstance(tm, Abs):
        bvar2 = _inst_in_term([], tyin, tm.bvar)
        env2 = [(tm.bvar, bvar2), *env]
        try:
            body2 = _inst_in_term(env2, tyin, tm.body)
            if bvar2 is tm.bvar and body2 is tm.body:
                return tm
            return Abs(bvar2, body2)
        except Clash as ex:
            if ex.tm != bvar2:
                raise
            ifrees = [_inst_in_term([], tyin, v) for v in frees(tm.body)]
            bvar3 = variant(ifrees, bvar2)
            z = Var(bvar3.name, tm.bvar.ty)
            return _inst_in_term(
                env, tyin, Abs(z, _vsubst([(z, tm.bvar)], tm.body))
            )
    raise HolError("_inst_in_term: ill-formed term")


# ---------------------------------------------------------------------------
# Term-variable substitution (capture avoiding)
# ---------------------------------------------------------------------------


def _vsubst(ilist: list, tm: term) -> term:
    """DHOL-aware capture-avoiding term substitution. Also propagates the
    substitution into type annotations of Var/Const/Abs binders, since a
    Var's declared type may mention term variables being substituted."""
    if isinstance(tm, Var):
        for src, dst in ilist:
            if dst == tm:
                return src
        new_ty = subst_in_type(ilist, tm.ty)
        return tm if new_ty is tm.ty else Var(tm.name, new_ty)
    if isinstance(tm, Const):
        new_ty = subst_in_type(ilist, tm.ty)
        return tm if new_ty is tm.ty else Const(tm.name, new_ty)
    if isinstance(tm, Comb):
        return Comb(_vsubst(ilist, tm.fun), _vsubst(ilist, tm.arg))
    if isinstance(tm, Abs):
        ilist2 = [(t, x) for (t, x) in ilist if x != tm.bvar]
        new_bvar_ty = subst_in_type(ilist, tm.bvar.ty)
        new_bvar = (
            tm.bvar if new_bvar_ty is tm.bvar.ty
            else Var(tm.bvar.name, new_bvar_ty)
        )
        if not ilist2:
            return tm if new_bvar is tm.bvar else Abs(new_bvar, tm.body)
        if any(vfree_in(new_bvar, t) and vfree_in(x, tm.body) for t, x in ilist2):
            v2 = variant([_vsubst(ilist2, tm.body)], new_bvar)
            return Abs(v2, _vsubst([(v2, tm.bvar), *ilist2], tm.body))
        return Abs(new_bvar, _vsubst(ilist2, tm.body))
    raise HolError("vsubst: ill-formed term")


# ---------------------------------------------------------------------------
# Pretty printing
# ---------------------------------------------------------------------------


def _pp_ty(ty, _max=180):
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
        if not _occurs_in_type(ty.bvar, ty.body):
            return f"({_pp_ty_raw(ty.bvar.ty)} -> {_pp_ty_raw(ty.body)})"
        return f"(Pi {ty.bvar.name}:{_pp_ty_raw(ty.bvar.ty)}. {_pp_ty_raw(ty.body)})"
    return repr(ty)


def _pp_tm(tm, _max=220):
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
# type_of (pure function: terms inside certificates are well-formed by
# construction, so this always succeeds on them)
# ---------------------------------------------------------------------------


def type_of(tm: term) -> hol_type:
    if isinstance(tm, Var) or isinstance(tm, Const):
        return tm.ty
    if isinstance(tm, Comb):
        f_ty = type_of(tm.fun)
        if isinstance(f_ty, Pi):
            return subst_in_type([(tm.arg, f_ty.bvar)], f_ty.body)
        raise HolError("type_of: head of application is not a Pi")
    if isinstance(tm, Abs):
        return Pi(tm.bvar, type_of(tm.body))
    raise HolError("type_of: ill-typed term")


# ---------------------------------------------------------------------------
# Term-set operations (alpha-aware assumption lists)
# ---------------------------------------------------------------------------


def alphaorder(tm1: term, tm2: term) -> int:
    if _tm_alpha([], tm1, tm2):
        return 0
    r1, r2 = repr(tm1), repr(tm2)
    return (r1 > r2) - (r1 < r2)


def term_union(l1: list, l2: list) -> list:
    result: list = []
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
# Equation helpers (terms of shape Comb(Comb(Const("=",_), s), t))
# ---------------------------------------------------------------------------


def _is_eq(c: term) -> bool:
    return (
        isinstance(c, Comb)
        and isinstance(c.fun, Comb)
        and isinstance(c.fun.fun, Const)
        and c.fun.fun.name == "="
    )


def _lhs(c: term) -> term:
    return c.fun.arg


def _rhs(c: term) -> term:
    return c.arg


def safe_mk_eq(lhs: term, r: term) -> term:
    ty = type_of(lhs)
    eq_ty = Pi(Var("_", ty), Pi(Var("_", ty), bool_ty))
    return Comb(Comb(Const("=", eq_ty), lhs), r)


# ---------------------------------------------------------------------------
# Typing rules: VAR, CONST, APP, LAMBDA, CONV
#
# These are the *only* legal ways to build a typing_thm. Term construction
# outside of these rules has no certifying force.
# ---------------------------------------------------------------------------


def VAR(v: Var) -> typing_thm:
    """var-intro: Gamma, x:A |- x : A  (the x:A binding is intrinsic to v)."""
    return typing_thm([], v, v.ty)


def CONST(name: str, tyin: list = ()) -> typing_thm:
    """const-intro: |- c : tyin(A) where c:A is in the theory."""
    decl_ty = get_const_type(name)
    inst_ty = type_subst(tyin, decl_ty)
    return typing_thm([], Const(name, inst_ty), inst_ty)


def APP(f_th: typing_thm, a_th: typing_thm,
        eq: type_eq_thm | None = None) -> typing_thm:
    """appl':  Gamma |- f : Pi(x:A). B   Gamma |- a : A
              ------------------------------------------
                        Gamma |- f a : B[x/a]

    If type_of(a) doesn't match A definitionally, eq must witness A == A'."""
    f_ty = f_th._ty
    if not isinstance(f_ty, Pi):
        raise HolError(f"APP: head not a Pi -- got {_pp_ty(f_ty)}")
    expected = f_ty.bvar.ty
    got = a_th._ty
    asl = term_union(f_th._asl, a_th._asl)
    if not type_eq(expected, got):
        if eq is None:
            raise HolError(
                f"APP: domain mismatch -- expected {_pp_ty(expected)}, "
                f"got {_pp_ty(got)} (no bridge supplied)"
            )
        if not _bridge_matches(eq, expected, got):
            raise HolError(
                f"APP: bridge does not match -- "
                f"witness {_pp_ty(eq._lhs)} == {_pp_ty(eq._rhs)} "
                f"does not connect {_pp_ty(expected)} and {_pp_ty(got)}"
            )
        asl = term_union(asl, eq._asl)
    result_ty = subst_in_type([(a_th._tm, f_ty.bvar)], f_ty.body)
    return typing_thm(asl, Comb(f_th._tm, a_th._tm), result_ty)


def LAMBDA(v: Var, body_th: typing_thm) -> typing_thm:
    """lambda':  Gamma, x:A |- t : B
                ----------------------------
                Gamma |- (\\x:A. t) : Pi(x:A). B
    Any assumption mentioning v is discharged (it's no longer in scope)."""
    asl = [a for a in body_th._asl if not vfree_in(v, a)]
    return typing_thm(asl, Abs(v, body_th._tm), Pi(v, body_th._ty))


def CONV(t_th: typing_thm, eq: type_eq_thm) -> typing_thm:
    """Admissible conversion rule: Gamma |- t : A   Gamma |- A == B
                                    -------------------------------
                                          Gamma |- t : B"""
    asl = term_union(t_th._asl, eq._asl)
    if type_eq(t_th._ty, eq._lhs):
        return typing_thm(asl, t_th._tm, eq._rhs)
    if type_eq(t_th._ty, eq._rhs):
        return typing_thm(asl, t_th._tm, eq._lhs)
    raise HolError(
        f"CONV: term type {_pp_ty(t_th._ty)} matches neither side of "
        f"{_pp_ty(eq._lhs)} == {_pp_ty(eq._rhs)}"
    )


def _bridge_matches(eq: type_eq_thm, A: hol_type, B: hol_type) -> bool:
    return (type_eq(eq._lhs, A) and type_eq(eq._rhs, B)) or (
        type_eq(eq._lhs, B) and type_eq(eq._rhs, A)
    )


# ---------------------------------------------------------------------------
# Type-equality rules: TY_REFL, TY_SYM, TY_TRANS, TY_CONG_BASE, TY_CONG_PI
# ---------------------------------------------------------------------------


def TY_REFL(ty: hol_type) -> type_eq_thm:
    return type_eq_thm([], ty, ty)


def TY_SYM(e: type_eq_thm) -> type_eq_thm:
    return type_eq_thm(e._asl, e._rhs, e._lhs)


def TY_TRANS(e1: type_eq_thm, e2: type_eq_thm) -> type_eq_thm:
    if not type_eq(e1._rhs, e2._lhs):
        raise HolError("TY_TRANS: middle types do not match")
    return type_eq_thm(term_union(e1._asl, e2._asl), e1._lhs, e2._rhs)


def TY_CONG_BASE(tyop: str, type_args: list, term_eqs: list) -> type_eq_thm:
    """congBase':  a : Pi(x1:A1)...(xn:An). tp in T
                    Gamma |- s_i = t_i  (regular term-equality thms)
                  -------------------------------------------------
                  Gamma |- a s1...sn == a t1...tn

    Each term_eqs[i] must be a thm whose conclusion is an equation."""
    try:
        arity, params = get_type_kind(tyop)
    except KeyError:
        raise HolError(f"TY_CONG_BASE: unknown type {tyop}")
    if arity != len(type_args):
        raise HolError("TY_CONG_BASE: wrong type-arg count")
    if len(params) != len(term_eqs):
        raise HolError("TY_CONG_BASE: wrong term-arg count")
    asl: list = []
    lhss: list = []
    rhss: list = []
    for eq in term_eqs:
        if not isinstance(eq, thm) or not _is_eq(eq._concl):
            raise HolError("TY_CONG_BASE: each argument must be an equation thm")
        lhss.append(_lhs(eq._concl))
        rhss.append(_rhs(eq._concl))
        asl = term_union(asl, eq._asl)
    return type_eq_thm(
        asl,
        Tyapp(tyop, tuple(type_args), tuple(lhss)),
        Tyapp(tyop, tuple(type_args), tuple(rhss)),
    )


def TY_CONG_PI(v: Var, dom_eq: type_eq_thm, cod_eq: type_eq_thm) -> type_eq_thm:
    """congPi:  Gamma |- A == A'   Gamma, x:A |- B == B'
               --------------------------------------------
               Gamma |- Pi(x:A). B == Pi(x:A'). B'
    v carries the binder name and its type; v.ty must be dom_eq._lhs."""
    if not type_eq(v.ty, dom_eq._lhs):
        raise HolError("TY_CONG_PI: binder type does not match domain LHS")
    asl = term_union(dom_eq._asl, cod_eq._asl)
    return type_eq_thm(
        asl,
        Pi(v, cod_eq._lhs),
        Pi(Var(v.name, dom_eq._rhs), cod_eq._rhs),
    )


# ---------------------------------------------------------------------------
# Validity rules: REFL, ASSUME, BETA, TRANS, MK_COMB, ABS, EQ_MP,
# DEDUCT_ANTISYM_RULE, INST, INST_TYPE
# ---------------------------------------------------------------------------


def REFL(t_th: typing_thm) -> thm:
    return thm(t_th._asl, safe_mk_eq(t_th._tm, t_th._tm))


def ASSUME(F_th: typing_thm) -> thm:
    if not type_eq(F_th._ty, bool_ty):
        raise HolError("ASSUME: not a proposition")
    return thm([F_th._tm, *F_th._asl], F_th._tm)


def BETA(redex_th: typing_thm) -> thm:
    tm = redex_th._tm
    if not (
        isinstance(tm, Comb)
        and isinstance(tm.fun, Abs)
        and tm.arg == tm.fun.bvar
    ):
        raise HolError("BETA: not a trivial beta-redex")
    return thm(redex_th._asl, safe_mk_eq(tm, tm.fun.body))


def ETA(t_th: typing_thm) -> thm:
    """etaPi:  Gamma |- t : Pi(x:A). B
              -----------------------------
              Gamma |- t = (\\x:A. t x)

    The bound variable name is chosen fresh to avoid capture in t."""
    f_ty = t_th._ty
    if not isinstance(f_ty, Pi):
        raise HolError(f"ETA: term type is not a Pi (got {_pp_ty(f_ty)})")
    fresh_v = variant(frees(t_th._tm), f_ty.bvar)
    eta_form = Abs(fresh_v, Comb(t_th._tm, fresh_v))
    return thm(t_th._asl, safe_mk_eq(t_th._tm, eta_form))


def EQ_TY_CONV(eq_th: thm, ty_eq: type_eq_thm) -> thm:
    """Validity-level conversion:
                Gamma |- s =A t    Delta |- A == B
                ----------------------------------
                       Gamma + Delta |- s =B t

    Re-tags an equation's = constant at a propositionally-equal type.
    The bridge may run in either direction (A == B or B == A). The
    bridge's hypotheses are absorbed into the result theorem.

    This plugs the gap where DHOL admits the conversion rule
        Gamma |- F : bool    Gamma |- F == F'   (with F, F' = s =T t)
        Gamma |- F     ===>  Gamma |- F'
    but the kernel had no way to apply it at the validity layer."""
    c = eq_th._concl
    if not _is_eq(c):
        raise HolError("EQ_TY_CONV: conclusion is not an equation")
    eq_const = c.fun.fun
    # The = constant's type is Pi(_:A, Pi(_:A, bool)); read A off the outer Pi.
    A = eq_const.ty.bvar.ty
    if type_eq(ty_eq._lhs, A):
        B = ty_eq._rhs
    elif type_eq(ty_eq._rhs, A):
        B = ty_eq._lhs
    else:
        raise HolError(
            f"EQ_TY_CONV: bridge {_pp_ty(ty_eq._lhs)} == {_pp_ty(ty_eq._rhs)} "
            f"does not connect equation type {_pp_ty(A)}"
        )
    new_eq_const = Const("=", Pi(Var("_", B), Pi(Var("_", B), bool_ty)))
    s, t = _lhs(c), _rhs(c)
    new_concl = Comb(Comb(new_eq_const, s), t)
    return thm(term_union(eq_th._asl, ty_eq._asl), new_concl)


def TRANS(th1: thm, th2: thm) -> thm:
    c1, c2 = th1._concl, th2._concl
    if _is_eq(c1) and _is_eq(c2) and alphaorder(_rhs(c1), _lhs(c2)) == 0:
        return thm(term_union(th1._asl, th2._asl), Comb(c1.fun, _rhs(c2)))
    raise HolError("TRANS")


def MK_COMB(th1: thm, th2: thm, eq: type_eq_thm | None = None) -> thm:
    c1, c2 = th1._concl, th2._concl
    if not (_is_eq(c1) and _is_eq(c2)):
        raise HolError("MK_COMB: not both equations")
    l1, r1 = _lhs(c1), _rhs(c1)
    l2, r2 = _lhs(c2), _rhs(c2)
    f_ty = type_of(l1)
    if not isinstance(f_ty, Pi):
        raise HolError("MK_COMB: head type is not Pi")
    expected, got = f_ty.bvar.ty, type_of(l2)
    asl = term_union(th1._asl, th2._asl)
    if not type_eq(expected, got):
        if eq is None or not _bridge_matches(eq, expected, got):
            raise HolError("MK_COMB: domain types do not agree")
        asl = term_union(asl, eq._asl)
    return thm(asl, safe_mk_eq(Comb(l1, l2), Comb(r1, r2)))


def ABS(v: Var, th: thm) -> thm:
    c = th._concl
    if not _is_eq(c):
        raise HolError("ABS: conclusion not an equation")
    if any(vfree_in(v, a) for a in th._asl):
        raise HolError("ABS: bound variable occurs free in hypotheses")
    l, r = _lhs(c), _rhs(c)
    return thm(th._asl, safe_mk_eq(Abs(v, l), Abs(v, r)))


def EQ_MP(th1: thm, th2: thm) -> thm:
    c = th1._concl
    if _is_eq(c) and alphaorder(_lhs(c), th2._concl) == 0:
        return thm(term_union(th1._asl, th2._asl), _rhs(c))
    raise HolError("EQ_MP")


def DEDUCT_ANTISYM_RULE(th1: thm, th2: thm) -> thm:
    asl1 = term_remove(th2._concl, th1._asl)
    asl2 = term_remove(th1._concl, th2._asl)
    return thm(term_union(asl1, asl2), safe_mk_eq(th1._concl, th2._concl))


def INST(theta: list, th: thm) -> thm:
    """theta is a list of (typing_thm, Var). Each replacement carries its
    own typing certificate, whose assumptions are absorbed into the
    result.

    Sequential semantics: the i-th replacement's type must match the i-th
    variable's declared type with the *earlier* replacements already
    applied (paper's substitution lemma, linearly-ordered context). So
    for [(t1, x1), (t2, x2)] with x2:A2 depending on x1, t2 must have
    type A2[x1/t1].

    Propositional bridging is handled by CONV: pre-coerce a replacement
    to the (sequentially-)expected type before passing it in."""
    if not theta:
        return th
    tm_theta: list = []
    asl_extra: list = []
    for i, (t_th, x) in enumerate(theta):
        if not isinstance(t_th, typing_thm):
            raise HolError(
                "INST: replacement must be a typing_thm "
                "(wrap with VAR/CONST/APP/... or CONV)"
            )
        if not isinstance(x, Var):
            raise HolError("INST: target must be a Var")
        expected_ty = subst_in_type(tm_theta, x.ty)
        if not type_eq(t_th._ty, expected_ty):
            raise HolError(
                f"INST: type mismatch at position {i} "
                f"(replacement {_pp_ty(t_th._ty)} vs expected "
                f"{_pp_ty(expected_ty)} after earlier substitutions); "
                f"pre-apply CONV"
            )
        tm_theta.append((t_th._tm, x))
        asl_extra = term_union(asl_extra, t_th._asl)
    f = lambda tm: _vsubst(tm_theta, tm)
    return thm(
        term_union(term_image(f, th._asl), asl_extra),
        f(th._concl),
    )


def INST_TYPE(theta: list, th: thm) -> thm:
    """theta is a list of (replacement_type, Tyvar). Propagates the
    substitution into every type annotation, using Clash-driven alpha-
    rename when type instantiation would cause a bound variable to
    collide with a free one in the body."""
    if not theta:
        return th
    f = lambda tm: _inst_in_term([], theta, tm)
    return thm(term_image(f, th._asl), f(th._concl))


# ---------------------------------------------------------------------------
# Axioms and definitions
# ---------------------------------------------------------------------------

the_axioms: list = []


def axioms() -> list:
    return list(the_axioms)


def new_axiom(F_th: typing_thm) -> thm:
    if not type_eq(F_th._ty, bool_ty):
        raise HolError("new_axiom: not a proposition")
    if F_th._asl:
        raise HolError("new_axiom: axiom must be unconditional")
    th = thm([], F_th._tm)
    the_axioms.append(th)
    return th


the_definitions: list = []


def definitions() -> list:
    return list(the_definitions)


def new_basic_definition(lhs: Var, rhs_th: typing_thm) -> thm:
    if rhs_th._asl:
        raise HolError("new_basic_definition: rhs must be unconditional")
    if not freesin([], rhs_th._tm):
        fv = [v.name for v in frees(rhs_th._tm)]
        raise HolError("new_basic_definition: rhs not closed: " + ", ".join(fv))
    if not type_eq(lhs.ty, rhs_th._ty):
        raise HolError("new_basic_definition: declared type does not match rhs")
    allowed = tyvars(lhs.ty)
    if not all(tv in allowed for tv in type_vars_in_term(rhs_th._tm)):
        raise HolError(
            "new_basic_definition: type variables not reflected in constant"
        )
    new_constant(lhs.name, lhs.ty)
    c = Const(lhs.name, lhs.ty)
    dth = thm([], safe_mk_eq(c, rhs_th._tm))
    the_definitions.append(dth)
    return dth


# ---------------------------------------------------------------------------
# Demo: vectors indexed by nat, with a propositional type bridge
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    # nat as a base type
    new_type("nat", type_arity=0, term_params=())
    nat_ty = Tyapp("nat", (), ())
    new_constant("0", nat_ty)
    new_constant("S", mk_arrow(nat_ty, nat_ty))
    new_constant("add", mk_arrow(nat_ty, mk_arrow(nat_ty, nat_ty)))

    zero_th = CONST("0")
    succ_th = CONST("S")
    add_th = CONST("add")
    one_th = APP(succ_th, zero_th)
    two_th = APP(succ_th, one_th)
    print("0   ::", _pp_ty(zero_th._ty))
    print("S 0 ::", _pp_ty(one_th._ty))
    print()

    # vec : nat -> tp
    new_type("vec", type_arity=0, term_params=(nat_ty,))

    def vec(n_th):
        return mk_type("vec", [], [n_th])

    # nil : vec 0
    new_constant("nil", vec(zero_th))
    nil_th = CONST("nil")
    print("nil ::", _pp_ty(nil_th._ty))

    # cons : Pi(n:nat). nat -> vec n -> vec (S n)
    n_var = Var("n", nat_ty)
    n_th = VAR(n_var)
    vec_n = vec(n_th)
    vec_Sn = vec(APP(succ_th, n_th))
    cons_ty = Pi(n_var, mk_arrow(nat_ty, mk_arrow(vec_n, vec_Sn)))
    new_constant("cons", cons_ty)
    cons_th = CONST("cons")

    # Build cons 0 0 nil  ::  vec (S 0)
    v1_th = APP(APP(APP(cons_th, zero_th), zero_th), nil_th)
    print("cons 0 0 nil           ::", _pp_ty(v1_th._ty))

    # Build cons 1 0 (cons 0 0 nil)  ::  vec (S (S 0))
    v2_th = APP(APP(APP(cons_th, one_th), zero_th), v1_th)
    print("cons 1 0 (cons 0 0 nil)::", _pp_ty(v2_th._ty))

    # Definitional mismatch: cons 1 0 nil rejected (expects vec 1, got vec 0)
    try:
        APP(APP(APP(cons_th, one_th), zero_th), nil_th)
    except HolError as e:
        print("\nexpected failure:", str(e).splitlines()[0])

    # ----------------------------------------------------------------
    # Propositional type bridge.
    #
    # Axiom: forall n. add 0 n = n  -- we encode just the free-variable form
    # |- add 0 n = n   (n a free variable of type nat).
    # Then specialize to n := 0, lift to vec(add 0 0) == vec 0 via TY_CONG_BASE,
    # and use the bridge to apply a function expecting vec 0 to a value
    # whose type is vec(add 0 0).
    # ----------------------------------------------------------------

    print()
    add_0_n = APP(APP(add_th, zero_th), VAR(n_var))
    eq_form = APP(APP(CONST("=", [(nat_ty, aty)]), add_0_n), VAR(n_var))
    print("axiom term ::", _pp_tm(eq_form._tm), ":", _pp_ty(eq_form._ty))
    add_zero = new_axiom(eq_form)  # |- add 0 n = n
    print("axiom      ::", add_zero)

    # Specialize n := 0
    add_0_0_eq_0 = INST([(zero_th, n_var)], add_zero)
    print("specialised::", add_0_0_eq_0)

    # Lift to type equality vec(add 0 0) == vec 0
    vec_bridge = TY_CONG_BASE("vec", [], [add_0_0_eq_0])
    print("type bridge::", vec_bridge)

    # Build a value of type vec(add 0 0) by CONV-ing nil : vec 0
    nil_at_add = CONV(nil_th, TY_SYM(vec_bridge))
    print("nil viewed as vec(add 0 0) ::", _pp_ty(nil_at_add._ty))

    # Define a consumer  g : vec 0 -> nat
    g_v = Var("v", vec(zero_th))
    g_th = LAMBDA(g_v, zero_th)  # \v:vec(0). 0
    print("g          ::", _pp_ty(g_th._ty))

    # Now apply g to nil_at_add (whose type is vec(add 0 0), not vec 0).
    # Without a bridge, APP rejects:
    try:
        APP(g_th, nil_at_add)
    except HolError as e:
        print("without bridge:", str(e).splitlines()[0])

    # With the bridge, APP succeeds and the resulting typing absorbs the
    # bridge's hypotheses (here empty, since the axiom was unconditional).
    g_nil = APP(g_th, nil_at_add, eq=vec_bridge)
    print("with bridge: g (nil :vec(add 0 0)) ::", _pp_ty(g_nil._ty))
    print("             asl =", g_nil._asl)

    # Wrap it into a regular theorem.
    g_nil_refl = REFL(g_nil)
    print("REFL(g nil) ::", g_nil_refl)

    # ----------------------------------------------------------------
    # INST also propagates the substitution into type annotations.
    # Build |- cons n x v = cons n x v with v : vec n free, then INST
    # n := zero. The free v should reappear as v : vec 0 in the result.
    # ----------------------------------------------------------------
    print()
    x_var = Var("x", nat_ty)
    v_var = Var("v", vec(n_th))  # v : vec n
    cons_nxv_th = APP(APP(APP(cons_th, n_th), VAR(x_var)), VAR(v_var))
    print("cons n x v ::", _pp_ty(cons_nxv_th._ty))
    refl_cons = REFL(cons_nxv_th)
    print("REFL       ::", refl_cons)
    refl_cons_at_0 = INST([(zero_th, n_var)], refl_cons)
    print("INST n:=0  ::", refl_cons_at_0)
    # Inspect the Var occurrences in the new conclusion to confirm v's
    # type annotation was rewritten from vec(n) to vec(0).
    for free in frees(refl_cons_at_0._concl):
        print(f"  free var {free.name} :: {_pp_ty(free.ty)}")

    # ----------------------------------------------------------------
    # Sequential semantics: INST [(zero, n), (v_th, v)] where v_th has
    # type vec(0) — matching v's declared type vec(n) only AFTER the
    # earlier substitution n := 0 has been applied.
    # ----------------------------------------------------------------
    print()
    nil_th_again = CONST("nil")  # vec(0)
    seq_inst = INST([(zero_th, n_var), (nil_th_again, v_var)], refl_cons)
    print("seq INST [n:=0, v:=nil] ::", seq_inst)

    # ----------------------------------------------------------------
    # Propositional bridging via CONV-then-INST. We have nil : vec(0)
    # and want to substitute it for v : vec(n) with n eventually becoming
    # `add 0 0`. The replacement's type after the n:=add 0 0 step would
    # be vec(add 0 0), so we CONV nil from vec(0) to vec(add 0 0) using
    # the bridge derived earlier, then INST sequentially.
    # ----------------------------------------------------------------
    print()
    add00_th = APP(APP(add_th, zero_th), zero_th)        # add 0 0 : nat
    nil_at_add00 = CONV(nil_th, vec_bridge)              # nil : vec(add 0 0)
    print("nil : vec(0)  ==CONV==>  vec(add 0 0)  ::", _pp_ty(nil_at_add00._ty))
    bridged_inst = INST(
        [(add00_th, n_var), (nil_at_add00, v_var)],
        refl_cons,
    )
    print("INST [n:=add 0 0, v:=nil (coerced)] ::", bridged_inst)
    for free in frees(bridged_inst._concl):
        print(f"  free var {free.name} :: {_pp_ty(free.ty)}")

    # ----------------------------------------------------------------
    # ETA: eta-expand a Pi-typed term.
    # ----------------------------------------------------------------
    print()
    succ_eta = ETA(succ_th)
    print("ETA(S) ::", succ_eta)

    # Eta-expanding cons applied to 0 (type nat -> vec 0 -> vec (S 0)).
    cons0_eta = ETA(APP(cons_th, zero_th))
    print("ETA(cons 0) ::", cons0_eta)

    # Eta-expanding cons itself (dependent Pi: Pi(n:nat). ...).
    cons_eta = ETA(cons_th)
    print("ETA(cons)   ::", cons_eta)

    # ----------------------------------------------------------------
    # EQ_TY_CONV: re-tag an equation at a propositionally-equal type.
    # ----------------------------------------------------------------
    print()
    def _eq_tag(th):
        return _pp_ty(th._concl.fun.fun.ty.bvar.ty)

    nil_refl = REFL(nil_th)
    print(f"REFL(nil)                :: {nil_refl}  [= tagged at {_eq_tag(nil_refl)}]")
    # nil_refl's = constant is tagged at vec(0). Re-tag via the bridge
    # vec(add 0 0) == vec(0) (which here happens to have empty asl).
    nil_refl_at_add = EQ_TY_CONV(nil_refl, vec_bridge)
    print(f"EQ_TY_CONV via vec_bridge:: {nil_refl_at_add}  [= tagged at {_eq_tag(nil_refl_at_add)}]")

    # Demonstrate hypothesis propagation: ASSUME the same equation
    # add 0 0 = 0, lift it, and use the resulting bridge in EQ_TY_CONV;
    # the assumption should appear in the result's asl.
    print()
    assumed_eq = ASSUME(eq_form)  # not quite -- eq_form is the universally
                                  # quantified form. Let's specialise:
    # Build an assumption form with n bound to 0:
    n0_eq = APP(APP(CONST("=", [(nat_ty, aty)]),
                    APP(APP(add_th, zero_th), zero_th)),
                zero_th)
    print("assumption term ::", _pp_tm(n0_eq._tm))
    assumed_n0 = ASSUME(n0_eq)
    print("ASSUME           ::", assumed_n0)
    vec_bridge_hyp = TY_CONG_BASE("vec", [], [assumed_n0])
    print("derived bridge   ::", vec_bridge_hyp)
    nil_refl_hyp = EQ_TY_CONV(nil_refl, vec_bridge_hyp)
    print(f"EQ_TY_CONV w/ hyp:: {nil_refl_hyp}  [= tagged at {_eq_tag(nil_refl_hyp)}]")
