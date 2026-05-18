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
# Both MK_COMB and ABS accept an optional type-equality bridge for the
# dependent case: MK_COMB's cod_eq witnesses B[l2/x] == B[r2/x] when the
# substituted codomains differ; ABS's ty_eq witnesses A == A' so the
# binder type may differ between the two sides of the abstraction.
#
# Deliberate spike-level simplifications:
#   - INST / INST_TYPE require definitionally-matching types; substitutions
#     that need propositional bridges must be built via APP + CONV.
#   - new_basic_type_definition is omitted.
#   - eta is not part of alpha at Pi.

from __future__ import annotations
import sys
from dataclasses import dataclass
from typing import Callable, NamedTuple

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
    precondition: "term | None" = None  # None == true; otherwise a bool term


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
    term_args: tuple = ()  # chosen σ-values for Var entries in the declared Φ

    def __post_init__(self):
        if not isinstance(self.term_args, tuple):
            object.__setattr__(self, "term_args", tuple(self.term_args))


@dataclass(frozen=True, slots=True)
class Comb:
    fun: "term"
    arg: "term"


@dataclass(frozen=True, slots=True)
class Abs:
    bvar: Var
    body: "term"
    precondition: "term | None" = None  # None == true; otherwise a bool term


term = Var | Const | Comb | Abs


@dataclass(frozen=True, slots=True)
class Assume:
    """Assumption-entry binder in a type-symbol declaration context
    (paper's `▷F` in a `Φ`-context). Carries a boolean term schema
    that the user must discharge at every mk_type / TY_CONG_BASE call
    site. Unlike Tyvar / Var entries, it does not bind a name in scope
    for later entries -- it is a pure obligation."""
    formula: term


# A Φ-slot is a binder at one of the three DHOL judgment levels:
#
#   Tyvar(α)   -- binds at tp        (`Γ ⊢ α : tp`)
#   Var(x, A)  -- binds at term      (`Γ ⊢ x : A`)
#   Assume(F)  -- binds at validity  (`Γ ⊢ F`)
#
# The PhiSubst evidence for each slot is the corresponding J-witness:
# hol_type for Tyvar (carrying the tp-level fact implicitly), typing_thm
# for Var (the term-level witness), and thm for Assume (the validity
# witness). This pointwise mapping is what makes `_apply_phi_subst`
# and `_apply_phi_dual` J-agnostic walkers.
Slot = Tyvar | Var | Assume


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


class StagedThm:
    """(Φ) ▷ F  -- a thm parameterized over a Φ-telescope.

    Carries the prop-level J-tag explicitly: a `PropBody(F)` body
    paired with a Φ-telescope of Tyvar | Var | Assume binders. The
    asl-as-Assume-formulas view is reconstructed by `_phi_asl(phi)`
    when the projected thm is needed (e.g. for printing).

    Use `interpret(staged, σ)` to instantiate to a concrete thm; σ
    matches Φ pointwise (hol_type for Tyvar, typing_thm for Var, thm
    for Assume), validated by the same `_apply_phi_subst` walker used
    by `mk_type` and `CONST`."""

    __slots__ = ("_phi", "_body")

    def __init__(self, phi, body):
        if not isinstance(body, PropBody):
            raise HolError(
                "StagedThm: body must be a PropBody (got "
                f"{type(body).__name__})"
            )
        self._phi = tuple(phi)
        self._body = body

    @property
    def thm(self) -> "thm":
        """Projected validity view: `[Assume-formulas-of-Φ] ⊢ F`."""
        return thm(_phi_asl(self._phi), self._body.formula)

    def __repr__(self):
        projected = self.thm
        if not self._phi:
            return repr(projected)
        return f"({_pp_phi(self._phi)}) ▷ {projected!r}"


def _phi_asl(phi) -> list:
    """The Assume-formulas of Φ in declaration order -- the asl carried
    by the projected `thm` view of a `StagedThm`."""
    asl: list = []
    for b in phi:
        if isinstance(b, Assume):
            asl = term_union(asl, [b.formula])
    return asl


def _pp_phi(phi) -> str:
    parts = []
    for e in phi:
        if isinstance(e, Tyvar):
            parts.append(e.name)
        elif isinstance(e, Var):
            parts.append(f"{e.name}:{_pp_ty(e.ty)}")
        elif isinstance(e, Assume):
            parts.append(f"▷{_pp_tm(e.formula)}")
        else:
            parts.append(repr(e))
    return ", ".join(parts)


# ---------------------------------------------------------------------------
# Declarations and the Judgment ADT
#
# DHOL has three judgment levels, each with its own body shape:
#
#   tp        Γ; Φ ⊢ name(Φ) : tp     -- TpBody()         (no body data)
#   term      Γ; Φ ⊢ name(Φ) : ty     -- TmBody(ty)       (a hol_type)
#   prop      Γ; Φ ▷ F                -- PropBody(F)      (a term : bool)
#
# `Judgment = TpBody | TmBody | PropBody` reifies the body tag of a
# staged declaration. The two named-declaration species (tp and term)
# live in the unified `the_decls` registry; the prop species is
# carried by `StagedThm` (axioms are anonymous and live in
# `the_axioms`, but their body shape is exactly the same Judgment
# discriminator -- this is the J-level symmetry from the audit doc).
#
# A type symbol's body is just `TpBody()` -- inhabitation is the
# responsibility of the associated witness Decl, a separate TmBody
# entry registered atomically with the type by `new_type`.
#
# Each Decl's Φ is an ordered telescope of Slot binders (Tyvar / Var /
# Assume); later entries may reference earlier ones. The flat-arity
# case is recovered by an empty Φ; rank-1 polymorphism alone by a Φ
# of Tyvars; the dependent-parameter case by a Φ of Vars.
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class TpBody:
    """tp-level body: `name(Φ) : tp`. Carries no body data of its own;
    inhabitation is the responsibility of the associated witness Decl,
    registered atomically by `new_type`."""


@dataclass(frozen=True, slots=True)
class TmBody:
    """term-level body: `name(Φ) : ty`."""
    ty: hol_type


@dataclass(frozen=True, slots=True)
class PropBody:
    """prop-level body: validity body `F : bool`. The Φ-Assume binders
    carry F's hypotheses implicitly -- the projection-as-thm view of
    a staged prop reconstructs them via `_phi_asl(phi)`."""
    formula: term


Judgment = TpBody | TmBody | PropBody


@dataclass(frozen=True, slots=True)
class Decl:
    """A staged declaration: `name(Φ)` with a body discriminator.

    Φ is a tuple of Slot binders (Tyvar | Var | Assume), interpreted
    sequentially; body discriminates the judgment level:
      * TpBody    -- name(Φ) : tp
      * TmBody    -- name(Φ) : ty
      * PropBody  -- (Φ) ▷ F  (used internally by `StagedThm`; not
                     registered by name in `the_decls`)
    """
    name: str
    phi: tuple
    body: Judgment


# Insertion order = declaration order; newer entries shadow older ones
# in iteration, mirroring HOL Light's "latest first" discipline (and
# the previous insert(0, ...) lists). Lookup is direct via dict[name].
the_decls: dict = {"bool": Decl("bool", (), TpBody())}


def types() -> list:
    """Public view: `(name, phi)` tuples for type symbols, newest first."""
    return [
        (d.name, d.phi)
        for d in reversed(the_decls.values())
        if isinstance(d.body, TpBody)
    ]


def get_type_kind(s: str) -> tuple:
    """Return the declared Φ-telescope of a type symbol."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, TpBody):
        raise KeyError(s)
    return d.phi


def _head_tyop(ty: hol_type) -> str | None:
    """Type-constant name at the head of ty, after stripping leading
    Pi binders. Used by new_type to validate that an inhabitation
    witness's type targets the right family."""
    while isinstance(ty, Pi):
        ty = ty.body
    if isinstance(ty, Tyapp):
        return ty.tyop
    return None


def new_type(
    name: str,
    phi: tuple = (),
    witness: tuple | None = None,
) -> None:
    """Declares a new type constant `name(Φ) : tp`, atomically with
    an inhabitation witness.

    `phi` is a Φ-telescope of `Tyvar | Var | Assume` binders. Same
    vocabulary as on term constants -- later entries may reference
    earlier ones (rank-1 polymorphism interleaved with dependent term
    params and assumption obligations).

    The `witness` argument is a (const_name, const_ty) pair. const_ty
    (after stripping leading Pi binders) must have `name` as its head;
    declaring const_name at const_ty establishes the new type family as
    inhabited per the paper's modified non-emptiness rule (§3). Both
    the type and the witness constant land in the kernel in a single
    operation -- there is no observable intermediate state where the
    type exists without inhabitation.

    `bool` is the sole exception: it's the kernel's primitive type and
    requires no user call to new_type.
    """
    if witness is None:
        raise HolError(
            f"new_type: {name} requires an inhabitation witness. "
            f"Pass witness=(const_name, const_ty) where const_ty's head "
            f"(after Pi-stripping) is {name}."
        )
    if name in the_decls:
        raise HolError(f"new_type: type {name} has already been declared")
    _check_phi(phi, f"new_type({name})")
    witness_name, witness_ty = witness
    if witness_name in the_decls:
        raise HolError(
            f"new_type: witness constant {witness_name} already declared"
        )
    head = _head_tyop(witness_ty)
    if head != name:
        raise HolError(
            f"new_type: witness type must have {name} as its head "
            f"(got {head})"
        )
    # All checks passed -- commit atomically.
    the_decls[name] = Decl(name, tuple(phi), TpBody())
    witness_phi = tuple(Tyvar(tv.name) for tv in tyvars(witness_ty))
    the_decls[witness_name] = Decl(witness_name, witness_phi, TmBody(witness_ty))


bool_ty: hol_type = Tyapp("bool", (), ())
aty: hol_type = Tyvar("A")


def _seed_constant(name: str, phi: tuple, ty: hol_type) -> None:
    the_decls[name] = Decl(name, phi, TmBody(ty))


# Seed the registry with the two kernel-primitive term constants:
#   = : (A:tp) → Pi(_:A). Pi(_:A). bool
#   ==> : Pi(_:bool). Pi(_:bool). bool
_seed_constant(
    "=",
    (Tyvar("A"),),
    Pi(Var("_", aty), Pi(Var("_", aty), bool_ty)),
)
_seed_constant(
    "==>",
    (),
    Pi(Var("_", bool_ty), Pi(Var("_", bool_ty), bool_ty)),
)


def constants() -> list:
    """Public view: `(name, phi, ty)` tuples for term constants,
    newest first."""
    return [
        (d.name, d.phi, d.body.ty)
        for d in reversed(the_decls.values())
        if isinstance(d.body, TmBody)
    ]


def get_const_phi(s: str) -> tuple:
    """Return the declared Φ-telescope of a term constant."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, TmBody):
        raise KeyError(s)
    return d.phi


def get_const_type(s: str) -> hol_type:
    """Return the constant's declared body type (well-formed under Φ)."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, TmBody):
        raise KeyError(s)
    return d.body.ty


def new_constant(name: str, ty: hol_type,
                 phi: tuple | None = None) -> None:
    """Declare a staged constant `name(Φ) : ty`.

    Φ is a telescope of Slot binders that may interleave:
      * Tyvar(α)   -- rank-1 polymorphism
      * Var(x, A)  -- dependent term parameter
      * Assume(F)  -- declaration-time precondition

    `ty` may reference any Tyvar/Var bound in Φ; Assume entries are pure
    obligations that don't bind a name in scope.

    When `phi` is None, Φ defaults to the free Tyvars of `ty` (in
    first-appearance order) as Tyvar entries. Pass `phi` explicitly to
    add Var/Assume entries or to control the order of the Tyvar slots."""
    if name in the_decls:
        raise HolError(
            f"new_constant: name {name} has already been declared"
        )
    if phi is None:
        phi = tuple(Tyvar(tv.name) for tv in tyvars(ty))
    else:
        _check_phi(phi, f"new_constant({name})")
        phi = tuple(phi)
    the_decls[name] = Decl(name, phi, TmBody(ty))


def mk_arrow(a: hol_type, b: hol_type) -> hol_type:
    return Pi(Var("_", a), b)


def _check_assume_proof(arg, formula: term, theta_ty: list,
                        theta_tm: list, ctx: str) -> term:
    """Validate that `arg` is a `thm` whose conclusion alpha-matches
    `formula` after applying the term substitution `theta_tm` and the
    type substitution `theta_ty`. Returns the substituted `formula`
    (`needed`); the caller decides what to do with `arg._asl`."""
    if not isinstance(arg, thm):
        raise HolError(f"{ctx}: argument for Assume binder must be a thm")
    needed = _inst_in_term([], theta_ty, _vsubst(theta_tm, formula))
    if not _tm_alpha([], arg._concl, needed):
        raise HolError(
            f"{ctx}: Assume proof concludes {_pp_tm(arg._concl)} "
            f"but required is {_pp_tm(needed)}"
        )
    return needed


# ---------------------------------------------------------------------------
# Φ-telescopes and Φ-substitutions
#
# A Φ-telescope is an ordered tuple of binders:
#
#   Phi      = tuple[Tyvar | Var | Assume, ...]
#
#   * Tyvar(α) binds a type variable α in scope for later entries.
#   * Var(x, A) binds a term variable x:A; A may reference earlier
#     Tyvar/Var binders.
#   * Assume(F) is a pure obligation (boolean term schema) that must be
#     discharged at every use site; F may reference earlier binders.
#
# A Φ-substitution σ provides one replacement per Φ entry, in order:
#
#   PhiSubst = tuple[hol_type | typing_thm | thm, ...]
#
#   * Tyvar entry  -> hol_type
#   * Var entry    -> typing_thm certifying the chosen term's type
#   * Assume entry -> thm discharging the obligation
#
# Both telescopes and substitutions are interpreted sequentially:
# each entry/replacement is checked under the substitution accumulated
# from earlier ones.  `_apply_phi_subst` is the shared validator that
# `mk_type`, the staged `CONST`, and (per-side) `TY_CONG_BASE` use to
# walk the two structures in parallel.
# ---------------------------------------------------------------------------


Phi = tuple                 # tuple[Tyvar | Var | Assume, ...]
PhiSubst = tuple            # tuple[hol_type | typing_thm | thm, ...]


def _check_phi(phi, ctx: str) -> None:
    """Light syntactic check: every entry is a Tyvar, Var, or Assume.
    Well-formedness of binder annotations under earlier entries is the
    caller's responsibility (honest-caller perimeter, mirroring how
    `new_type` accepts raw `Var(x, A)` without re-checking A)."""
    for entry in phi:
        if not isinstance(entry, (Tyvar, Var, Assume)):
            raise HolError(
                f"{ctx}: context entries must be Tyvar, Var, or Assume "
                f"(got {entry!r})"
            )


class PhiSubstResult(NamedTuple):
    """Output of `_apply_phi_subst`. Fields:
      theta_ty:  list of (chosen_hol_type, Tyvar) -- type substitution
      theta_tm:  list of (chosen_term, Var)        -- term substitution
      term_args: chosen terms for Var entries (declaration order)
      asl_extra: assumptions absorbed from Var-typings + Assume-proofs"""
    theta_ty: list
    theta_tm: list
    term_args: list
    asl_extra: list


def _apply_phi_subst(phi, sigma, ctx: str) -> PhiSubstResult:
    """Walk Φ and σ in parallel, validating each replacement against
    the corresponding binder species (under the running substitution
    from earlier entries).

    Per-slot work is dispatched through `_SLOT_DISPATCH` (defined
    below, with all the type-equality helpers in scope); each entry
    handles its J-level's evidence-shape check + theta/asl extraction.

    The caller decides how to consume the result (e.g. mk_type rejects
    any non-empty asl_extra; CONST absorbs it into the result's asl)."""
    if len(phi) != len(sigma):
        raise HolError(
            f"{ctx}: wrong number of arguments "
            f"(expected {len(phi)}, got {len(sigma)})"
        )
    out = PhiSubstResult(theta_ty=[], theta_tm=[], term_args=[], asl_extra=[])
    for binder, arg in zip(phi, sigma):
        handlers = _SLOT_DISPATCH.get(type(binder))
        if handlers is None:
            raise HolError(f"{ctx}: ill-formed context binder")
        handlers.subst(binder, arg, out, ctx)
    return out


def mk_type(tyop: str, args: list) -> hol_type:
    """Build a Tyapp from a type-constant name and an ordered list of
    arguments matching the declared Φ-telescope shape.

    Each `args[i]` corresponds to Φ entry `i`:
      * Tyvar binder  -> args[i] is a `hol_type`.
      * Var binder    -> args[i] is a `typing_thm` whose `_ty` matches
        the binder's declared type with all earlier args substituted in;
        must be unconditional (empty asl).
      * Assume binder -> args[i] is a `thm` discharging the formula
        substituted with all earlier args; must be unconditional.

    The result Tyapp stores Tyvar-slot choices in `type_args` (in
    declaration order) and Var-slot terms in `term_args` (in declaration
    order); the declared Φ recovers the original interleaving."""
    try:
        phi = get_type_kind(tyop)
    except KeyError:
        raise HolError(f"mk_type: type {tyop} has not been defined")
    result = _apply_phi_subst(phi, tuple(args), f"mk_type({tyop})")
    if result.asl_extra:
        raise HolError(
            "mk_type: Φ arguments must be unconditional (empty asl); "
            "mk_type returns a hol_type with no asl tracking"
        )
    type_args = tuple(t for t, _ in result.theta_ty)
    return Tyapp(tyop, type_args, tuple(result.term_args))


# ---------------------------------------------------------------------------
# Free variables, type variables
# ---------------------------------------------------------------------------


def _uniq_extend(seen: list, items) -> list:
    """Append each item to `seen` if not already present (by ==).
    Mutates `seen` in place and returns it for chaining."""
    for x in items:
        if x not in seen:
            seen.append(x)
    return seen


def frees(tm: term) -> list:
    if isinstance(tm, Var):
        return [tm]
    if isinstance(tm, Const):
        seen: list = []
        for a in tm.term_args:
            _uniq_extend(seen, frees(a))
        return seen
    if isinstance(tm, Abs):
        seen = [v for v in frees(tm.body) if v != tm.bvar]
        if tm.precondition is not None:
            _uniq_extend(seen, (v for v in frees(tm.precondition) if v != tm.bvar))
        return seen
    if isinstance(tm, Comb):
        return _uniq_extend(list(frees(tm.fun)), frees(tm.arg))
    raise HolError("frees: ill-formed term")


def freesin(acc: list, tm: term) -> bool:
    if isinstance(tm, Var):
        return tm in acc
    if isinstance(tm, Const):
        return all(freesin(acc, a) for a in tm.term_args)
    if isinstance(tm, Abs):
        body_ok = freesin([tm.bvar, *acc], tm.body)
        if not body_ok:
            return False
        if tm.precondition is None:
            return True
        return freesin([tm.bvar, *acc], tm.precondition)
    if isinstance(tm, Comb):
        return freesin(acc, tm.fun) and freesin(acc, tm.arg)
    raise HolError("freesin: ill-formed term")


def vfree_in(v: term, tm: term) -> bool:
    if isinstance(tm, Abs):
        if v == tm.bvar:
            return False
        if vfree_in(v, tm.body):
            return True
        return tm.precondition is not None and vfree_in(v, tm.precondition)
    if isinstance(tm, Comb):
        return vfree_in(v, tm.fun) or vfree_in(v, tm.arg)
    if isinstance(tm, Const):
        return any(vfree_in(v, a) for a in tm.term_args)
    return tm == v


def tyvars(ty: hol_type) -> list:
    if isinstance(ty, Tyvar):
        return [ty]
    if isinstance(ty, Tyapp):
        seen: list = []
        for a in ty.type_args:
            _uniq_extend(seen, tyvars(a))
        for a in ty.term_args:
            _uniq_extend(seen, type_vars_in_term(a))
        return seen
    if isinstance(ty, Pi):
        seen = _uniq_extend(list(tyvars(ty.bvar.ty)), tyvars(ty.body))
        if ty.precondition is not None:
            _uniq_extend(seen, type_vars_in_term(ty.precondition))
        return seen
    raise HolError("tyvars: ill-formed type")


def type_vars_in_term(tm: term) -> list:
    if isinstance(tm, Var):
        return tyvars(tm.ty)
    if isinstance(tm, Const):
        seen = list(tyvars(tm.ty))
        for a in tm.term_args:
            _uniq_extend(seen, type_vars_in_term(a))
        return seen
    if isinstance(tm, Comb):
        return _uniq_extend(
            list(type_vars_in_term(tm.fun)),
            type_vars_in_term(tm.arg),
        )
    if isinstance(tm, Abs):
        seen = _uniq_extend(
            list(tyvars(tm.bvar.ty)), type_vars_in_term(tm.body)
        )
        if tm.precondition is not None:
            _uniq_extend(seen, type_vars_in_term(tm.precondition))
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
        env2 = [(t1.bvar, t2.bvar), *env]
        if not _prec_eq(env2, t1.precondition, t2.precondition):
            return False
        return _ty_eq(env2, t1.body, t2.body)
    return False


def _prec_eq(env: list, p1, p2) -> bool:
    """Compare two preconditions for alpha-equivalence under `env`.
    None means `true`; two Nones are equal."""
    if p1 is None and p2 is None:
        return True
    if p1 is None or p2 is None:
        return False
    return _tm_alpha(env, p1, p2)


def _tm_alpha(env: list, a: term, b: term) -> bool:
    if isinstance(a, Var) and isinstance(b, Var):
        for x, y in env:
            if a == x:
                return b == y
            if b == y:
                return False
        return a == b
    if isinstance(a, Const) and isinstance(b, Const):
        if a.name != b.name or not _ty_eq(env, a.ty, b.ty):
            return False
        if len(a.term_args) != len(b.term_args):
            return False
        return all(
            _tm_alpha(env, x, y) for x, y in zip(a.term_args, b.term_args)
        )
    if isinstance(a, Comb) and isinstance(b, Comb):
        return _tm_alpha(env, a.fun, b.fun) and _tm_alpha(env, a.arg, b.arg)
    if isinstance(a, Abs) and isinstance(b, Abs):
        if not _ty_eq(env, a.bvar.ty, b.bvar.ty):
            return False
        env2 = [(a.bvar, b.bvar), *env]
        if not _prec_eq(env2, a.precondition, b.precondition):
            return False
        return _tm_alpha(env2, a.body, b.body)
    return False


# ---------------------------------------------------------------------------
# Term substitution into types (capture avoiding)
# ---------------------------------------------------------------------------


def _vsubst_opt(theta: list, prec):
    """`_vsubst` lifted over `None`-valued preconditions."""
    return None if prec is None else _vsubst(theta, prec)


def _inst_in_term_opt(env: list, tyin: list, prec):
    """`_inst_in_term` lifted over `None`-valued preconditions."""
    return None if prec is None else _inst_in_term(env, tyin, prec)


def _subst_binder(theta: list, bvar: Var, body, prec,
                  subst_body, free_in_body, ctor):
    """Capture-avoiding substitution under a binder, shared between
    `subst_in_type` (Pi) and `_vsubst` (Abs). `subst_body` recurses
    into `body` (`subst_in_type` / `_vsubst`); `free_in_body` is the
    free-occurrence predicate matching `body`'s shape (`_occurs_in_type`
    / `vfree_in`); `ctor` builds the result binder (`Pi` / `Abs`)."""
    theta2 = [(t, x) for t, x in theta if x != bvar]
    new_bvar_ty = subst_in_type(theta, bvar.ty)
    new_bvar = (
        bvar if new_bvar_ty is bvar.ty
        else Var(bvar.name, new_bvar_ty)
    )
    if not theta2:
        return ctor(new_bvar, body, prec)
    body_uses = lambda x: (
        free_in_body(x, body)
        or (prec is not None and vfree_in(x, prec))
    )
    if any(vfree_in(new_bvar, t) and body_uses(x) for t, x in theta2):
        avoid = [subst_body(theta2, body)]
        if prec is not None:
            avoid.append(_vsubst(theta2, prec))
        fresh = variant(avoid, new_bvar)
        rename = [(fresh, bvar), *theta2]
        return ctor(
            fresh, subst_body(rename, body), _vsubst_opt(rename, prec)
        )
    return ctor(
        new_bvar, subst_body(theta2, body), _vsubst_opt(theta2, prec)
    )


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
        return _subst_binder(
            theta, ty.bvar, ty.body, ty.precondition,
            subst_in_type, _occurs_in_type, Pi,
        )
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
        in_prec = ty.precondition is not None and vfree_in(v, ty.precondition)
        return (
            _occurs_in_type(v, ty.bvar.ty)
            or in_prec
            or _occurs_in_type(v, ty.body)
        )
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
            _inst_in_term_opt([], i, ty.precondition),
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
        new_args = tuple(_inst_in_term(env, tyin, a) for a in tm.term_args)
        if ty2 is tm.ty and all(
            n is o for n, o in zip(new_args, tm.term_args)
        ):
            return tm
        return Const(tm.name, ty2, new_args)
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
            prec2 = _inst_in_term_opt(env2, tyin, tm.precondition)
            if (
                bvar2 is tm.bvar
                and body2 is tm.body
                and prec2 is tm.precondition
            ):
                return tm
            return Abs(bvar2, body2, prec2)
        except Clash as ex:
            if ex.tm != bvar2:
                raise
            ifrees = [_inst_in_term([], tyin, v) for v in frees(tm.body)]
            bvar3 = variant(ifrees, bvar2)
            z = Var(bvar3.name, tm.bvar.ty)
            renamed = _vsubst([(z, tm.bvar)], tm.body)
            renamed_prec = _vsubst_opt([(z, tm.bvar)], tm.precondition)
            return _inst_in_term(
                env, tyin, Abs(z, renamed, renamed_prec)
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
        new_args = tuple(_vsubst(ilist, a) for a in tm.term_args)
        if new_ty is tm.ty and all(
            n is o for n, o in zip(new_args, tm.term_args)
        ):
            return tm
        return Const(tm.name, new_ty, new_args)
    if isinstance(tm, Comb):
        return Comb(_vsubst(ilist, tm.fun), _vsubst(ilist, tm.arg))
    if isinstance(tm, Abs):
        return _subst_binder(
            ilist, tm.bvar, tm.body, tm.precondition,
            _vsubst, vfree_in, Abs,
        )
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
        prec = (
            "" if ty.precondition is None
            else f"|{_pp_tm_raw(ty.precondition)}"
        )
        if not _occurs_in_type(ty.bvar, ty.body) and ty.precondition is None:
            return f"({_pp_ty_raw(ty.bvar.ty)} -> {_pp_ty_raw(ty.body)})"
        return (
            f"(Pi {ty.bvar.name}:{_pp_ty_raw(ty.bvar.ty)}{prec}. "
            f"{_pp_ty_raw(ty.body)})"
        )
    return repr(ty)


def _pp_tm(tm, _max=220):
    s = _pp_tm_raw(tm)
    return s if len(s) <= _max else s[: _max - 3] + "..."


def _pp_tm_raw(tm):
    if isinstance(tm, Var):
        return tm.name
    if isinstance(tm, Const):
        if tm.term_args:
            inner = ", ".join(_pp_tm_raw(a) for a in tm.term_args)
            return f"{tm.name}({inner})"
        return tm.name
    if isinstance(tm, Abs):
        prec = (
            "" if tm.precondition is None
            else f"|{_pp_tm_raw(tm.precondition)}"
        )
        return (
            f"(\\{tm.bvar.name}:{_pp_ty_raw(tm.bvar.ty)}{prec}. "
            f"{_pp_tm_raw(tm.body)})"
        )
    if isinstance(tm, Comb):
        return f"({_pp_tm_raw(tm.fun)} {_pp_tm_raw(tm.arg)})"
    return repr(tm)


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


def _eq_tag(c: term) -> hol_type:
    """Read an equation's type tag off its = constant. Use this instead
    of type_of(_lhs(c)) so that the type honoured matches what the rule
    that built the equation certified, not the term's intrinsic shape."""
    return c.fun.fun.ty.bvar.ty


def safe_mk_eq(ty: hol_type, lhs: term, r: term) -> term:
    """Build an equation tagged at the given type. The caller supplies
    the type (typically from a typing_thm._ty or from another equation's
    tag), so type_of is never consulted during equation construction."""
    eq_ty = Pi(Var("_", ty), Pi(Var("_", ty), bool_ty))
    return Comb(Comb(Const("=", eq_ty), lhs), r)


# ---------------------------------------------------------------------------
# Implication helpers (terms of shape Comb(Comb(Const("==>", _), F), G))
#
# Implication is primitive (not derived from equality, as in classic HOL)
# because typing the consequent in dependent setups requires assuming the
# antecedent -- see Rule D in Rabe's 2026 "Semantics for DHOL".
# ---------------------------------------------------------------------------


_imp_const_ty: hol_type = Pi(Var("_", bool_ty), Pi(Var("_", bool_ty), bool_ty))


def mk_imp(F: term, G: term) -> term:
    """Build the term `F ==> G` at type bool. Both arguments are assumed
    to be of type bool (the typing rule IMP_TYPE certifies this; this
    helper is purely a term constructor)."""
    return Comb(Comb(Const("==>", _imp_const_ty), F), G)


def _is_imp(c: term) -> bool:
    return (
        isinstance(c, Comb)
        and isinstance(c.fun, Comb)
        and isinstance(c.fun.fun, Const)
        and c.fun.fun.name == "==>"
    )


def _imp_ant(c: term) -> term:
    return c.fun.arg


def _imp_con(c: term) -> term:
    return c.arg


# ---------------------------------------------------------------------------
# Typing rules: VAR, CONST, APP, LAMBDA, CONV
#
# These are the *only* legal ways to build a typing_thm. Term construction
# outside of these rules has no certifying force.
# ---------------------------------------------------------------------------


def VAR(v: Var) -> typing_thm:
    """var-intro: Gamma, x:A |- x : A  (the x:A binding is intrinsic to v)."""
    return typing_thm([], v, v.ty)


def CONST(name: str, sigma: tuple = ()) -> typing_thm:
    """const-intro (staged):
            c(Φ) : A   in the theory     σ matching Φ
            ------------------------------------------
                       |- c(σ) : A[σ]

    σ is a Φ-substitution matching the declared telescope in order:
      * Tyvar entry  -> hol_type
      * Var entry    -> typing_thm certifying the term's type at the
                        Φ-prefix-substituted binder type
      * Assume entry -> thm discharging the formula at the same prefix

    Each Var/Assume σ-entry's `_asl` is absorbed into the result; the
    chosen Var-arg terms appear in the resulting `Const.term_args`."""
    try:
        phi = get_const_phi(name)
        decl_ty = get_const_type(name)
    except KeyError:
        raise HolError(f"CONST: constant {name} is not declared")
    result = _apply_phi_subst(phi, tuple(sigma), f"CONST({name})")
    inst_ty = type_subst(
        result.theta_ty, subst_in_type(result.theta_tm, decl_ty)
    )
    return typing_thm(
        result.asl_extra,
        Const(name, inst_ty, tuple(result.term_args)),
        inst_ty,
    )


def APP(f_th: typing_thm, a_th: typing_thm,
        eq: type_eq_thm | None = None,
        prec: "thm | None" = None) -> typing_thm:
    """appl' (paper P3):  Gamma |- f : Pi(x:A|F). B   Gamma |- a : A
                          Gamma |- F[a/x]
                          --------------------------------------------
                                  Gamma |- f a : B[a/x]

    `eq` (optional) bridges A == A' when a_th._ty differs from f's domain.
    `prec` (required when f's Pi has a non-None precondition) is a `thm`
    whose conclusion is alpha-eq to F[a/x]; its asl is absorbed."""
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
    if f_ty.precondition is not None:
        if prec is None:
            raise HolError(
                f"APP: f's Pi has precondition {_pp_tm(f_ty.precondition)}; "
                f"supply prec= a thm proving its substitution at the arg"
            )
        if not isinstance(prec, thm):
            raise HolError("APP: prec must be a thm")
        needed = _vsubst([(a_th._tm, f_ty.bvar)], f_ty.precondition)
        if not _tm_alpha([], prec._concl, needed):
            raise HolError(
                f"APP: prec proof concludes {_pp_tm(prec._concl)} but "
                f"required precondition (after substitution) is "
                f"{_pp_tm(needed)}"
            )
        asl = term_union(asl, prec._asl)
    elif prec is not None:
        raise HolError("APP: f has no precondition; do not supply prec")
    result_ty = subst_in_type([(a_th._tm, f_ty.bvar)], f_ty.body)
    return typing_thm(asl, Comb(f_th._tm, a_th._tm), result_ty)


def LAMBDA(v: Var, body_th: typing_thm,
           precondition: "term | None" = None) -> typing_thm:
    """lambda' (paper P2):  Gamma, x:A, ▷F |- t : B
                           ------------------------------------
                           Gamma |- (\\x:A|F. t) : Pi(x:A|F). B

    The body's certificate must have been built under `▷F` (i.e. F may
    appear in body_th._asl). LAMBDA captures F as the precondition on
    the resulting Pi/Abs and discharges F (and any assumption mentioning
    v) from the asl. `precondition=None` is the unconditional case
    (F = true) and behaves exactly like the original rule."""
    asl = body_th._asl
    if precondition is not None:
        asl = term_remove(precondition, asl)
    asl = [a for a in asl if not vfree_in(v, a)]
    return typing_thm(
        asl,
        Abs(v, body_th._tm, precondition),
        Pi(v, body_th._ty, precondition),
    )


def CONV(t_th: typing_thm, eq: type_eq_thm) -> typing_thm:
    """Admissible conversion rule: Gamma |- t : A   Gamma |- A == B
                                    -------------------------------
                                          Gamma |- t : B"""
    asl = term_union(t_th._asl, eq._asl)
    return typing_thm(asl, t_th._tm, _other_side(eq, t_th._ty, "CONV"))


def _bridge_matches(eq: type_eq_thm, A: hol_type, B: hol_type) -> bool:
    return (type_eq(eq._lhs, A) and type_eq(eq._rhs, B)) or (
        type_eq(eq._lhs, B) and type_eq(eq._rhs, A)
    )


def _other_side(eq: type_eq_thm, ty: hol_type, ctx: str) -> hol_type:
    """Return whichever side of `eq` is not definitionally `ty`. Raises
    HolError tagged with `ctx` if neither side matches `ty`."""
    if type_eq(eq._lhs, ty):
        return eq._rhs
    if type_eq(eq._rhs, ty):
        return eq._lhs
    raise HolError(
        f"{ctx}: bridge {_pp_ty(eq._lhs)} == {_pp_ty(eq._rhs)} "
        f"does not connect {_pp_ty(ty)}"
    )


def _require_bool(t_th: typing_thm, ctx: str) -> None:
    """Reject typing_thms whose type isn't definitionally bool."""
    if not type_eq(t_th._ty, bool_ty):
        raise HolError(f"{ctx}: non-bool type {_pp_ty(t_th._ty)}")


def _require_eq(c: term, ctx: str) -> None:
    """Reject conclusions that aren't a `=`-headed equation."""
    if not _is_eq(c):
        raise HolError(f"{ctx}: conclusion is not an equation")


def _discharge(prec: "thm | None", F: term, asl: list,
               ctx: str, side: str) -> list:
    """Validate a precondition discharge against `F` and return the
    asl-with-extras.

    Two modes, ordered by user effort:
      - **Explicit:** `prec` is a `thm` whose conclusion is alpha-eq to
        `F`; its asl is absorbed into the result.
      - **Asl-implicit:** `prec is None` and `F` is already alpha-present
        in `asl` (typically because it was introduced upstream by
        `ASSUME` or carried from a typing chain). No new asl entries.

    Used by BETA / MK_COMB / APP to keep the precondition surface
    declarative: if the obligation is already a hypothesis, the user
    doesn't have to re-prove it. `ctx`/`side` are for error labels."""
    if prec is None:
        if not any(_tm_alpha([], a, F) for a in asl):
            raise HolError(
                f"{ctx}: {side} precondition {_pp_tm(F)} not discharged "
                f"(neither supplied as prec nor present in asl)"
            )
        return asl
    if not isinstance(prec, thm):
        raise HolError(f"{ctx}: {side} prec must be a thm")
    if not _tm_alpha([], prec._concl, F):
        raise HolError(
            f"{ctx}: {side} prec concludes {_pp_tm(prec._concl)} but "
            f"required is {_pp_tm(F)}"
        )
    return term_union(asl, prec._asl)


def IMP_TYPE(F_th: typing_thm, G_th: typing_thm) -> typing_thm:
    """Rule D (dependent implication typing):
            Gamma |- F : bool    Gamma, ▷F |- G : bool
            -------------------------------------------
                      Gamma |- F ⇒ G : bool

    The consequent's typing may depend on F being assumed; if G_th's asl
    contains F (typically introduced via a bridge derived from ASSUME(F)),
    that occurrence is discharged in the result, mirroring the paper's
    `▷F` context entry being absorbed by the implication."""
    _require_bool(F_th, "IMP_TYPE antecedent")
    _require_bool(G_th, "IMP_TYPE consequent")
    F_tm = F_th._tm
    asl = term_union(F_th._asl, term_remove(F_tm, G_th._asl))
    return typing_thm(asl, mk_imp(F_tm, G_th._tm), bool_ty)


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


class PhiSide(NamedTuple):
    """One side of a dual Φ-walk -- the σ chosen for either the LHS or
    the RHS of a congruence rule."""
    theta_ty: list      # (chosen_hol_type, Tyvar)
    theta_tm: list      # (chosen_term, Var)
    type_args: list     # chosen hol_types for Tyvar entries (decl. order)
    term_args: list     # chosen terms for Var entries (decl. order)

    @classmethod
    def empty(cls) -> "PhiSide":
        return cls(theta_ty=[], theta_tm=[], type_args=[], term_args=[])


class PhiDualResult(NamedTuple):
    """Output of `_apply_phi_dual`: an LHS side, an RHS side, and the
    asl absorbed from the per-slot certificates."""
    lhs: PhiSide
    rhs: PhiSide
    asl_extra: list


# ---------------------------------------------------------------------------
# Per-slot dispatch
#
# `_SLOT_DISPATCH` is the table that captures the Slot ↔ J-level
# correspondence in one place. Each Slot variant maps to a pair of
# handlers -- one for the single-σ walker (`_apply_phi_subst`) and
# one for the paired σ_l/σ_r walker (`_apply_phi_dual`). Each handler
# checks the evidence's shape (the J-level appropriate type) and
# extracts the per-slot contribution to θ_ty / θ_tm / term_args /
# asl_extra.
#
# Adding a new Slot kind is one new pair of handlers plus one entry
# here -- no edits to either walker.
# ---------------------------------------------------------------------------


def _subst_tyvar(binder, arg, out, ctx):
    if not isinstance(arg, (Tyvar, Tyapp, Pi)):
        raise HolError(
            f"{ctx}: argument for Tyvar binder {binder.name} "
            "must be a hol_type"
        )
    out.theta_ty.append((arg, binder))


def _subst_var(binder, arg, out, ctx):
    if not isinstance(arg, typing_thm):
        raise HolError(
            f"{ctx}: argument for Var binder {binder.name} "
            "must be a typing_thm"
        )
    expected = type_subst(
        out.theta_ty, subst_in_type(out.theta_tm, binder.ty)
    )
    if not type_eq(expected, arg._ty):
        raise HolError(
            f"{ctx}: term argument for {binder.name} has wrong type "
            f"(expected {_pp_ty(expected)}, got {_pp_ty(arg._ty)})"
        )
    out.theta_tm.append((arg._tm, binder))
    out.term_args.append(arg._tm)
    out.asl_extra[:] = term_union(out.asl_extra, arg._asl)


def _subst_assume(binder, arg, out, ctx):
    _check_assume_proof(arg, binder.formula, out.theta_ty, out.theta_tm, ctx)
    out.asl_extra[:] = term_union(out.asl_extra, arg._asl)


def _dual_tyvar(binder, arg, lhs, rhs, asl_extra, ctx):
    if not isinstance(arg, type_eq_thm):
        raise HolError(
            f"{ctx}: argument for Tyvar binder {binder.name} "
            "must be a type_eq_thm"
        )
    lhs.type_args.append(arg._lhs)
    rhs.type_args.append(arg._rhs)
    lhs.theta_ty.append((arg._lhs, binder))
    rhs.theta_ty.append((arg._rhs, binder))
    asl_extra[:] = term_union(asl_extra, arg._asl)


def _dual_var(binder, arg, lhs, rhs, asl_extra, ctx):
    if not isinstance(arg, thm) or not _is_eq(arg._concl):
        raise HolError(
            f"{ctx}: argument for Var binder {binder.name} "
            "must be an equation thm"
        )
    tag = _eq_tag(arg._concl)
    expected = type_subst(
        lhs.theta_ty, subst_in_type(lhs.theta_tm, binder.ty)
    )
    if not type_eq(expected, tag):
        raise HolError(
            f"{ctx}: equation tag {_pp_ty(tag)} does not match "
            f"expected {_pp_ty(expected)} at {binder.name}"
        )
    lhs_tm = _lhs(arg._concl)
    rhs_tm = _rhs(arg._concl)
    lhs.term_args.append(lhs_tm)
    rhs.term_args.append(rhs_tm)
    lhs.theta_tm.append((lhs_tm, binder))
    rhs.theta_tm.append((rhs_tm, binder))
    asl_extra[:] = term_union(asl_extra, arg._asl)


def _dual_assume(binder, arg, lhs, rhs, asl_extra, ctx):
    needed_l = _check_assume_proof(
        arg, binder.formula, lhs.theta_ty, lhs.theta_tm, ctx
    )
    needed_r = _inst_in_term(
        [], rhs.theta_ty, _vsubst(rhs.theta_tm, binder.formula)
    )
    if not _tm_alpha([], needed_l, needed_r):
        raise HolError(
            f"{ctx}: Assume formula's LHS and RHS substitutions "
            "differ; this kernel ships the rule only for the case "
            "where the obligation is symmetric across the two "
            "sides of the congruence"
        )
    asl_extra[:] = term_union(asl_extra, arg._asl)


class _SlotHandlers(NamedTuple):
    """Per-slot dispatch: shape-check + per-J-level extraction."""
    subst: Callable    # (binder, arg, out, ctx) -> None
    dual:  Callable    # (binder, arg, lhs, rhs, asl_extra, ctx) -> None


_SLOT_DISPATCH: dict = {
    Tyvar:  _SlotHandlers(subst=_subst_tyvar,  dual=_dual_tyvar),
    Var:    _SlotHandlers(subst=_subst_var,    dual=_dual_var),
    Assume: _SlotHandlers(subst=_subst_assume, dual=_dual_assume),
}


def _apply_phi_dual(phi, args, ctx: str) -> PhiDualResult:
    """Dual-substitution Φ-walker shared by `TY_CONG_BASE` (type-side
    congruence), `TM_CONG_BASE` (term-side congruence), and
    `THM_CONG_BASE` (staged-axiom congruence).

    Each `args[i]` pairs an LHS and RHS replacement for Φ entry i:
      * Tyvar  -> type_eq_thm `A_l == A_r`
      * Var    -> equation thm `s_l = s_r` tagged at the binder type
                  with all earlier-LHS substitutions applied
      * Assume -> thm proving the formula; the LHS and RHS
                  substitutions of the Assume formula must coincide
                  (kernel ships only this symmetric case).

    Per-slot work is dispatched through `_SLOT_DISPATCH`."""
    if len(phi) != len(args):
        raise HolError(
            f"{ctx}: wrong number of arguments "
            f"(expected {len(phi)}, got {len(args)})"
        )
    lhs = PhiSide.empty()
    rhs = PhiSide.empty()
    asl_extra: list = []
    for binder, arg in zip(phi, args):
        handlers = _SLOT_DISPATCH.get(type(binder))
        if handlers is None:
            raise HolError(f"{ctx}: ill-formed Φ entry")
        handlers.dual(binder, arg, lhs, rhs, asl_extra, ctx)
    return PhiDualResult(lhs=lhs, rhs=rhs, asl_extra=asl_extra)


def TY_CONG_BASE(tyop: str, args: list) -> type_eq_thm:
    """congBase':  a(Φ) declared in theory      per-slot Φ-args
                  ----------------------------------------------
                          Gamma |- a(σ_l) == a(σ_r)

    Each `args[i]` matches Φ entry i (see `_apply_phi_dual`)."""
    try:
        phi = get_type_kind(tyop)
    except KeyError:
        raise HolError(f"TY_CONG_BASE: unknown type {tyop}")
    result = _apply_phi_dual(phi, args, f"TY_CONG_BASE({tyop})")
    return type_eq_thm(
        result.asl_extra,
        Tyapp(tyop, tuple(result.lhs.type_args), tuple(result.lhs.term_args)),
        Tyapp(tyop, tuple(result.rhs.type_args), tuple(result.rhs.term_args)),
    )


def TM_CONG_BASE(name: str, args: list,
                 cod_eq: type_eq_thm | None = None) -> thm:
    """Term-side congruence (analogue of TY_CONG_BASE for a staged
    term constant):
            c(Φ) : A in theory      per-slot Φ-args
            -----------------------------------------------
                  Gamma |- c(σ_l) =A[σ_l] c(σ_r)

    Each `args[i]` matches Φ entry i (see `_apply_phi_dual`). The
    equation is tagged at the LHS view `A[σ_l]`.

    With a dependent body type whose two sides differ -- A[σ_l] !=
    A[σ_r] -- supply `cod_eq` witnessing the bridge; the equation is
    still tagged at A[σ_l] and the RHS Const carries its native type
    A[σ_r]."""
    try:
        phi = get_const_phi(name)
        decl_ty = get_const_type(name)
    except KeyError:
        raise HolError(f"TM_CONG_BASE: unknown constant {name}")
    result = _apply_phi_dual(phi, args, f"TM_CONG_BASE({name})")
    inst_ty_l = type_subst(
        result.lhs.theta_ty, subst_in_type(result.lhs.theta_tm, decl_ty)
    )
    inst_ty_r = type_subst(
        result.rhs.theta_ty, subst_in_type(result.rhs.theta_tm, decl_ty)
    )
    asl = result.asl_extra
    if not type_eq(inst_ty_l, inst_ty_r):
        if cod_eq is None or not _bridge_matches(
            cod_eq, inst_ty_l, inst_ty_r
        ):
            raise HolError(
                f"TM_CONG_BASE: instantiated types differ "
                f"({_pp_ty(inst_ty_l)} vs {_pp_ty(inst_ty_r)}); "
                f"supply cod_eq witnessing A[σ_l] == A[σ_r]"
            )
        asl = term_union(asl, cod_eq._asl)
    lhs_const = Const(name, inst_ty_l, tuple(result.lhs.term_args))
    rhs_const = Const(name, inst_ty_r, tuple(result.rhs.term_args))
    return thm(asl, safe_mk_eq(inst_ty_l, lhs_const, rhs_const))


def THM_CONG_BASE(staged: StagedThm, args: list) -> thm:
    """Staged-axiom congruence (analogue of TY_CONG_BASE / TM_CONG_BASE
    for a staged axiom):
            (Φ) ▷ F in theory      per-slot Φ-args
            -------------------------------------------
                  Gamma |- F[σ_l] = F[σ_r]  : bool

    Each `args[i]` matches Φ entry i (see `_apply_phi_dual`)."""
    if not isinstance(staged, StagedThm):
        raise HolError("THM_CONG_BASE: first argument must be a StagedThm")
    phi = staged._phi
    F = staged._body.formula
    result = _apply_phi_dual(phi, args, "THM_CONG_BASE")
    F_l = _inst_in_term(
        [], result.lhs.theta_ty, _vsubst(result.lhs.theta_tm, F)
    )
    F_r = _inst_in_term(
        [], result.rhs.theta_ty, _vsubst(result.rhs.theta_tm, F)
    )
    return thm(result.asl_extra, safe_mk_eq(bool_ty, F_l, F_r))


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
# Validity rules: REFL, ASSUME, BETA, ETA, EQ_TY_CONV, TRANS, MK_COMB, ABS,
# EQ_MP, DISCH, MP, DEDUCT_ANTISYM_RULE, INST, INST_TYPE
# (DISCH / MP are the implication-intro / modus ponens pair for the
# primitive `==>`; their typing-layer companion is IMP_TYPE / Rule D.)
# ---------------------------------------------------------------------------


def REFL(t_th: typing_thm) -> thm:
    return thm(t_th._asl, safe_mk_eq(t_th._ty, t_th._tm, t_th._tm))


def ASSUME(F_th: typing_thm) -> thm:
    _require_bool(F_th, "ASSUME")
    return thm([F_th._tm, *F_th._asl], F_th._tm)


def BETA(redex_th: typing_thm, prec: "thm | None" = None) -> thm:
    """Trivial beta:  Gamma |- (\\x:A|F. t) x : B
                     [prec : Gamma' |- F  OR  F in Gamma]
                     -------------------------------------
                     Gamma (+ Gamma') |- (\\x:A|F. t) x = t

    When the Abs carries a precondition F, the discharge is required:
    either pass `prec=` a thm proving F (its asl is absorbed), or have
    F already alpha-present in `redex_th._asl` (the asl-implicit form;
    no extra asl). Since the redex is trivial (arg == bvar), no
    substitution is applied to F."""
    tm = redex_th._tm
    if not (
        isinstance(tm, Comb)
        and isinstance(tm.fun, Abs)
        and tm.arg == tm.fun.bvar
    ):
        raise HolError("BETA: not a trivial beta-redex")
    abs_node = tm.fun
    asl = redex_th._asl
    if abs_node.precondition is not None:
        asl = _discharge(prec, abs_node.precondition, asl, "BETA", "redex")
    elif prec is not None:
        raise HolError("BETA: Abs has no precondition; do not supply prec")
    return thm(asl, safe_mk_eq(redex_th._ty, tm, abs_node.body))


def ETA(t_th: typing_thm) -> thm:
    """etaPi:  Gamma |- t : Pi(x:A|F). B
              ---------------------------------
              Gamma |- t = (\\x:A|F. t x)

    The bound variable is chosen fresh to avoid capture in t and in F.
    The precondition F (if any) is threaded onto the RHS abstraction
    (with the binder renamed). The equation itself doesn't discharge F:
    semantically, at non-F arguments both sides are equally undefined."""
    f_ty = t_th._ty
    if not isinstance(f_ty, Pi):
        raise HolError(f"ETA: term type is not a Pi (got {_pp_ty(f_ty)})")
    avoid = frees(t_th._tm)
    if f_ty.precondition is not None:
        avoid = term_union(avoid, frees(f_ty.precondition))
    fresh_v = variant(avoid, f_ty.bvar)
    new_prec = (
        None if f_ty.precondition is None
        else _vsubst([(fresh_v, f_ty.bvar)], f_ty.precondition)
    )
    eta_form = Abs(fresh_v, Comb(t_th._tm, fresh_v), new_prec)
    return thm(t_th._asl, safe_mk_eq(t_th._ty, t_th._tm, eta_form))


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
    _require_eq(c, "EQ_TY_CONV")
    A = _eq_tag(c)
    B = _other_side(ty_eq, A, "EQ_TY_CONV")
    new_eq_const = Const("=", Pi(Var("_", B), Pi(Var("_", B), bool_ty)))
    s, t = _lhs(c), _rhs(c)
    new_concl = Comb(Comb(new_eq_const, s), t)
    return thm(term_union(eq_th._asl, ty_eq._asl), new_concl)


def TRANS(th1: thm, th2: thm) -> thm:
    c1, c2 = th1._concl, th2._concl
    _require_eq(c1, "TRANS")
    _require_eq(c2, "TRANS")
    if not type_eq(_eq_tag(c1), _eq_tag(c2)):
        raise HolError(
            f"TRANS: equation types differ "
            f"({_pp_ty(_eq_tag(c1))} vs {_pp_ty(_eq_tag(c2))}); "
            f"use EQ_TY_CONV to align first"
        )
    if not _tm_alpha([], _rhs(c1), _lhs(c2)):
        raise HolError("TRANS: middle terms do not match")
    return thm(term_union(th1._asl, th2._asl), Comb(c1.fun, _rhs(c2)))


def MK_COMB(th1: thm, th2: thm,
            eq: type_eq_thm | None = None,
            cod_eq: type_eq_thm | None = None,
            prec: "thm | tuple | None" = None) -> thm:
    """congAppl':  Gamma |- f =Pi(x:A|F).B f'    Gamma |- a =A a'
                  prec_l : Gamma_l |- F[a/x]   prec_r : Gamma_r |- F[a'/x]
                  ----------------------------------------------------------
                            Gamma + ... |- f a =B[a/x] f' a'

    With a dependent codomain B and a propositional (rather than
    definitional) argument equation l2 = r2, the natural LHS type
    B[l2/x] and RHS type B[r2/x] differ. ``cod_eq`` witnesses that
    bridge; the result is tagged at B[l2/x]. ``eq`` is the domain
    bridge (used when the argument's equation tag doesn't match the
    function's Pi-domain definitionally).

    When the function's Pi carries a precondition F, each side's
    obligation `F[l2/x]` / `F[r2/x]` must be discharged. ``prec`` is
    one of:

      - ``thm`` -- single discharge used for both sides; requires
        `F[l2/x]` and `F[r2/x]` to coincide alpha-eq (typical when F
        is closed in x). The thm's asl is absorbed once.
      - ``(left, right)`` -- per-side tuple; each entry is a ``thm``
        or ``None``.
      - ``None`` -- equivalent to ``(None, None)``.

    A ``None`` slot is the asl-implicit form: that side's F-instance
    must already be alpha-present in the running asl (typically
    introduced upstream by ``ASSUME``)."""
    c1, c2 = th1._concl, th2._concl
    _require_eq(c1, "MK_COMB")
    _require_eq(c2, "MK_COMB")
    f_ty = _eq_tag(c1)
    arg_ty = _eq_tag(c2)
    if not isinstance(f_ty, Pi):
        raise HolError(
            f"MK_COMB: function-side equation type is not Pi "
            f"(got {_pp_ty(f_ty)})"
        )
    expected = f_ty.bvar.ty
    asl = term_union(th1._asl, th2._asl)
    if not type_eq(expected, arg_ty):
        if eq is None or not _bridge_matches(eq, expected, arg_ty):
            raise HolError(
                f"MK_COMB: domain types do not agree "
                f"(expected {_pp_ty(expected)}, got {_pp_ty(arg_ty)})"
            )
        asl = term_union(asl, eq._asl)
    l1, r1 = _lhs(c1), _rhs(c1)
    l2, r2 = _lhs(c2), _rhs(c2)
    if f_ty.precondition is not None:
        needed_l = _vsubst([(l2, f_ty.bvar)], f_ty.precondition)
        needed_r = _vsubst([(r2, f_ty.bvar)], f_ty.precondition)
        if isinstance(prec, tuple):
            if len(prec) != 2:
                raise HolError(
                    f"MK_COMB: prec tuple must be (left, right), got "
                    f"length {len(prec)}"
                )
            prec_l, prec_r = prec
            asl = _discharge(prec_l, needed_l, asl, "MK_COMB", "F[l2/x]")
            asl = _discharge(prec_r, needed_r, asl, "MK_COMB", "F[r2/x]")
        else:
            if prec is not None and not _tm_alpha([], needed_l, needed_r):
                raise HolError(
                    f"MK_COMB: single-thm prec requires F[l2/x] and "
                    f"F[r2/x] to coincide alpha-eq (got {_pp_tm(needed_l)} "
                    f"vs {_pp_tm(needed_r)}); pass prec=(left, right)"
                )
            asl = _discharge(prec, needed_l, asl, "MK_COMB", "F[l2/x]=F[r2/x]")
    elif prec is not None:
        raise HolError(
            "MK_COMB: function's Pi has no precondition; do not supply prec"
        )
    result_ty_l = subst_in_type([(l2, f_ty.bvar)], f_ty.body)
    result_ty_r = subst_in_type([(r2, f_ty.bvar)], f_ty.body)
    if not type_eq(result_ty_l, result_ty_r):
        if cod_eq is None or not _bridge_matches(
            cod_eq, result_ty_l, result_ty_r
        ):
            raise HolError(
                f"MK_COMB: codomain types do not agree "
                f"({_pp_ty(result_ty_l)} vs {_pp_ty(result_ty_r)}); "
                f"supply cod_eq witnessing B[l2/x] == B[r2/x]"
            )
        asl = term_union(asl, cod_eq._asl)
    return thm(asl, safe_mk_eq(result_ty_l, Comb(l1, l2), Comb(r1, r2)))


def ABS(v: Var, th: thm, ty_eq: type_eq_thm | None = None) -> thm:
    """congLambda':  Gamma |- A == A'    Gamma, x:A |- t =B t'
                    ------------------------------------------------
                    Gamma |- (\\x:A. t) =Pi(x:A).B (\\x:A'. t')

    Without ``ty_eq`` this is the homogeneous case (A == A'). With
    ``ty_eq``, ``v.ty`` must match one side of the bridge and the
    other side becomes the RHS binder type; the result is tagged at
    Pi(x:A). B (the LHS view). ``v`` must not occur free in any
    hypothesis, including the bridge's."""
    c = th._concl
    _require_eq(c, "ABS")
    if any(vfree_in(v, a) for a in th._asl):
        raise HolError("ABS: bound variable occurs free in hypotheses")
    body_ty = _eq_tag(c)
    l, r = _lhs(c), _rhs(c)
    if ty_eq is None:
        v_rhs = v
        asl = th._asl
    else:
        if any(vfree_in(v, a) for a in ty_eq._asl):
            raise HolError(
                "ABS: bound variable occurs free in bridge hypotheses"
            )
        v_rhs = Var(v.name, _other_side(ty_eq, v.ty, "ABS"))
        asl = term_union(th._asl, ty_eq._asl)
    new_ty = Pi(v, body_ty)
    return thm(asl, safe_mk_eq(new_ty, Abs(v, l), Abs(v_rhs, r)))


def EQ_MP(th1: thm, th2: thm) -> thm:
    c = th1._concl
    _require_eq(c, "EQ_MP")
    if not type_eq(_eq_tag(c), bool_ty):
        raise HolError(
            f"EQ_MP: equation tag must be bool (got {_pp_ty(_eq_tag(c))})"
        )
    if not _tm_alpha([], _lhs(c), th2._concl):
        raise HolError("EQ_MP: lhs of equation does not match th2's conclusion")
    return thm(term_union(th1._asl, th2._asl), _rhs(c))


def DISCH(F_th: typing_thm, th: thm) -> thm:
    """Implication introduction:
            Gamma |- F : bool    Gamma, F |- G
            ----------------------------------
                  Gamma |- F ⇒ G

    The antecedent's typing is supplied by F_th; its assumptions (if any)
    join the result's. F is removed from th._asl. A vacuous discharge --
    F not in th._asl -- is permitted, matching HOL Light's DISCH."""
    _require_bool(F_th, "DISCH antecedent")
    F_tm = F_th._tm
    asl = term_union(F_th._asl, term_remove(F_tm, th._asl))
    return thm(asl, mk_imp(F_tm, th._concl))


def MP(imp_th: thm, ant_th: thm) -> thm:
    """Modus ponens:
            Gamma1 |- F ⇒ G    Gamma2 |- F
            ------------------------------
                  Gamma1 ∪ Gamma2 |- G"""
    c = imp_th._concl
    if not _is_imp(c):
        raise HolError("MP: first argument is not an implication")
    F = _imp_ant(c)
    G = _imp_con(c)
    if not _tm_alpha([], F, ant_th._concl):
        raise HolError(
            "MP: antecedent does not match second argument's conclusion"
        )
    return thm(term_union(imp_th._asl, ant_th._asl), G)


def DEDUCT_ANTISYM_RULE(th1: thm, th2: thm) -> thm:
    asl1 = term_remove(th2._concl, th1._asl)
    asl2 = term_remove(th1._concl, th2._asl)
    return thm(
        term_union(asl1, asl2),
        safe_mk_eq(bool_ty, th1._concl, th2._concl),
    )


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
    collide with a free one in the body. Well-formedness of replacement
    types is the caller's responsibility (honest-caller perimeter)."""
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


def new_axiom(F_th: typing_thm, phi: tuple | None = None) -> StagedThm:
    """Declare an axiom `(Φ) ▷ F`. Returns a StagedThm; use
    `interpret(staged, σ)` to instantiate.

    Φ is a telescope of Tyvar | Var | Assume binders, same vocabulary
    as on `new_type` / `new_constant`. When Φ is empty (the default),
    the axiom is concrete: `F_th` must be unconditional, free of Vars,
    and free of Tyvars not already in Φ.

    Otherwise Φ binds the axiom's parameters:
      * `F_th._asl` entries must alpha-match Assume formulas in Φ;
      * free Vars of `F_th._tm` must be bound by Var entries in Φ;
      * free Tyvars of `F_th._tm` must be bound by Tyvar entries in Φ.
    """
    _require_bool(F_th, "new_axiom")
    if phi is None:
        phi = ()
    _check_phi(phi, "new_axiom")
    phi = tuple(phi)

    expected_asl = _phi_asl(phi)
    for a in F_th._asl:
        if not any(_tm_alpha([], a, f) for f in expected_asl):
            raise HolError(
                "new_axiom: asl entry "
                f"{_pp_tm(a)} is not declared by any Assume entry in Φ"
            )

    bound_vars = [b for b in phi if isinstance(b, Var)]
    for fv in frees(F_th._tm):
        if fv not in bound_vars:
            raise HolError(
                f"new_axiom: free var {fv.name} is not bound by "
                f"any Var entry in Φ"
            )

    allowed_tvs = [b for b in phi if isinstance(b, Tyvar)]
    for tv in type_vars_in_term(F_th._tm):
        if tv not in allowed_tvs:
            raise HolError(
                f"new_axiom: type-var {tv.name} is not reflected in Φ"
            )

    staged = StagedThm(phi, PropBody(F_th._tm))
    the_axioms.append(staged)
    return staged


def interpret(staged: StagedThm, sigma: tuple) -> thm:
    """One-shot interpretation of a staged thm at σ.

    Walks Φ left-to-right, discharging slot-by-slot:
      * Tyvar slot  -- σ-entry is a `hol_type` (INST_TYPE-style);
      * Var slot    -- σ-entry is a `typing_thm` (INST-style; its
                       _ty must match the binder type under
                       earlier substitutions);
      * Assume slot -- σ-entry is a `thm` discharging the Assume
                       formula under earlier substitutions (MP-style).

    σ-shape is validated by `_apply_phi_subst` -- the same walker
    `mk_type` and `CONST` use.

    The result is a closed `thm`: Γ |- F[σ], whose asl absorbs the
    typing_thm and Assume-proof assumptions from σ; the original
    Assume-formula asl entries are discharged."""
    if not isinstance(staged, StagedThm):
        raise HolError("interpret: first argument must be a StagedThm")
    phi = staged._phi
    F = staged._body.formula
    result = _apply_phi_subst(phi, tuple(sigma), "interpret")
    f = lambda tm: _inst_in_term(
        [], result.theta_ty, _vsubst(result.theta_tm, tm)
    )
    return thm(result.asl_extra, f(F))


def instantiate(target, sigma: tuple):
    """Unified Φ-substitution dispatcher.

    Dispatches by J-level of `target`:
      * type-name str (TpBody)  -- `mk_type(target, sigma)` → hol_type
      * const-name str (TmBody) -- `CONST(target, sigma)`   → typing_thm
      * StagedThm               -- `interpret(target, sigma)` → thm

    The three primary entry points (`mk_type`, `CONST`, `interpret`)
    remain available; `instantiate` is the J-agnostic alias that all
    three share -- the validator `_apply_phi_subst` is the same in
    every case, and the only difference is which evidence-shape the
    target's body asks for."""
    if isinstance(target, StagedThm):
        return interpret(target, sigma)
    if isinstance(target, str):
        d = the_decls.get(target)
        if d is None:
            raise HolError(f"instantiate: unknown name {target}")
        if isinstance(d.body, TpBody):
            return mk_type(target, list(sigma))
        if isinstance(d.body, TmBody):
            return CONST(target, tuple(sigma))
    raise HolError(
        f"instantiate: target must be a declared name or a StagedThm "
        f"(got {target!r})"
    )


the_definitions: list = []


def definitions() -> list:
    return list(the_definitions)


def new_basic_definition(lhs: Var, rhs_th: typing_thm,
                         phi: tuple | None = None) -> thm:
    """Define a new staged constant `lhs(Φ) := rhs_th`.

    Φ is a telescope of binders (Tyvar | Var | Assume). When `phi` is
    None, Φ defaults to the free Tyvars of `lhs.ty` (in first-appearance
    order); pass `phi` explicitly to add Var/Assume entries or to order
    Tyvar slots.

    The rhs's free Vars must all be bound by Var entries in Φ, and its
    `_asl` entries must alpha-match Assume formulas in Φ. Type-variables
    of rhs must be reflected in Φ or in `lhs.ty`.

    The emitted defining equation is `[asl] |- lhs(σ_Φ) = rhs_th._tm`
    where σ_Φ applies Φ to its own binders -- i.e. the constant is
    introduced at its declaration-site Φ-application."""
    if not type_eq(lhs.ty, rhs_th._ty):
        raise HolError("new_basic_definition: declared type does not match rhs")
    if phi is None:
        phi = tuple(Tyvar(tv.name) for tv in tyvars(lhs.ty))
    else:
        _check_phi(phi, f"new_basic_definition({lhs.name})")
        phi = tuple(phi)
    bound_vars = [b for b in phi if isinstance(b, Var)]
    expected_asl: list = []
    for b in phi:
        if isinstance(b, Assume):
            expected_asl = term_union(expected_asl, [b.formula])
    for a in rhs_th._asl:
        if not any(_tm_alpha([], a, f) for f in expected_asl):
            raise HolError(
                "new_basic_definition: rhs asl entry "
                f"{_pp_tm(a)} is not declared by any Assume entry in Φ"
            )
    for fv in frees(rhs_th._tm):
        if fv not in bound_vars:
            raise HolError(
                f"new_basic_definition: rhs free var {fv.name} is not "
                f"bound by any Var entry in Φ"
            )
    allowed_tvs = list(tyvars(lhs.ty))
    for b in phi:
        if isinstance(b, Tyvar) and b not in allowed_tvs:
            allowed_tvs.append(b)
    for tv in type_vars_in_term(rhs_th._tm):
        if tv not in allowed_tvs:
            raise HolError(
                f"new_basic_definition: rhs type-var {tv.name} is not "
                f"reflected in Φ or in lhs type"
            )
    new_constant(lhs.name, lhs.ty, phi=phi)
    # Apply Φ to itself: σ replaces each binder with itself.
    self_sigma: list = []
    for b in phi:
        if isinstance(b, Tyvar):
            self_sigma.append(b)
        elif isinstance(b, Var):
            self_sigma.append(typing_thm([], b, b.ty))
        elif isinstance(b, Assume):
            self_sigma.append(thm([b.formula], b.formula))
    c_th = CONST(lhs.name, sigma=tuple(self_sigma))
    dth = thm(c_th._asl, safe_mk_eq(rhs_th._ty, c_th._tm, rhs_th._tm))
    the_definitions.append(dth)
    return dth


# ---------------------------------------------------------------------------
# Demo: vectors indexed by nat, with a propositional type bridge
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    # nat as a base type, with "0" as the atomic inhabitation witness.
    nat_ty = Tyapp("nat", (), ())
    new_type("nat", phi=(), witness=("0", nat_ty))
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

    # vec : (n:nat) -> tp, with nil : vec(0) as the atomic inhabitation witness.
    zero_const = Const("0", nat_ty)
    nil_ty = Tyapp("vec", (), (zero_const,))
    new_type(
        "vec",
        phi=(Var("n", nat_ty),),
        witness=("nil", nil_ty),
    )

    def vec(n_th):
        return mk_type("vec", [n_th])

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
    eq_form = APP(APP(CONST("=", (nat_ty,)), add_0_n), VAR(n_var))
    print("axiom term ::", _pp_tm(eq_form._tm), ":", _pp_ty(eq_form._ty))
    add_zero = new_axiom(eq_form, phi=(n_var,))  # (n:nat) ▷ add 0 n = n
    print("axiom      ::", add_zero)

    # Specialize n := 0 in one step via interpret(σ).
    add_0_0_eq_0 = interpret(add_zero, (zero_th,))
    print("interpreted::", add_0_0_eq_0)

    # Lift to type equality vec(add 0 0) == vec 0
    vec_bridge = TY_CONG_BASE("vec", [add_0_0_eq_0])
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
    def _eq_tag_str(th):
        return _pp_ty(_eq_tag(th._concl))

    nil_refl = REFL(nil_th)
    print(f"REFL(nil)                :: {nil_refl}  [= tagged at {_eq_tag_str(nil_refl)}]")
    # The CONV'd typing_thm (nil_at_add : vec(add 0 0)) now flows its
    # certificate type into REFL, so the equation gets tagged at
    # vec(add 0 0), not at the intrinsic vec(0). Pre-fix this would
    # have read type_of(nil) = vec(0).
    nil_refl_via_cert = REFL(nil_at_add)
    print(f"REFL(nil_at_add)         :: {nil_refl_via_cert}  "
          f"[= tagged at {_eq_tag_str(nil_refl_via_cert)}]")
    # nil_refl's = constant is tagged at vec(0). Re-tag via the bridge
    # vec(add 0 0) == vec(0) (which here happens to have empty asl).
    nil_refl_at_add = EQ_TY_CONV(nil_refl, vec_bridge)
    print(f"EQ_TY_CONV via vec_bridge:: {nil_refl_at_add}  [= tagged at {_eq_tag_str(nil_refl_at_add)}]")

    # Demonstrate hypothesis propagation: ASSUME the same equation
    # add 0 0 = 0, lift it, and use the resulting bridge in EQ_TY_CONV;
    # the assumption should appear in the result's asl.
    print()
    assumed_eq = ASSUME(eq_form)  # not quite -- eq_form is the universally
                                  # quantified form. Let's specialise:
    # Build an assumption form with n bound to 0:
    n0_eq = APP(APP(CONST("=", (nat_ty,)),
                    APP(APP(add_th, zero_th), zero_th)),
                zero_th)
    print("assumption term ::", _pp_tm(n0_eq._tm))
    assumed_n0 = ASSUME(n0_eq)
    print("ASSUME           ::", assumed_n0)
    vec_bridge_hyp = TY_CONG_BASE("vec", [assumed_n0])
    print("derived bridge   ::", vec_bridge_hyp)
    nil_refl_hyp = EQ_TY_CONV(nil_refl, vec_bridge_hyp)
    print(f"EQ_TY_CONV w/ hyp:: {nil_refl_hyp}  [= tagged at {_eq_tag_str(nil_refl_hyp)}]")

    # ----------------------------------------------------------------
    # Atomic new_type: every type lands in the kernel with its witness.
    # Inhabitation is correct by construction -- no runtime tracking,
    # no theory-layer check to forget.
    # ----------------------------------------------------------------
    print()
    new_type("phantom", (), witness=("ghost", Tyapp("phantom", (), ())))
    print("declared phantom with witness ghost")

    # Missing witness -> rejected at the kernel boundary:
    try:
        new_type("orphan", ())
    except HolError as e:
        print("rejects missing witness ::", str(e).splitlines()[0])

    # Witness with wrong head -> rejected:
    try:
        new_type(
            "stranger", (),
            witness=("misfit", Tyapp("nat", (), ())),
        )
    except HolError as e:
        print("rejects wrong-head witness ::", str(e).splitlines()[0])

    # ----------------------------------------------------------------
    # congLambda' (ABS with binder-type bridge) and congAppl'
    # (MK_COMB with codomain bridge): exercise the heterogeneous case.
    # ----------------------------------------------------------------
    print()
    # Build (\v:vec 0. 0) = (\v:vec(add 0 0). 0) via ABS + the type
    # bridge vec(0) == vec(add 0 0). REFL gives the body equality; the
    # bridge is precisely vec_bridge (or its TY_SYM).
    body_zero = REFL(zero_th)  # |- 0 = 0  at type nat
    v_at_vec0 = Var("v", vec(zero_th))
    abs_hetero = ABS(v_at_vec0, body_zero, ty_eq=TY_SYM(vec_bridge))
    print("ABS with ty_eq ::", abs_hetero)

    # Now MK_COMB with a dependent codomain. f = g at Pi(n:nat). vec n,
    # applied to an argument equation l2 = r2 where l2 != r2 forces the
    # natural codomain types vec(l2) and vec(r2) to differ.
    #
    # Construct a constant family `mkvec : Pi(n:nat). vec n` so REFL
    # gives us |- mkvec = mkvec at Pi(n:nat). vec n. Pair with the
    # specialised argument equation add 0 0 = 0 (i.e. add_0_0_eq_0):
    # MK_COMB now needs cod_eq witnessing vec(add 0 0) == vec(0).
    print()
    new_constant("mkvec", Pi(n_var, vec(n_th)))
    mkvec_th = CONST("mkvec")
    f_eq = REFL(mkvec_th)
    # We need add_0_0_eq_0 tagged at nat (it already is).
    try:
        # First show the call fails without cod_eq:
        MK_COMB(f_eq, add_0_0_eq_0)
    except HolError as e:
        print("without cod_eq ::", str(e).splitlines()[0])
    bridged = MK_COMB(f_eq, add_0_0_eq_0, cod_eq=vec_bridge)
    print("MK_COMB with cod_eq ::", bridged)

    # ----------------------------------------------------------------
    # Primitive `==>` and Rule D (dependent implication typing).
    # Example 3 from the paper, adapted: x = y ⇒ f x = f y where f is a
    # dependent function. Type-checking the consequent f x = f y at
    # type bool needs the assumption x = y to bridge vec(x) ≡ vec(y)
    # (here we use add 0 0 = 0 ⇒ nil =vec(0) nil-coerced, since we have
    # that bridge already).
    # ----------------------------------------------------------------
    print()
    # Antecedent: add 0 0 = 0  (as a bool typing_thm)
    ant_typing = APP(APP(CONST("=", (nat_ty,)), add00_th), zero_th)
    print("antecedent F ::", _pp_tm(ant_typing._tm), ":", _pp_ty(ant_typing._ty))

    # Consequent G typed under ▷F: build nil =vec(0) (nil viewed via bridge).
    # The ASSUMEd equation builds a bridge whose asl mentions F; CONV
    # through that bridge lifts nil's certificate, and REFL emits a thm
    # whose asl tracks the dependency. Then we wrap as a bool typing_thm.
    assumed_F = ASSUME(ant_typing)
    bridge_under_F = TY_CONG_BASE("vec", [assumed_F])
    nil_under_F = CONV(nil_th, TY_SYM(bridge_under_F))
    print("nil under ▷F  ::", nil_under_F)

    # Consequent term: nil =vec(add 0 0) nil  (well-typed under ▷F).
    cons_eq_term = APP(
        APP(CONST("=", (nil_under_F._ty,)), nil_under_F),
        nil_under_F,
    )
    print("consequent G typing ::", cons_eq_term)

    # IMP_TYPE discharges F from the consequent's asl.
    imp_typing = IMP_TYPE(ant_typing, cons_eq_term)
    print("F ⇒ G typing ::", imp_typing)
    print("            asl =", imp_typing._asl)  # F should be gone

    # Now exercise the validity-layer pair. Build `[F] |- G` as a thm,
    # DISCH F to get `|- F ⇒ G`, then MP-apply with an axiom that
    # provides F.
    g_under_F = REFL(nil_under_F)  # [F] |- (nil =vec(0) nil)
    print("[F] |- G  ::", g_under_F)
    imp_thm = DISCH(ant_typing, g_under_F)
    print("DISCH F   ::", imp_thm)

    # Now MP with the axiom add_0_0_eq_0 (which is [] |- add 0 0 = 0).
    g_thm = MP(imp_thm, add_0_0_eq_0)
    print("MP(F⇒G, F) ::", g_thm)

    # ----------------------------------------------------------------
    # Unified declaration context: rank-1 polymorphism interleaved with
    # dependent term parameters. Declare
    #
    #   pvec : (u:Type, n:nat) -> tp        -- vector of u of length n
    #   pnil : pvec(bool, 0)                -- inhabitation witness
    #   pcons : Pi(u:Type). Pi(n:nat). u -> pvec(u, n) -> pvec(u, S n)
    #
    # This exercises a context with BOTH a Tyvar binder and a Var
    # binder, demonstrating that later context entries may use earlier
    # ones (here `n:nat` could in principle reference `u:Type` -- not
    # exercised, but the shape is general).
    # ----------------------------------------------------------------
    print()
    u_tv = Tyvar("u")
    pvec_pnil_ty = Tyapp("pvec", (bool_ty,), (Const("0", nat_ty),))
    new_type(
        "pvec",
        phi=(u_tv, Var("n", nat_ty)),
        witness=("pnil", pvec_pnil_ty),
    )

    def pvec(u_ty, n_th):
        return mk_type("pvec", [u_ty, n_th])

    pnil_th = CONST("pnil")
    print("pnil ::", _pp_ty(pnil_th._ty))
    print("pvec(nat, 0) ::", _pp_ty(pvec(nat_ty, zero_th)))
    print("pvec(bool, S 0) ::", _pp_ty(pvec(bool_ty, one_th)))

    # Build a value at pvec(bool, 0) (just pnil) and a wrong-arity call.
    try:
        mk_type("pvec", [bool_ty])  # missing the term arg
    except HolError as e:
        print("wrong arity ::", str(e).splitlines()[0])

    # Wrong shape: pass a hol_type where a typing_thm is expected.
    try:
        mk_type("pvec", [bool_ty, nat_ty])
    except HolError as e:
        print("wrong shape ::", str(e).splitlines()[0])

    # TY_CONG_BASE with mixed argument shapes: pvec(bool, add 0 0) ==
    # pvec(bool, 0) via type-refl on the u slot and add_0_0_eq_0 on n.
    bool_refl = TY_REFL(bool_ty)
    pvec_bridge = TY_CONG_BASE("pvec", [bool_refl, add_0_0_eq_0])
    print("pvec bridge ::", pvec_bridge)

    # Cross-instantiation: pvec(nat, 0) == pvec(bool, 0) would need a
    # non-trivial type equality on u, which we can't prove (and rightly
    # so). Show that passing TY_REFL of two different types in the u
    # slot via the bridge yields well-formed but distinct Tyapps.
    # Instead, exercise the typing-bridge inside CONV using pvec_bridge.
    pnil_at_add = CONV(pnil_th, TY_SYM(pvec_bridge))
    print("pnil viewed as pvec(bool, add 0 0) ::", _pp_ty(pnil_at_add._ty))

    # ----------------------------------------------------------------
    # Cross-binder dependence: a Var binder whose type mentions an
    # earlier Tyvar binder.
    #
    #   tagged : (u:Type, x:u) -> tp
    #
    # Here the second context entry x has type `u`, which is bound by
    # the first. At use sites we substitute the chosen hol_type for u
    # into x's expected type before tag-checking. This is the case the
    # 2026 paper's `Φ`-contexts make routine and the old flat
    # `term_params: tuple[hol_type,...]` cannot express.
    # ----------------------------------------------------------------
    print()
    u_tv2 = Tyvar("u")
    x_var2 = Var("x", u_tv2)
    tagged_witness_ty = Tyapp("tagged", (nat_ty,), (Const("0", nat_ty),))
    new_type(
        "tagged",
        phi=(u_tv2, x_var2),
        witness=("tagzero", tagged_witness_ty),
    )

    # Use: tagged(nat, 0) is well-formed because zero_th : nat matches
    # the binder type u with u := nat.
    tagged_nat0 = mk_type("tagged", [nat_ty, zero_th])
    print("tagged(nat, 0)  ::", _pp_ty(tagged_nat0))

    # tagged(bool, nil_th) would fail: nil_th : vec(0) does not match
    # the binder type u with u := bool.
    try:
        mk_type("tagged", [bool_ty, zero_th])
    except HolError as e:
        print("cross-dep mismatch ::", str(e).splitlines()[0])

    # TY_CONG_BASE on tagged: the n-position equation's tag must be
    # whatever type the earlier Tyvar slot chose. Use TY_REFL on u
    # to keep the type slot at nat, and add_0_0_eq_0 (tagged at nat)
    # for the x slot.
    nat_refl = TY_REFL(nat_ty)
    tagged_bridge = TY_CONG_BASE("tagged", [nat_refl, add_0_0_eq_0])
    print("tagged bridge   ::", tagged_bridge)

    # The tag-vs-prefix check actually fires: if we pick u := bool but
    # supply an equation tagged at nat (add_0_0_eq_0), it's rejected.
    bool_refl_again = TY_REFL(bool_ty)
    try:
        TY_CONG_BASE("tagged", [bool_refl_again, add_0_0_eq_0])
    except HolError as e:
        print("cross-dep cong  ::", str(e).splitlines()[0])

    # ----------------------------------------------------------------
    # Item 13: function preconditions on Pi / lambda.
    #
    # Build a λ with precondition F = (add 0 0 = 0): under ▷F the body
    # type-checks as 0:nat, so LAMBDA captures F as the binder's
    # precondition. APP to zero_th then requires a thm discharging
    # F[0/n] -- here add_0_0_eq_0 already discharges it (F doesn't
    # mention n, so F[0/n] = F).
    # ----------------------------------------------------------------
    print()
    F = add_0_0_eq_0._concl  # the bool term add 0 0 = 0
    # The body's typing has F in its asl (it does not actually need
    # F to type zero, but we add it to simulate "type-checked under ▷F").
    body_th_under_F = typing_thm([F], zero_th._tm, nat_ty)
    n_for_lam = Var("n", nat_ty)
    lam_with_prec = LAMBDA(n_for_lam, body_th_under_F, precondition=F)
    print("λ with precondition F ::", lam_with_prec)
    # APP without prec: rejected.
    try:
        APP(lam_with_prec, zero_th)
    except HolError as e:
        print("APP no-prec       ::", str(e).splitlines()[0])
    # APP with the wrong proof: rejected.
    try:
        APP(lam_with_prec, zero_th, prec=REFL(zero_th))
    except HolError as e:
        print("APP wrong-prec    ::", str(e).splitlines()[0])
    # APP with the right proof: succeeds, absorbs nothing extra (the
    # axiom add_0_0_eq_0 has empty asl).
    app_with_prec = APP(lam_with_prec, zero_th, prec=add_0_0_eq_0)
    print("APP with prec     ::", app_with_prec)

    # BETA on a preconditioned redex: F must be discharged. The user
    # has two declarative options:
    #   (i) pass prec= a thm proving F;
    #  (ii) leave prec= None when F is already a hypothesis in
    #       redex_th._asl (asl-implicit).
    redex_th = typing_thm([F], Comb(lam_with_prec._tm, n_for_lam), nat_ty)
    # Asl-implicit: F is in redex_th._asl, so no extra prec needed.
    beta_implicit = BETA(redex_th)
    print("BETA asl-implicit ::", beta_implicit)
    # Explicit prec: works too. add_0_0_eq_0 is the axiom |- F.
    beta_with_prec = BETA(redex_th, prec=add_0_0_eq_0)
    print("BETA with prec    ::", beta_with_prec)
    # Wrong prec: rejected.
    try:
        BETA(redex_th, prec=REFL(zero_th))
    except HolError as e:
        print("BETA wrong-prec   ::", str(e).splitlines()[0])
    # When F is in neither asl nor prec: rejected.
    bare_redex_th = typing_thm([], Comb(lam_with_prec._tm, n_for_lam), nat_ty)
    try:
        BETA(bare_redex_th)
    except HolError as e:
        print("BETA no discharge ::", str(e).splitlines()[0])

    # ETA on a preconditioned Pi: the RHS Abs threads F (with binder
    # alpha-renamed if needed); no discharge is required.
    t_prec_var = Var("g", lam_with_prec._ty)
    t_prec_th = VAR(t_prec_var)
    eta_with_prec = ETA(t_prec_th)
    print("ETA with prec     ::", eta_with_prec)

    # MK_COMB on a preconditioned Pi. F = (add 0 0 = 0) is closed in n,
    # so F[l2/n] and F[r2/n] coincide, and a single prec= covers both
    # sides.
    f_eq_th = REFL(LAMBDA(  # f = f at Pi(n:nat|F). nat
        Var("n", nat_ty),
        typing_thm([F], zero_th._tm, nat_ty),
        precondition=F,
    ))
    try:
        MK_COMB(f_eq_th, add_0_0_eq_0)
    except HolError as e:
        print("MK_COMB no-prec   ::", str(e).splitlines()[0])
    # Single thm: covers both sides when F[l2/x] and F[r2/x] coincide.
    mk_comb_prec_single = MK_COMB(f_eq_th, add_0_0_eq_0, prec=add_0_0_eq_0)
    print("MK_COMB prec=thm  ::", mk_comb_prec_single)
    # Tuple form: per-side, each slot is thm | None.
    mk_comb_prec_pair = MK_COMB(
        f_eq_th, add_0_0_eq_0,
        prec=(add_0_0_eq_0, add_0_0_eq_0),
    )
    print("MK_COMB prec=tuple::", mk_comb_prec_pair)
    # Tuple with a None slot mixes explicit (left) with asl-implicit
    # (right). Here F isn't in asl, so it's rejected.
    try:
        MK_COMB(f_eq_th, add_0_0_eq_0, prec=(add_0_0_eq_0, None))
    except HolError as e:
        print("MK_COMB asl-miss  ::", str(e).splitlines()[0])

    # ----------------------------------------------------------------
    # Item 14b.1: constants with declaration-time preconditions.
    #
    # Declare a constant `gated : nat` whose use is gated on F. Without
    # the proof, CONST refuses; with it, CONST emits a typing_thm that
    # absorbs the proof's asl (here empty, since add_0_0_eq_0 is an axiom).
    # ----------------------------------------------------------------
    print()
    new_constant("gated", nat_ty, phi=(Assume(F),))
    try:
        CONST("gated")
    except HolError as e:
        print("CONST no-prec     ::", str(e).splitlines()[0])
    gated_th = CONST("gated", (add_0_0_eq_0,))
    print("CONST with prec   ::", gated_th)

    # The constant's asl tracks the proof's. If we use an assumed
    # version of F (via ASSUME), the asl picks it up.
    F_assumed = ASSUME(typing_thm([], F, bool_ty))
    gated_under_F = CONST("gated", (F_assumed,))
    print("CONST under ▷F    ::", gated_under_F)

    # ----------------------------------------------------------------
    # Item 14b.2: type families with `▷F` in their Φ-context.
    #
    # Declare `pos_vec : (n:nat | n = n) -> tp` -- the obligation
    # `n = n` is trivially provable by REFL, but the kernel still
    # demands the proof at every mk_type call site.
    # ----------------------------------------------------------------
    print()
    n_ctx = Var("n", nat_ty)
    n_self_eq = safe_mk_eq(nat_ty, n_ctx, n_ctx)
    new_type(
        "pos_vec",
        phi=(n_ctx, Assume(n_self_eq)),
        witness=("pos_nil", Tyapp("pos_vec", (), (Const("0", nat_ty),))),
    )

    # mk_type without the Assume proof is rejected.
    try:
        mk_type("pos_vec", [zero_th])
    except HolError as e:
        print("pos_vec missing   ::", str(e).splitlines()[0])

    # With the proof: pos_vec(0) is well-formed.
    proof_0_eq_0 = REFL(zero_th)  # |- 0 = 0 at nat
    pos_vec_0 = mk_type("pos_vec", [zero_th, proof_0_eq_0])
    print("pos_vec(0)        ::", _pp_ty(pos_vec_0))

    # Wrong proof (a different equation) is rejected.
    one_one_eq = REFL(one_th)  # |- (S 0) = (S 0)
    try:
        mk_type("pos_vec", [zero_th, one_one_eq])
    except HolError as e:
        print("pos_vec wrong     ::", str(e).splitlines()[0])

    # TY_CONG_BASE on pos_vec where n varies: the Assume formula
    # `n = n` substitutes differently on the LHS (where n := add 0 0)
    # vs the RHS (where n := 0), and the kernel correctly refuses --
    # this case requires a per-side discharge that the rule doesn't
    # support yet.
    try:
        TY_CONG_BASE("pos_vec", [add_0_0_eq_0, REFL(add00_th)])
    except HolError as e:
        print("pos_vec cong (varying n) ::", str(e).splitlines()[0])

    # Now declare a second family with an *n-independent* Assume
    # obligation. Then LHS and RHS substitutions coincide and
    # TY_CONG_BASE proceeds normally.
    pos_vec2_witness = Tyapp("pos_vec2", (), (Const("0", nat_ty),))
    new_type(
        "pos_vec2",
        phi=(Var("n", nat_ty), Assume(F)),  # F = (add 0 0 = 0)
        witness=("pos_nil2", pos_vec2_witness),
    )
    # mk_type at pos_vec2(0) discharges F via add_0_0_eq_0.
    pv2_zero = mk_type("pos_vec2", [zero_th, add_0_0_eq_0])
    print("pos_vec2(0)              ::", _pp_ty(pv2_zero))
    # Congruence: pos_vec2(add 0 0) == pos_vec2(0), with the same
    # n-free Assume discharge on both sides.
    pos_vec2_cong = TY_CONG_BASE(
        "pos_vec2", [add_0_0_eq_0, add_0_0_eq_0]
    )
    print("pos_vec2 bridge          ::", pos_vec2_cong)

    # ----------------------------------------------------------------
    # Staged term-side declarations: a constant whose Φ includes a Var
    # entry. `inc(n:nat) : nat` carries its term parameter in the Φ
    # rather than being curried via Pi(n:nat). nat. Calling sites use
    # CONST(name, sigma=(...)) to fill in the parameter in one step.
    # ----------------------------------------------------------------
    print()
    n_inc = Var("n", nat_ty)
    new_constant("inc", nat_ty, phi=(n_inc,))
    inc_at_0 = CONST("inc", sigma=(zero_th,))
    print("inc(0) (staged)   ::", inc_at_0)
    inc_at_n = CONST("inc", sigma=(VAR(n_inc),))
    print("inc(n) (free var) ::", inc_at_n)

    # Differ-by-Var-arg: two `inc` constants with different σ-Var-arg
    # are NOT alpha-equal, even though they share name + instantiated ty.
    print("inc(0) tm == inc(n) tm ::",
          _tm_alpha([], inc_at_0._tm, inc_at_n._tm))

    # Φ-staged definition. `dbl(n:nat) := add n n` -- the body mentions
    # the Var-bound n freely; the emitted defining equation is tagged at
    # the Var-binder Φ-application.
    print()
    dbl_body = APP(APP(add_th, VAR(n_inc)), VAR(n_inc))  # |- add n n : nat
    dbl_def = new_basic_definition(
        Var("dbl", nat_ty), dbl_body, phi=(n_inc,)
    )
    print("dbl(n) := add n n ::", dbl_def)

    # Use the staged constant: CONST("dbl", sigma=(zero_th,)) builds
    # `dbl(0) : nat` with term_args=(0,).
    dbl_at_0 = CONST("dbl", sigma=(zero_th,))
    print("dbl(0) (staged)   ::", dbl_at_0)

    # Φ with an Assume entry on a term constant: `gated_inc(n:nat |
    # add 0 0 = 0) : nat`. Discharging the Assume at use site flows
    # through `sigma=(...)`.
    print()
    new_constant(
        "gated_inc", nat_ty, phi=(n_inc, Assume(F))
    )
    gated_inc_at_0 = CONST(
        "gated_inc", sigma=(zero_th, add_0_0_eq_0)
    )
    print("gated_inc(0)      ::", gated_inc_at_0)

    # ----------------------------------------------------------------
    # TM_CONG_BASE: term-side congruence for a staged constant. From
    # add 0 0 = 0 (per-slot Var-arg equation) derive
    #   |- inc(add 0 0) = inc(0)   tagged at nat.
    # The analogue of TY_CONG_BASE for term constants -- the gap that
    # closed the term/type-side symmetry.
    # ----------------------------------------------------------------
    print()
    inc_cong = TM_CONG_BASE("inc", [add_0_0_eq_0])
    print("inc(add 0 0) = inc(0) ::", inc_cong)

    # Multi-slot example: dbl(n) := add n n. TM_CONG_BASE on a Var-only
    # Φ derives dbl(add 0 0) = dbl(0) without going through MK_COMB on
    # the Pi-encoded body.
    dbl_cong = TM_CONG_BASE("dbl", [add_0_0_eq_0])
    print("dbl(add 0 0) = dbl(0) ::", dbl_cong)

    # ----------------------------------------------------------------
    # Staged theorems: (Φ) ▷ F as a first-class shape on axioms.
    #
    # Exercise each slot species: Tyvar (polymorphism), Var (dependent
    # term parameter), Assume (precondition). `interpret(staged, σ)`
    # fans the three discharge axes in one step; THM_CONG_BASE relates
    # two interpretations σ_l / σ_r via per-slot equations.
    # ----------------------------------------------------------------
    print()

    # Polymorphic axiom over a Tyvar slot. Declare a polymorphic
    # `default : Pi(A:tp). A` constant, then state the axiom
    #   (A:tp) ▷ default(A) = default(A)
    # (trivially true, but it exercises the Tyvar slot of new_axiom).
    A_tv = Tyvar("A")
    new_constant("default", A_tv, phi=(A_tv,))
    default_A = CONST("default", (A_tv,))
    eq_A = APP(APP(CONST("=", (A_tv,)), default_A), default_A)
    poly_ax = new_axiom(eq_A, phi=(A_tv,))
    print("poly axiom        ::", poly_ax)
    # Interpret at A := nat: |- default(nat) = default(nat).
    poly_at_nat = interpret(poly_ax, (nat_ty,))
    print("interpret @ nat   ::", poly_at_nat)
    # Interpret at A := bool: |- default(bool) = default(bool).
    poly_at_bool = interpret(poly_ax, (bool_ty,))
    print("interpret @ bool  ::", poly_at_bool)

    # Dependent axiom over an Assume slot. State the conditional
    # axiom (n:nat, ▷ add 0 n = 0) ▷ n = 0. The Assume entry's formula
    # joins the underlying thm's asl; interpret(σ) discharges it via
    # the σ-entry that proves the formula at the chosen n.
    n_eq_form = APP(APP(CONST("=", (nat_ty,)), add_0_n), zero_th)
    inner_eq = APP(APP(CONST("=", (nat_ty,)), VAR(n_var)), zero_th)
    F_assume = Assume(n_eq_form._tm)
    cond_ax = new_axiom(inner_eq, phi=(n_var, F_assume))
    print("cond axiom        ::", cond_ax)
    # Interpret at n := 0 with a proof that add 0 0 = 0 (via add_0_0_eq_0).
    # The Assume formula at n := 0 is `add 0 0 = 0`, which add_0_0_eq_0
    # proves -- so the result discharges the precondition.
    cond_at_0 = interpret(cond_ax, (zero_th, add_0_0_eq_0))
    print("interpret σ = (0, |- add 0 0 = 0) ::", cond_at_0)

    # THM_CONG_BASE: from per-slot equations relate two interpretations
    # of `add_zero` (the staged axiom (n:nat) ▷ add 0 n = n). With the
    # per-slot equation `add 0 0 = 0` on the n slot, derive
    #     |- (add 0 (add 0 0) = add 0 0) = (add 0 0 = 0)     at bool.
    add_zero_cong = THM_CONG_BASE(add_zero, [add_0_0_eq_0])
    print("THM_CONG_BASE     ::", add_zero_cong)

    # Empty Φ (no slots) -- the staged form degenerates to a plain thm.
    triv_ax = new_axiom(
        APP(APP(CONST("=", (nat_ty,)), zero_th), zero_th)
    )
    print("empty-Φ axiom     ::", triv_ax)
    print("interpret ()      ::", interpret(triv_ax, ()))

    # Unified `instantiate` dispatcher: same σ-shape, three J-levels.
    inst_type = instantiate("vec", [zero_th])          # hol_type
    inst_const = instantiate("0", ())                  # typing_thm
    inst_thm = instantiate(add_zero, (zero_th,))       # thm
    print("instantiate vec  ::", _pp_ty(inst_type))
    print("instantiate 0    ::", inst_const)
    print("instantiate axiom::", inst_thm)

    # Rejection paths: shape mismatch (σ arity), wrong slot evidence,
    # and unbound free var in F.
    try:
        interpret(add_zero, ())
    except HolError as e:
        print("interpret wrong arity ::", str(e).splitlines()[0])
    try:
        interpret(add_zero, (nat_ty,))  # Tyvar arg for a Var slot
    except HolError as e:
        print("interpret wrong shape ::", str(e).splitlines()[0])
    try:
        # unbound free var: F has `n` but Φ is empty.
        new_axiom(eq_form)
    except HolError as e:
        print("axiom unbound var     ::", str(e).splitlines()[0])

