# DHOL kernel with typing as derivation
#
# Based on Rothgang/Rabe/Benzmueller, "Dependently-Typed Higher-Order Logic"
# (ACM TOCL, 2025; arXiv:2305.15382). Term well-typedness is itself a
# judgement, not a meta-level function. The kernel exposes four families
# of certificates (all subclasses of `Cert`):
#
#   typing_thm    Gamma |- t : A           (well-typed term)
#   type_eq_thm   Gamma |- A == B          (propositional type equality)
#   thm           Gamma |- F               (validity, as in HOL)
#
# (The earlier `subtype_thm` cert and its rules have been retired; the
# only refinement-related primitives now live at the typing layer as
# RESTRICT / RESTRICT_PROOF / FORGET_TYPING.)
#
# === Trust boundary ===
#
# This module is the trust base. Everything in it -- the Cert subclasses,
# their constructors (the introduction rules), the Φ-walkers, the σ-evidence
# validators, the substitution primitives, and the declaration introducers
# (`new_type`, `new_constant`, `new_axiom`, `new_type_eq_axiom`,
# `new_basic_definition`) -- can affect soundness. A bug
# here can make a wrong sequent provable.
#
# Convenience helpers that do NOT extend trust live one layer up, in
# `basics_dhol.py` alongside the propositional-bridge wrappers:
#
#   instantiate                -- pure router over mk_type / CONST / interpret
#   mk_arrow, mk_subtype       -- thin type constructors (no Cert produced)
#
# Pretty-printers (`_pp_ty`, `_pp_tm`, `_pp_phi`) remain inside this module
# despite being non-trust because they are used in `HolError` messages; the
# choice of formatting cannot make a sequent provable.
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
# TY_CONG_BASE (congBase' in the paper) and Pi-congruence via TY_PI.
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
    """Dependent function type `Πx:A.B`. Pi-domain refinement is
    encoded by giving `bvar` a `Subtype`-typed `ty`:
        Π(x : A|F[x]). B   ≡   Pi(Var("x", Subtype(y:A, F[y/x])), B)
    There is no separate precondition slot -- `Subtype` is the
    canonical refinement type former, used uniformly at every position
    (top-level, codomain, equality index, AND Pi-domain). The
    refinement F becomes available as a hypothesis inside the body via
    `RESTRICT_PROOF` on the bvar's typing certificate."""
    bvar: "Var"
    body: "hol_type"


@dataclass(frozen=True, slots=True)
class Subtype:
    """Predicate subtype `bvar.ty | predicate` -- the refinement of
    `bvar.ty` (the base type A) by the bool predicate `predicate`,
    with `bvar` bound in `predicate`. Inhabitants are exactly those
    a:A for which `predicate[a/bvar]` holds.

    The canonical encoding of Pi-domain refinement: a Pi whose binder
    has type `Subtype(y:A, p)` is the dependent function type over
    `A|p`. Single canonical form -- there is no parallel precondition
    slot on Pi.
    """
    bvar: "Var"
    predicate: "term"


@dataclass(frozen=True, slots=True)
class TyopApp:
    """Application of a Φ-bound rank-1 type operator to term arguments.

    A `TyopApp(name, args)` is a placeholder type, parameterised by the
    `args` terms, that resolves to a concrete `hol_type` when the
    enclosing Φ-substitution supplies a `TypeAbs` for `name`. After
    Φ-resolution no `TyopApp` should remain in a kernel certificate.

    Distinct from `Tyapp`, which represents declared type constants:
    `name` here refers to a Φ-bound `TyopVar` slot, not the `the_decls`
    registry."""
    name: str
    args: tuple             # tuple[term, ...]

    def __post_init__(self):
        if not isinstance(self.args, tuple):
            object.__setattr__(self, "args", tuple(self.args))


hol_type = Tyvar | Tyapp | Pi | Subtype | TyopApp


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


term = Var | Const | Comb | Abs


@dataclass(frozen=True, slots=True)
class Assume:
    """Assumption-entry binder in a type-symbol declaration context
    (paper's `▷F` in a `Φ`-context). Carries a boolean term schema
    that the user must discharge at every mk_type / TY_CONG_BASE call
    site. Unlike Tyvar / Var entries, it does not bind a name in scope
    for later entries -- it is a pure obligation."""
    formula: term


@dataclass(frozen=True, slots=True)
class TyopVar:
    """Φ-slot: a rank-1 type-operator variable with declared term
    parameters. Bound name in scope for later Φ-entries (its applied
    form is `TyopApp(name, args)`). All applications must yield `tp`;
    no type-level lambda, no βη on types.

    `params` is a telescope of `Var` binders interpreted under earlier
    Φ entries; the operator's kind is `(params...) → tp`. The σ-evidence
    is a `TypeAbs` whose bvar types match `params` modulo definitional
    equality."""
    name: str
    params: tuple           # tuple[Var, ...]

    def __post_init__(self):
        if not isinstance(self.params, tuple):
            object.__setattr__(self, "params", tuple(self.params))


@dataclass(frozen=True, slots=True)
class TyEqAssume:
    """Φ-slot asserting a type equality `lhs == rhs`, schematically
    over a binder telescope.

    `binders` is a tuple of `Var`s acting as universally-bound
    placeholders that may appear free in `lhs` / `rhs` (but not in
    later Φ entries). σ-evidence is a `type_eq_thm` whose sides match
    `lhs` / `rhs` (with `binders` carried through as free Vars) and
    whose `_asl` does not mention any binder -- the freshness
    discipline that makes the binders effectively universal.

    The type-equality analogue of `Assume(F)`. With empty binders this
    is a flat type-equality assumption."""
    binders: tuple
    lhs: "hol_type"
    rhs: "hol_type"

    def __post_init__(self):
        if not isinstance(self.binders, tuple):
            object.__setattr__(self, "binders", tuple(self.binders))


@dataclass(frozen=True, slots=True)
class TypeAbs:
    """Meta-level type abstraction `λ(x1:A1, ..., xn:An). body`.

    σ-evidence for a `TyopVar` Φ-slot. The user supplies bvars and a
    body type that may mention them; `_resolve_tyops_in_type` then
    substitutes `TyopApp` arguments for the bvars to recover the
    concrete codomain. Not a `hol_type` -- abstractions only exist as
    σ-evidence at the meta level, in line with item 19's "no type-level
    λ" constraint (the placeholder is consumed at instantiation)."""
    bvars: tuple            # tuple[Var, ...]
    body: "hol_type"

    def __post_init__(self):
        if not isinstance(self.bvars, tuple):
            object.__setattr__(self, "bvars", tuple(self.bvars))


# A Φ-slot is a binder at one of five DHOL judgement levels:
#
#   Tyvar(α)                -- binds at tp           (`Γ ⊢ α : tp`)
#   TyopVar(F, p)           -- binds at (p...)→tp    (rank-1 type op)
#   Var(x, A)               -- binds at term         (`Γ ⊢ x : A`)
#   Assume(F)               -- binds at validity     (`Γ ⊢ F`)
#   TyEqAssume(b, lhs, rhs) -- binds at type-eq      (`Γ ⊢ lhs == rhs`)
#
# The PhiSubst evidence for each slot is the corresponding J-witness:
# hol_type for Tyvar, TypeAbs for TyopVar, typing_thm for Var, thm
# for Assume, type_eq_thm for TyEqAssume. This pointwise mapping is
# what makes `_apply_phi_subst` and `_apply_phi_dual` J-agnostic
# walkers.
Slot = Tyvar | TyopVar | Var | Assume | TyEqAssume


# ---------------------------------------------------------------------------
# Certificates
# ---------------------------------------------------------------------------


# A certificate is `Γ ⊢ J`: a list of bool hypotheses (`_asl`) plus a
# `Judgement` payload `_j` discriminating the J-level. The three named
# cert classes below are marker subclasses of `Cert` -- each just routes
# its constructor signature into the right payload variant. All shared
# behaviour (repr / equality / hashing / `_asl` / payload accessors)
# lives once in `Cert`.
#
# The J-payload variants used as certificates are:
#   JTyping(tm, ty)    -- typing certificate `Γ ⊢ tm : ty`
#   JProp(formula)     -- validity certificate `Γ ⊢ F`
#   JEq(lhs, rhs)      -- type-equality certificate `Γ ⊢ lhs == rhs`
#
# Construction is the same JTyping/JProp/JEq used by `Staged` bodies,
# so `Staged.cert` projects directly into the matching cert subclass
# (`thm` / `type_eq_thm`).


@dataclass(frozen=True, slots=True)
class JTyping:
    """typing-cert payload: `Γ ⊢ tm : ty`. Used in `typing_thm`. Not
    a `Decl.body` (a constant's declared body is `JTm(ty)`; the `tm`
    is filled in at use-site by `CONST`)."""
    tm: term
    ty: hol_type


def _require_kernel_caller(cls_name: str) -> None:
    """Reject direct construction of kernel-private types from outside
    `fusion_dhol`. `Cert` subclasses and `Staged` are introduction-rule
    outputs: their constructors are the kernel's entry points and must
    only be invoked by the kernel itself. External code obtains
    certificates via VAR / CONST / APP / LAMBDA / CONV / REFL / ASSUME /
    ... / new_axiom / interpret.

    Frame layout: _require_kernel_caller is called from inside the
    subclass `__init__`, so frame 2 is the original `typing_thm(...)`
    (or similar) call site."""
    caller = sys._getframe(2).f_globals.get('__name__')
    if caller != __name__:
        raise HolError(
            f"{cls_name}: direct construction is forbidden outside the "
            f"kernel (caller module: {caller!r}). Use the kernel's "
            f"introduction rules to obtain certificates."
        )


class Cert:
    """`[asl] ⊢ judgement` -- the J-agnostic certificate carrier.

    Concrete cert subclasses (`typing_thm`, `type_eq_thm`, `thm`) just
    pick which `Judgement` variant populates `_j`. All representation,
    equality, and per-payload accessor logic is inherited.

    Backward-compat attribute properties (`_tm`, `_ty`, `_concl`,
    `_lhs`, `_rhs`) mirror the pre-refactor per-class field names so
    existing call sites read fields directly off the cert without
    going through `_j`.

    Construction is kernel-private (see `_require_kernel_caller`); the
    subclasses' `__init__`s gate the constructor."""

    __slots__ = ("_asl", "_j")

    def __init__(self, asl, j):
        self._asl = list(asl)
        self._j = j

    def __repr__(self):
        a = ", ".join(_pp_tm(x) for x in self._asl)
        j = self._j
        if isinstance(j, JTyping):
            return f"[{a}] |- {_pp_tm(j.tm)} : {_pp_ty(j.ty)}"
        if isinstance(j, JEq):
            return f"[{a}] |- {_pp_ty(j.lhs)} == {_pp_ty(j.rhs)}"
        if isinstance(j, JProp):
            return f"Sequent([{a}], {_pp_tm(j.formula)})"
        return f"Cert([{a}], {j!r})"

    def __eq__(self, other):
        return (
            isinstance(other, Cert)
            and type(self) is type(other)
            and self._asl == other._asl
            and self._j == other._j
        )

    def __hash__(self):
        return hash((type(self), tuple(self._asl), self._j))

    # Backward-compat field accessors -- raise AttributeError when the
    # payload doesn't carry the requested field (matching the old
    # per-class __slots__ behaviour).
    @property
    def _tm(self):
        if isinstance(self._j, JTyping):
            return self._j.tm
        raise AttributeError("_tm")

    @property
    def _ty(self):
        if isinstance(self._j, JTyping):
            return self._j.ty
        raise AttributeError("_ty")

    @property
    def _concl(self):
        if isinstance(self._j, JProp):
            return self._j.formula
        raise AttributeError("_concl")

    @property
    def _lhs(self):
        if isinstance(self._j, JEq):
            return self._j.lhs
        raise AttributeError("_lhs")

    @property
    def _rhs(self):
        if isinstance(self._j, JEq):
            return self._j.rhs
        raise AttributeError("_rhs")


class typing_thm(Cert):
    """Gamma |- t : A."""
    __slots__ = ()

    def __init__(self, asl, tm, ty):
        _require_kernel_caller("typing_thm")
        super().__init__(asl, JTyping(tm, ty))


class type_eq_thm(Cert):
    """Gamma |- A == B."""
    __slots__ = ()

    def __init__(self, asl, lhs, rhs):
        _require_kernel_caller("type_eq_thm")
        super().__init__(asl, JEq(lhs, rhs))


class thm(Cert):
    """Gamma |- F  (boolean validity)."""
    __slots__ = ()

    def __init__(self, asl, concl):
        _require_kernel_caller("thm")
        super().__init__(asl, JProp(concl))


class Staged:
    """(Φ) ▷ body  -- a relational judgement parameterised over a
    Φ-telescope. body is one of `JProp(F)` or `JEq(L, R)`, and
    discriminates which concrete certificate `interpret(staged, σ)`
    produces (`thm` or `type_eq_thm` respectively).

    The asl-as-Assume-formulas view is reconstructed by `_phi_asl(phi)`
    when the projected certificate is needed (e.g. for printing).

    Use `interpret(staged, σ)` to instantiate; σ matches Φ pointwise
    (hol_type for Tyvar, typing_thm for Var, thm for Assume, etc),
    validated by the same `_apply_phi_subst` walker used by `mk_type`
    and `CONST`."""

    __slots__ = ("_phi", "_body")

    def __init__(self, phi, body):
        _require_kernel_caller("Staged")
        if not isinstance(body, (JProp, JEq)):
            raise HolError(
                "Staged: body must be a JProp or JEq (got "
                f"{type(body).__name__})"
            )
        self._phi = tuple(phi)
        self._body = body

    @property
    def cert(self):
        """Projected certificate view, dispatched on body shape."""
        asl = _phi_asl(self._phi)
        b = self._body
        if isinstance(b, JProp):
            return thm(asl, b.formula)
        if isinstance(b, JEq):
            return type_eq_thm(asl, b.lhs, b.rhs)
        raise HolError(f"Staged.cert: unknown body {type(b).__name__}")

    def __repr__(self):
        projected = self.cert
        if not self._phi:
            return repr(projected)
        return f"({_pp_phi(self._phi)}) ▷ {projected!r}"


# Backward-compatibility aliases for the old per-J Staged classes.
# basics_dhol.py uses `StagedThm` as a return-type annotation; the
# union behaviour is now carried by the body discriminator.
StagedThm = Staged
StagedTypeEq = Staged


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
        elif isinstance(e, TyopVar):
            params = ", ".join(f"{p.name}:{_pp_ty(p.ty)}" for p in e.params)
            parts.append(f"{e.name}:({params})→tp" if params else f"{e.name}:tp")
        elif isinstance(e, Var):
            parts.append(f"{e.name}:{_pp_ty(e.ty)}")
        elif isinstance(e, Assume):
            parts.append(f"▷{_pp_tm(e.formula)}")
        elif isinstance(e, TyEqAssume):
            bvs = ", ".join(f"{b.name}:{_pp_ty(b.ty)}" for b in e.binders)
            sig = f" ⟨{bvs}⟩" if bvs else ""
            parts.append(f"▷{sig} {_pp_ty(e.lhs)} == {_pp_ty(e.rhs)}")
        else:
            parts.append(repr(e))
    return ", ".join(parts)


# ---------------------------------------------------------------------------
# Declarations and the Judgement ADT
#
# The Judgement ADT is the single sort of the DHOL GAT: each variant
# carries the payload of one judgement level.
#
#   JTp                       Γ; Φ ⊢ name(Φ) : tp     (decl-body only)
#   JTm(ty)                   Γ; Φ ⊢ name(Φ) : ty     (decl-body only)
#   JTyping(tm, ty)           Γ ⊢ tm : ty             (cert-payload only)
#   JProp(formula)            (Φ) ▷ F                 (decl-body + cert)
#   JEq(lhs, rhs)             (Φ) ▷ A == B            (decl-body + cert)
#
# Named declarations (JTp / JTm bodies) live in the unified `the_decls`
# registry as `Decl(name, phi, body)`; relational bodies (JProp / JEq)
# are anonymous and travel as `Staged(phi, body)`. The same variants
# populate `Cert._j` for the projected certificate -- one Judgement
# ADT, two roles. `JTyping` only appears as a cert payload:
# named-constant declarations use `JTm(ty)` (the schema), and the `tm`
# is constructed at instantiation time by `CONST`.
#
# Each Decl's Φ is an ordered telescope of Slot binders (Tyvar /
# TyopVar / Var / Assume / TyEqAssume); later entries may reference
# earlier ones. The flat-arity case is recovered by an empty Φ; rank-1
# polymorphism alone by a Φ of Tyvars; the dependent-parameter case by
# a Φ of Vars.
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class JTp:
    """tp-level body: `name(Φ) : tp`. Carries no body data of its own.
    Following Rabe 2026, declared types are not required to be inhabited;
    `∀x:A. F ⇒ ∃x:A. F` is correspondingly not a theorem. A theory that
    wants `A` non-empty registers an inhabitant via a separate
    `new_constant` call."""


@dataclass(frozen=True, slots=True)
class JTm:
    """term-level body: `name(Φ) : ty`."""
    ty: hol_type


@dataclass(frozen=True, slots=True)
class JProp:
    """prop-level body: validity body `F : bool`. The Φ-Assume binders
    carry F's hypotheses implicitly -- the projection-as-thm view of
    a staged prop reconstructs them via `_phi_asl(phi)`."""
    formula: term


@dataclass(frozen=True, slots=True)
class JEq:
    """type-equality-level body: `(Φ) ▷ lhs == rhs`. Φ-TyEqAssume
    binders carry the type-equality hypotheses; the projection-as-
    type_eq_thm view reconstructs the bool-side asl via `_phi_asl(phi)`
    (TyEqAssume entries contribute no bool asl)."""
    lhs: hol_type
    rhs: hol_type


Judgement = JTp | JTm | JTyping | JProp | JEq


@dataclass(frozen=True, slots=True)
class Decl:
    """A named staged declaration: `name(Φ)` with a Judgement body.

    Φ is a tuple of Slot binders, interpreted sequentially. Only the
    named-declaration levels appear here:
      * JTp        -- name(Φ) : tp
      * JTm(ty)    -- name(Φ) : ty
    The relational levels (JProp / JEq) are anonymous and live in
    `Staged`, not in `the_decls`.
    """
    name: str
    phi: tuple
    body: Judgement


# Insertion order = declaration order; newer entries shadow older ones
# in iteration, mirroring HOL Light's "latest first" discipline (and
# the previous insert(0, ...) lists). Lookup is direct via dict[name].
the_decls: dict = {"bool": Decl("bool", (), JTp())}


def get_type_kind(s: str) -> tuple:
    """Return the declared Φ-telescope of a type symbol."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, JTp):
        raise KeyError(s)
    return d.phi


def new_type(name: str, phi: tuple = ()) -> None:
    """Declares a new type constant `name(Φ) : tp`.

    `phi` is a Φ-telescope of `Tyvar | Var | Assume` binders. Same
    vocabulary as on term constants -- later entries may reference
    earlier ones (rank-1 polymorphism interleaved with dependent term
    params and assumption obligations).

    Per Rabe 2026, declared types are not required to be inhabited; a
    theory that wants `name` to be non-empty registers an inhabitant
    via a separate `new_constant` call.

    `bool` is the sole exception: it's the kernel's primitive type and
    requires no user call to new_type.
    """
    if name in the_decls:
        raise HolError(f"new_type: type {name} has already been declared")
    _check_phi(phi, f"new_type({name})")
    if any(isinstance(b, TyopVar) for b in phi):
        raise HolError(
            f"new_type({name}): TyopVar in Φ unsupported -- a declared "
            f"`Tyapp` carries Tyvar/Var-slot σ choices in type_args / "
            f"term_args but has no room to record the chosen TypeAbs. "
            f"TyopVar is only available in `new_axiom` / `new_constant` "
            f"telescopes, where σ is consumed at use site."
        )
    the_decls[name] = Decl(name, tuple(phi), JTp())


bool_ty: hol_type = Tyapp("bool", (), ())
aty: hol_type = Tyvar("A")


def _seed_constant(name: str, phi: tuple, ty: hol_type) -> None:
    the_decls[name] = Decl(name, phi, JTm(ty))


# Seed the registry with the one kernel-primitive term constant:
#   = : (A:tp) → Pi(_:A). Pi(_:A). bool
#
# Implication (==>), T, /\, !, ?, etc. are derived in basics_dhol.py.
_seed_constant(
    "=",
    (Tyvar("A"),),
    Pi(Var("_", aty), Pi(Var("_", aty), bool_ty)),
)


def get_const_phi(s: str) -> tuple:
    """Return the declared Φ-telescope of a term constant."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, JTm):
        raise KeyError(s)
    return d.phi


def get_const_type(s: str) -> hol_type:
    """Return the constant's declared body type (well-formed under Φ)."""
    d = the_decls.get(s)
    if d is None or not isinstance(d.body, JTm):
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
    the_decls[name] = Decl(name, phi, JTm(ty))


def _check_assume_proof(arg, formula: term, theta_ty: list,
                        theta_tm: list, ctx: str,
                        tyop_theta: list | None = None) -> term:
    """Validate that `arg` is a `thm` whose conclusion alpha-matches
    `formula` after applying the term substitution `theta_tm`, the
    type substitution `theta_ty`, and (when supplied) the rank-1
    tyop substitution `tyop_theta`. Returns the substituted `formula`
    (`needed`); the caller decides what to do with `arg._asl`."""
    if not isinstance(arg, thm):
        raise HolError(f"{ctx}: argument for Assume binder must be a thm")
    needed = _subst_full_term(theta_ty, theta_tm, tyop_theta or [], formula)
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
    """Light syntactic check: every entry is a Tyvar, TyopVar, Var,
    Assume, or TyEqAssume. Well-formedness of binder annotations under
    earlier entries is the caller's responsibility (honest-caller
    perimeter, mirroring how `new_type` accepts raw `Var(x, A)` without
    re-checking A)."""
    for entry in phi:
        if not isinstance(
            entry, (Tyvar, TyopVar, Var, Assume, TyEqAssume)
        ):
            raise HolError(
                f"{ctx}: context entries must be Tyvar, TyopVar, Var, "
                f"Assume, or TyEqAssume (got {entry!r})"
            )


class PhiSubstResult(NamedTuple):
    """Output of `_apply_phi_subst`. Fields:
      theta_ty:   list of (chosen_hol_type, Tyvar) -- type substitution
      theta_tm:   list of (chosen_term, Var)        -- term substitution
      tyop_theta: list of (TypeAbs, name)           -- tyop substitution
      term_args:  chosen terms for Var entries (declaration order)
      asl_extra:  assumptions absorbed from Var-typings + Assume-proofs"""
    theta_ty: list
    theta_tm: list
    tyop_theta: list
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
    out = PhiSubstResult(
        theta_ty=[], theta_tm=[], tyop_theta=[],
        term_args=[], asl_extra=[],
    )
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
    # `new_type` rejects TyopVar slots, so tyop_theta is necessarily
    # empty here -- the Tyapp's type_args / term_args have no place for
    # TypeAbs evidence.
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
        return [v for v in frees(tm.body) if v != tm.bvar]
    if isinstance(tm, Comb):
        return _uniq_extend(list(frees(tm.fun)), frees(tm.arg))
    raise HolError("frees: ill-formed term")


def frees_in_type(ty: hol_type) -> list:
    """Free term variables occurring in a type (Tyapp term_args, a
    Subtype's predicate, or a Pi's precondition). Used by refinement
    rules (RESTRICT / RESTRICT_PROOF / FORGET_TYPING) that need to know
    which term variables a refined type mentions."""
    if isinstance(ty, Tyvar):
        return []
    if isinstance(ty, Tyapp):
        seen: list = []
        for a in ty.type_args:
            _uniq_extend(seen, frees_in_type(a))
        for a in ty.term_args:
            _uniq_extend(seen, frees(a))
        return seen
    if isinstance(ty, Pi):
        seen = _uniq_extend(
            list(frees_in_type(ty.bvar.ty)),
            (v for v in frees_in_type(ty.body) if v != ty.bvar),
        )
        return seen
    if isinstance(ty, Subtype):
        seen = list(frees_in_type(ty.bvar.ty))
        _uniq_extend(seen, (v for v in frees(ty.predicate) if v != ty.bvar))
        return seen
    if isinstance(ty, TyopApp):
        seen = []
        for a in ty.args:
            _uniq_extend(seen, frees(a))
        return seen
    raise HolError("frees_in_type: ill-formed type")


def freesin(acc: list, tm: term) -> bool:
    if isinstance(tm, Var):
        return tm in acc
    if isinstance(tm, Const):
        return all(freesin(acc, a) for a in tm.term_args)
    if isinstance(tm, Abs):
        return freesin([tm.bvar, *acc], tm.body)
    if isinstance(tm, Comb):
        return freesin(acc, tm.fun) and freesin(acc, tm.arg)
    raise HolError("freesin: ill-formed term")


def vfree_in(v: term, tm: term) -> bool:
    if isinstance(tm, Abs):
        if v == tm.bvar:
            return False
        return vfree_in(v, tm.body)
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
        return _uniq_extend(list(tyvars(ty.bvar.ty)), tyvars(ty.body))
    if isinstance(ty, Subtype):
        return _uniq_extend(
            list(tyvars(ty.bvar.ty)), type_vars_in_term(ty.predicate)
        )
    if isinstance(ty, TyopApp):
        seen = []
        for a in ty.args:
            _uniq_extend(seen, type_vars_in_term(a))
        return seen
    raise HolError("tyvars: ill-formed type")


def tyop_names_in_type(ty: hol_type) -> list:
    """Names of all `TyopApp`s appearing in `ty` (in first-appearance
    order). A TyopApp's `name` is a Φ-bound TyopVar reference."""
    if isinstance(ty, Tyvar):
        return []
    if isinstance(ty, Tyapp):
        seen: list = []
        for a in ty.type_args:
            _uniq_extend(seen, tyop_names_in_type(a))
        for a in ty.term_args:
            _uniq_extend(seen, tyop_names_in_term(a))
        return seen
    if isinstance(ty, Pi):
        return _uniq_extend(
            list(tyop_names_in_type(ty.bvar.ty)),
            tyop_names_in_type(ty.body),
        )
    if isinstance(ty, Subtype):
        return _uniq_extend(
            list(tyop_names_in_type(ty.bvar.ty)),
            tyop_names_in_term(ty.predicate),
        )
    if isinstance(ty, TyopApp):
        seen = [ty.name]
        for a in ty.args:
            _uniq_extend(seen, tyop_names_in_term(a))
        return seen
    raise HolError("tyop_names_in_type: ill-formed type")


def tyop_names_in_term(tm: term) -> list:
    if isinstance(tm, Var):
        return tyop_names_in_type(tm.ty)
    if isinstance(tm, Const):
        seen = list(tyop_names_in_type(tm.ty))
        for a in tm.term_args:
            _uniq_extend(seen, tyop_names_in_term(a))
        return seen
    if isinstance(tm, Comb):
        return _uniq_extend(
            list(tyop_names_in_term(tm.fun)),
            tyop_names_in_term(tm.arg),
        )
    if isinstance(tm, Abs):
        return _uniq_extend(
            list(tyop_names_in_type(tm.bvar.ty)),
            tyop_names_in_term(tm.body),
        )
    raise HolError("tyop_names_in_term: ill-formed term")


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
        return _uniq_extend(
            list(tyvars(tm.bvar.ty)), type_vars_in_term(tm.body)
        )
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
        return _ty_eq(env2, t1.body, t2.body)
    if isinstance(t1, Subtype) and isinstance(t2, Subtype):
        if not _ty_eq(env, t1.bvar.ty, t2.bvar.ty):
            return False
        env2 = [(t1.bvar, t2.bvar), *env]
        return _tm_alpha(env2, t1.predicate, t2.predicate)
    if isinstance(t1, TyopApp) and isinstance(t2, TyopApp):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return False
        return all(_tm_alpha(env, a, b) for a, b in zip(t1.args, t2.args))
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
        return _tm_alpha(env2, a.body, b.body)
    return False


# ---------------------------------------------------------------------------
# Term substitution into types (capture avoiding)
# ---------------------------------------------------------------------------


def _map_type(f_ty: Callable, f_tm: Callable, ty: hol_type) -> hol_type:
    """Identity-walk over a hol_type, mapping nested types via `f_ty`
    and nested terms via `f_tm`. Returns `ty` unchanged if every
    sub-result is the same object as its source (the existing
    substitutors all rely on this aliasing optimisation, so the
    walker preserves it).

    Used by `subst_in_type`, `type_subst`, `_resolve_tyops_in_type`,
    and (for its non-binder cases) `_inst_in_term`."""
    if isinstance(ty, Tyvar):
        return ty
    if isinstance(ty, Tyapp):
        new_t = tuple(f_ty(a) for a in ty.type_args)
        new_m = tuple(f_tm(a) for a in ty.term_args)
        if all(n is o for n, o in zip(new_t, ty.type_args)) and \
           all(n is o for n, o in zip(new_m, ty.term_args)):
            return ty
        return Tyapp(ty.tyop, new_t, new_m)
    if isinstance(ty, Pi):
        new_bv_ty = f_ty(ty.bvar.ty)
        new_bv = (
            ty.bvar if new_bv_ty is ty.bvar.ty
            else Var(ty.bvar.name, new_bv_ty)
        )
        new_body = f_ty(ty.body)
        if new_bv is ty.bvar and new_body is ty.body:
            return ty
        return Pi(new_bv, new_body)
    if isinstance(ty, Subtype):
        new_bv_ty = f_ty(ty.bvar.ty)
        new_bv = (
            ty.bvar if new_bv_ty is ty.bvar.ty
            else Var(ty.bvar.name, new_bv_ty)
        )
        new_pred = f_tm(ty.predicate)
        if new_bv is ty.bvar and new_pred is ty.predicate:
            return ty
        return Subtype(new_bv, new_pred)
    if isinstance(ty, TyopApp):
        new_args = tuple(f_tm(a) for a in ty.args)
        if all(n is o for n, o in zip(new_args, ty.args)):
            return ty
        return TyopApp(ty.name, new_args)
    raise HolError("_map_type: ill-formed type")


def _map_term(f_ty: Callable, f_tm: Callable, tm) -> term:
    """Identity-walk over a term, mapping nested types via `f_ty`
    and nested terms via `f_tm`. Identity-aliasing-preserving, like
    `_map_type`. Used by `_vsubst`, `_resolve_tyops_in_term`, and
    `_inst_in_term` for their non-Abs / non-Var-leaf cases (each
    overrides only the cases where it differs from a plain identity
    walk)."""
    if isinstance(tm, Var):
        new_ty = f_ty(tm.ty)
        return tm if new_ty is tm.ty else Var(tm.name, new_ty)
    if isinstance(tm, Const):
        new_ty = f_ty(tm.ty)
        new_args = tuple(f_tm(a) for a in tm.term_args)
        if new_ty is tm.ty and all(
            n is o for n, o in zip(new_args, tm.term_args)
        ):
            return tm
        return Const(tm.name, new_ty, new_args)
    if isinstance(tm, Comb):
        f2 = f_tm(tm.fun)
        a2 = f_tm(tm.arg)
        if f2 is tm.fun and a2 is tm.arg:
            return tm
        return Comb(f2, a2)
    if isinstance(tm, Abs):
        new_bv_ty = f_ty(tm.bvar.ty)
        new_bv = (
            tm.bvar if new_bv_ty is tm.bvar.ty
            else Var(tm.bvar.name, new_bv_ty)
        )
        new_body = f_tm(tm.body)
        if new_bv is tm.bvar and new_body is tm.body:
            return tm
        return Abs(new_bv, new_body)
    raise HolError("_map_term: ill-formed term")


def _subst_binder(theta: list, bvar: Var, body,
                  subst_body, free_in_body, ctor):
    """Capture-avoiding substitution under a binder, shared between
    `subst_in_type` (Pi: body is hol_type), `_vsubst` (Abs: body is
    term), and the Subtype case (predicate is term). `subst_body`
    recurses into `body`; `free_in_body` is the free-occurrence
    predicate matching `body`'s shape; `ctor` builds the result binder."""
    theta2 = [(t, x) for t, x in theta if x != bvar]
    new_bvar_ty = subst_in_type(theta, bvar.ty)
    new_bvar = (
        bvar if new_bvar_ty is bvar.ty
        else Var(bvar.name, new_bvar_ty)
    )
    if not theta2:
        return ctor(new_bvar, body)
    if any(vfree_in(new_bvar, t) and free_in_body(x, body) for t, x in theta2):
        avoid = [subst_body(theta2, body)]
        fresh = variant(avoid, new_bvar)
        rename = [(fresh, bvar), *theta2]
        return ctor(fresh, subst_body(rename, body))
    return ctor(new_bvar, subst_body(theta2, body))


def subst_in_type(theta: list, ty: hol_type) -> hol_type:
    if not theta:
        return ty
    if isinstance(ty, Pi):
        return _subst_binder(
            theta, ty.bvar, ty.body,
            subst_in_type, _occurs_in_type, Pi,
        )
    if isinstance(ty, Subtype):
        return _subst_binder(
            theta, ty.bvar, ty.predicate,
            _vsubst, vfree_in, Subtype,
        )
    return _map_type(
        lambda x: subst_in_type(theta, x),
        lambda x: _vsubst(theta, x),
        ty,
    )


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
        return (
            _occurs_in_type(v, ty.bvar.ty)
            or _occurs_in_type(v, ty.body)
        )
    if isinstance(ty, Subtype):
        if ty.bvar == v:
            return _occurs_in_type(v, ty.bvar.ty)
        return _occurs_in_type(v, ty.bvar.ty) or vfree_in(v, ty.predicate)
    if isinstance(ty, TyopApp):
        return any(vfree_in(v, a) for a in ty.args)
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
    return _map_type(
        lambda x: type_subst(i, x),
        lambda x: _inst_in_term(i, x),
        ty,
    )


def _inst_in_term(tyin: list, tm: term) -> term:
    """Type-variable instantiation, propagated into every type
    annotation. Capture-avoiding under Abs: at each binder, the
    renamed bvar2 is checked against the type-instantiated free
    variables of the body upfront, and the binder is alpha-renamed
    via `variant` if (and only if) a collision exists. Non-binder
    cases delegate to `_map_term` for the structural walk."""
    if not tyin:
        return tm
    if isinstance(tm, Abs):
        bvar2 = Var(tm.bvar.name, type_subst(tyin, tm.bvar.ty))
        body_free_subst = [
            _inst_in_term(tyin, v) for v in frees(tm.body) if v != tm.bvar
        ]
        fresh_bvar = variant(body_free_subst, bvar2)
        if fresh_bvar != bvar2:
            # Renaming the binder dodges the collision; retry the walk
            # on the renamed Abs so the inner pre-scan runs over the
            # alpha-renamed body.
            z = Var(fresh_bvar.name, tm.bvar.ty)
            return _inst_in_term(
                tyin, Abs(z, _vsubst([(z, tm.bvar)], tm.body))
            )
        body2 = _inst_in_term(tyin, tm.body)
        if bvar2 is tm.bvar and body2 is tm.body:
            return tm
        return Abs(bvar2, body2)
    return _map_term(
        lambda x: type_subst(tyin, x),
        lambda x: _inst_in_term(tyin, x),
        tm,
    )


# ---------------------------------------------------------------------------
# Rank-1 type-operator resolution
#
# A `tyop_theta` is a list of (TypeAbs, name) pairs, one per TyopVar
# slot in the consumed Φ. The walkers below replace every
# `TyopApp(name, args)` whose name is bound in `tyop_theta` with the
# corresponding `TypeAbs.body` after substituting `args` for the
# TypeAbs's bvars. After resolution no `TyopApp` referring to a name
# in `tyop_theta` should remain in the result; references to other
# names (e.g. outer-scope TyopVars in a nested staging) are left
# alone, matching the way `_inst_in_term` leaves unbound `Tyvar`s
# alone.
# ---------------------------------------------------------------------------


def _resolve_tyops_in_type(tyop_theta: list, ty: hol_type) -> hol_type:
    if not tyop_theta:
        return ty
    if isinstance(ty, TyopApp):
        new_args = tuple(
            _resolve_tyops_in_term(tyop_theta, a) for a in ty.args
        )
        for typeabs, F_name in tyop_theta:
            if F_name == ty.name:
                if len(typeabs.bvars) != len(new_args):
                    raise HolError(
                        f"_resolve_tyops_in_type: arity mismatch for "
                        f"{ty.name} (got {len(new_args)}, "
                        f"expected {len(typeabs.bvars)})"
                    )
                sub = list(zip(new_args, typeabs.bvars))
                return _resolve_tyops_in_type(
                    tyop_theta, subst_in_type(sub, typeabs.body)
                )
        if all(n is o for n, o in zip(new_args, ty.args)):
            return ty
        return TyopApp(ty.name, new_args)
    return _map_type(
        lambda x: _resolve_tyops_in_type(tyop_theta, x),
        lambda x: _resolve_tyops_in_term(tyop_theta, x),
        ty,
    )


def _resolve_tyops_in_term(tyop_theta: list, tm: term) -> term:
    if not tyop_theta:
        return tm
    return _map_term(
        lambda x: _resolve_tyops_in_type(tyop_theta, x),
        lambda x: _resolve_tyops_in_term(tyop_theta, x),
        tm,
    )


# ---------------------------------------------------------------------------
# Composite Φ-substitution shortcuts
#
# Every Φ-walker accumulates three substitutions in lockstep:
#   theta_ty    -- Tyvar → hol_type    (from Tyvar slots)
#   theta_tm    -- Var   → term        (from Var slots)
#   tyop_theta  -- TyopVar → TypeAbs   (from TyopVar slots)
#
# Applying these to an expected schema (Var-typing, Assume formula,
# TyEqAssume side, TypeAbs param, …) always uses the same composition.
# These two helpers capture it once.
# ---------------------------------------------------------------------------


def _subst_full_type(theta_ty, theta_tm, tyop_theta, ty: hol_type) -> hol_type:
    """Apply (theta_tm, theta_ty, tyop_theta) to `ty` in the canonical
    order: Var → term, then Tyvar → hol_type, then TyopVar → TypeAbs."""
    return _resolve_tyops_in_type(
        tyop_theta, type_subst(theta_ty, subst_in_type(theta_tm, ty)),
    )


def _subst_full_term(theta_ty, theta_tm, tyop_theta, tm: term) -> term:
    """Apply (theta_tm, theta_ty, tyop_theta) to `tm` in the canonical
    order: Var → term, then Tyvar → hol_type, then TyopVar → TypeAbs."""
    return _resolve_tyops_in_term(
        tyop_theta, _inst_in_term(theta_ty, _vsubst(theta_tm, tm)),
    )


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
    if isinstance(tm, Abs):
        return _subst_binder(
            ilist, tm.bvar, tm.body,
            _vsubst, vfree_in, Abs,
        )
    return _map_term(
        lambda x: subst_in_type(ilist, x),
        lambda x: _vsubst(ilist, x),
        tm,
    )


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
        return (
            f"(Pi {ty.bvar.name}:{_pp_ty_raw(ty.bvar.ty)}. "
            f"{_pp_ty_raw(ty.body)})"
        )
    if isinstance(ty, Subtype):
        return (
            f"({_pp_ty_raw(ty.bvar.ty)}|"
            f"\\{ty.bvar.name}. {_pp_tm_raw(ty.predicate)})"
        )
    if isinstance(ty, TyopApp):
        if not ty.args:
            return ty.name
        return f"{ty.name}({', '.join(_pp_tm_raw(a) for a in ty.args)})"
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
        return (
            f"(\\{tm.bvar.name}:{_pp_ty_raw(tm.bvar.ty)}. "
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
    inst_ty = _resolve_tyops_in_type(result.tyop_theta, inst_ty)
    return typing_thm(
        result.asl_extra,
        Const(name, inst_ty, tuple(result.term_args)),
        inst_ty,
    )


def APP(f_th: typing_thm, a_th: typing_thm) -> typing_thm:
    """appl':  Gamma |- f : Pi(x:A). B   Gamma |- a : A
              ---------------------------------------------
                      Gamma |- f a : B[a/x]

    Homogeneous form: a_th._ty must definitionally match f's domain.
    For a propositional bridge A == A', pre-CONV the argument
    (basics_dhol exposes an APP wrapper that does this automatically).

    Preconditioned domains are encoded as Subtype-typed bvars:
    `Pi(x : Subtype(y:A, p)). B`. The argument must already inhabit
    the refined type `A|p` -- discharge of `p[a]` happens upstream
    when the caller constructs `a : A|p` via `RESTRICT`."""
    f_ty = f_th._ty
    if not isinstance(f_ty, Pi):
        raise HolError(f"APP: head not a Pi -- got {_pp_ty(f_ty)}")
    expected = f_ty.bvar.ty
    got = a_th._ty
    if not type_eq(expected, got):
        raise HolError(
            f"APP: domain mismatch -- expected {_pp_ty(expected)}, "
            f"got {_pp_ty(got)} (pre-CONV the argument to bridge)"
        )
    asl = term_union(f_th._asl, a_th._asl)
    result_ty = subst_in_type([(a_th._tm, f_ty.bvar)], f_ty.body)
    return typing_thm(asl, Comb(f_th._tm, a_th._tm), result_ty)


def LAMBDA(v: Var, body_th: typing_thm) -> typing_thm:
    """lambda':  Gamma, x:A |- t : B
                ----------------------------
                Gamma |- (\\x:A. t) : Pi(x:A). B

    Preconditioned abstractions are now encoded as ordinary lambdas
    whose binder type is a Subtype: `λx:A|p. t` is `LAMBDA(Var("x",
    Subtype(y:A, p)), t_th)`. The discharge of `p[x]` happens at the
    point where the binder is first introduced (the user's typing
    discipline / RESTRICT calls upstream); LAMBDA itself just abstracts."""
    asl = [a for a in body_th._asl if not vfree_in(v, a)]
    return typing_thm(
        asl,
        Abs(v, body_th._tm),
        Pi(v, body_th._ty),
    )


def CONV(t_th: typing_thm, eq: type_eq_thm) -> typing_thm:
    """Admissible conversion rule: Gamma |- t : A   Gamma |- A == B
                                    -------------------------------
                                          Gamma |- t : B"""
    asl = term_union(t_th._asl, eq._asl)
    return typing_thm(asl, t_th._tm, _other_side(eq, t_th._ty, "CONV"))


# ---------------------------------------------------------------------------
# Typing reconstruction: recover a typing_thm from a term or thm.
#
# DHOL's typing-as-derivation discipline taxes derived rules: any
# derived rule that invokes REFL on a sub-expression has to thread a
# typing certificate for that sub-expression, and those threads
# compound through theory layers. These constructors eliminate the tax
# by re-deriving the typing from the term's intrinsic annotations.
#
# Sound because DHOL terms carry their types intrinsically on Var,
# Const, and Abs.bvar -- a structural walk of a well-formed term
# yields its type without ambiguity. TYPE_OF fails on Comb-nodes
# whose argument's intrinsic type doesn't match the function's
# domain (terms typed via a propositional CONV bridge upstream); use
# the equation-side accessors instead for those.
# ---------------------------------------------------------------------------


def _walk_type(tm: term) -> hol_type:
    if isinstance(tm, Var):
        return tm.ty
    if isinstance(tm, Const):
        return tm.ty
    if isinstance(tm, Comb):
        f_ty = _walk_type(tm.fun)
        a_ty = _walk_type(tm.arg)
        if not isinstance(f_ty, Pi):
            raise HolError(
                f"TYPE_OF: function position has non-Pi type "
                f"{_pp_ty(f_ty)}"
            )
        if not type_eq(f_ty.bvar.ty, a_ty):
            raise HolError(
                f"TYPE_OF: domain mismatch (expected {_pp_ty(f_ty.bvar.ty)}, "
                f"got {_pp_ty(a_ty)}); term was typed via a propositional "
                f"bridge that TYPE_OF can't see -- use the equation-side "
                f"accessors instead"
            )
        return subst_in_type([(tm.arg, f_ty.bvar)], f_ty.body)
    if isinstance(tm, Abs):
        body_ty = _walk_type(tm.body)
        return Pi(tm.bvar, body_ty)
    raise HolError(f"TYPE_OF: unrecognised term shape {type(tm).__name__}")


def TYPE_OF(asl: list, tm: term) -> typing_thm:
    """Reconstruct `[asl] |- tm : ty` by walking tm's intrinsic
    annotations. The walk re-derives the same type the kernel's
    typing rules would have produced for a term with no propositional
    bridges."""
    return typing_thm(asl, tm, _walk_type(tm))


def LHS_TYPING(th: thm) -> typing_thm:
    """`th : asl |- a = b at A`  →  `[asl] |- a : A`. Inherits th's asl
    and reads the equation's tag off the `=` constant."""
    _require_eq(th._concl, "LHS_TYPING")
    return typing_thm(th._asl, _lhs(th._concl), _eq_tag(th._concl))


def RHS_TYPING(th: thm) -> typing_thm:
    """`th : asl |- a = b at A`  →  `[asl] |- b : A`."""
    _require_eq(th._concl, "RHS_TYPING")
    return typing_thm(th._asl, _rhs(th._concl), _eq_tag(th._concl))


def CONCL_TYPING(th: thm) -> typing_thm:
    """`th : asl |- F`  →  `[] |- F : bool`. Every thm's conclusion is a
    bool by kernel invariant. The typing is unconditional (bool is a
    closed concrete type with no dependencies), so the asl is empty --
    threading th's asl here would leak hypotheses into INST consumers."""
    return typing_thm([], th._concl, bool_ty)


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


# ---------------------------------------------------------------------------
# Type-equality rules.
#
# Naming parallels the term-equality rules wherever the structure
# matches:
#
#   TY_REFL          reflexivity              (parallels REFL)
#   TY_SYM           symmetry                 (derived at term level)
#   TY_TRANS         transitivity             (derived at term level)
#   TY_CONG_BASE     atomic-type congruence   (parallels TM_CONG_BASE)
#   TY_PI            Pi-binder congruence     (parallels ABS, the term
#                                              binder congruence)
#   TY_SUBTYPE       Subtype-binder congruence (no term analogue --
#                                               refinement types are a
#                                               type-only construct)
#
# TY_SYM / TY_TRANS are primitive here even though their term-level
# counterparts are derived; types have no first-class application
# (Comb-equivalent), so the term-level derivation route via MK_COMB +
# REFL does not transfer.
# ---------------------------------------------------------------------------


def TY_REFL(ty: hol_type) -> type_eq_thm:
    return type_eq_thm([], ty, ty)


def TY_SYM(e: type_eq_thm) -> type_eq_thm:
    return type_eq_thm(e._asl, e._rhs, e._lhs)


def TY_TRANS(e1: type_eq_thm, e2: type_eq_thm) -> type_eq_thm:
    if not type_eq(e1._rhs, e2._lhs):
        raise HolError("TY_TRANS: middle types do not match")
    return type_eq_thm(term_union(e1._asl, e2._asl), e1._lhs, e2._rhs)


def TY_PI(v: Var, dom_eq: type_eq_thm,
          cod_eq: type_eq_thm) -> type_eq_thm:
    """Pi-binder congruence (Rabe 2026 Rule ξ, without the precondition
    branch -- preconditions live inside Subtype binders and are bridged
    by `TY_SUBTYPE`):

      Gamma |- A == A'    Gamma, x:A |- B == B'
      --------------------------------------------
      Gamma |- Pi(x:A). B == Pi(x:A'). B'

    `v` is the binder of the LHS Pi; its type must match `dom_eq._lhs`.
    The RHS Pi binder is `Var(v.name, dom_eq._rhs)` and its body is
    `cod_eq._rhs` with the LHS binder re-indexed to the RHS binder via
    the equal-by-bridge type ambient in scope.

    Freshness: `v` must not occur free in either premise's hypotheses
    (those are the ambient Gamma; the bound `x:A` would correspond to a
    discharged hypothesis if cod_eq had been derived in an extended
    context)."""
    if not type_eq(v.ty, dom_eq._lhs):
        raise HolError(
            f"TY_PI: binder type {_pp_ty(v.ty)} does not match "
            f"dom_eq lhs {_pp_ty(dom_eq._lhs)}"
        )
    for a in dom_eq._asl:
        if vfree_in(v, a):
            raise HolError(
                "TY_PI: binder occurs free in dom_eq hypotheses"
            )
    for a in cod_eq._asl:
        if vfree_in(v, a):
            raise HolError(
                "TY_PI: binder occurs free in cod_eq hypotheses"
            )
    v_rhs = Var(v.name, dom_eq._rhs)
    rhs_body = subst_in_type([(v_rhs, v)], cod_eq._rhs)
    return type_eq_thm(
        term_union(dom_eq._asl, cod_eq._asl),
        Pi(v, cod_eq._lhs),
        Pi(v_rhs, rhs_body),
    )


def TY_SUBTYPE(v: Var, dom_eq: type_eq_thm,
               pred_eq: thm) -> type_eq_thm:
    """Subtype-binder congruence:

      Gamma |- A == A'    Gamma, x:A |- F =_bool F'
      ---------------------------------------------
            Gamma |- A|F == A'|F'

    Completes the precondition branch of Rabe 2026 Rule ξ when combined
    with `TY_PI` over a Subtype-typed Pi binder.

    `pred_eq` must be a boolean-tagged equation `F =_bool F'` (both sides
    are predicates in the x:A context). `v` re-indexes to the RHS side
    just like in TY_PI."""
    if not type_eq(v.ty, dom_eq._lhs):
        raise HolError(
            f"TY_SUBTYPE: binder type {_pp_ty(v.ty)} does not match "
            f"dom_eq lhs {_pp_ty(dom_eq._lhs)}"
        )
    _require_eq(pred_eq._concl, "TY_SUBTYPE")
    if not type_eq(_eq_tag(pred_eq._concl), bool_ty):
        raise HolError(
            f"TY_SUBTYPE: predicate equation must be tagged at bool "
            f"(got {_pp_ty(_eq_tag(pred_eq._concl))})"
        )
    for a in dom_eq._asl:
        if vfree_in(v, a):
            raise HolError(
                "TY_SUBTYPE: binder occurs free in dom_eq hypotheses"
            )
    for a in pred_eq._asl:
        if vfree_in(v, a):
            raise HolError(
                "TY_SUBTYPE: binder occurs free in pred_eq hypotheses"
            )
    v_rhs = Var(v.name, dom_eq._rhs)
    pred_lhs = _lhs(pred_eq._concl)
    pred_rhs = _vsubst([(v_rhs, v)], _rhs(pred_eq._concl))
    return type_eq_thm(
        term_union(dom_eq._asl, pred_eq._asl),
        Subtype(v, pred_lhs),
        Subtype(v_rhs, pred_rhs),
    )


class PhiSide(NamedTuple):
    """One side of a dual Φ-walk -- the σ chosen for either the LHS or
    the RHS of a congruence rule."""
    theta_ty: list      # (chosen_hol_type, Tyvar)
    theta_tm: list      # (chosen_term, Var)
    tyop_theta: list    # (TypeAbs, name) for TyopVar slots
    type_args: list     # chosen hol_types for Tyvar entries (decl. order)
    term_args: list     # chosen terms for Var entries (decl. order)

    @classmethod
    def empty(cls) -> "PhiSide":
        return cls(
            theta_ty=[], theta_tm=[], tyop_theta=[],
            type_args=[], term_args=[],
        )


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
    if not isinstance(arg, (Tyvar, Tyapp, Pi, Subtype)):
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
    expected = _subst_full_type(
        out.theta_ty, out.theta_tm, out.tyop_theta, binder.ty
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
    _check_assume_proof(
        arg, binder.formula, out.theta_ty, out.theta_tm, ctx,
        tyop_theta=out.tyop_theta,
    )
    out.asl_extra[:] = term_union(out.asl_extra, arg._asl)


def _check_typeabs_shape(arg, params, theta_ty, theta_tm, tyop_theta,
                         ctx, who):
    """Validate a `TypeAbs` σ-evidence for a `TyopVar` slot: matching
    arity, and each bvar type matches the declared `param.ty` modulo
    earlier substitutions (definitional eq). Caller-supplied bvar
    names need not match the declared params -- the substitution that
    consumes the TypeAbs renames as needed."""
    if not isinstance(arg, TypeAbs):
        raise HolError(
            f"{ctx}: argument for TyopVar binder {who} must be a TypeAbs"
        )
    if len(arg.bvars) != len(params):
        raise HolError(
            f"{ctx}: TypeAbs for {who} has wrong arity "
            f"(expected {len(params)}, got {len(arg.bvars)})"
        )
    for bv, p in zip(arg.bvars, params):
        expected = _subst_full_type(theta_ty, theta_tm, tyop_theta, p.ty)
        if not type_eq(expected, bv.ty):
            raise HolError(
                f"{ctx}: TypeAbs bvar {bv.name} for {who} has type "
                f"{_pp_ty(bv.ty)}, expected {_pp_ty(expected)}"
            )


def _subst_tyop(binder, arg, out, ctx):
    _check_typeabs_shape(
        arg, binder.params, out.theta_ty, out.theta_tm,
        out.tyop_theta, ctx, binder.name,
    )
    out.tyop_theta.append((arg, binder.name))


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
    expected = _subst_full_type(
        lhs.theta_ty, lhs.theta_tm, lhs.tyop_theta, binder.ty
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


def _dual_tyop(binder, arg, lhs, rhs, asl_extra, ctx):
    """Symmetric case only: a single `TypeAbs` is required to coincide
    on both sides of the congruence. The kernel ships only this case
    (matching the symmetric `Assume` handling)."""
    _check_typeabs_shape(
        arg, binder.params, lhs.theta_ty, lhs.theta_tm,
        lhs.tyop_theta, ctx, binder.name,
    )
    lhs.tyop_theta.append((arg, binder.name))
    rhs.tyop_theta.append((arg, binder.name))


def _check_ty_eq_assume(arg, binders, lhs, rhs,
                       theta_ty, theta_tm, tyop_theta, ctx):
    """Validate a `TyEqAssume` σ-evidence.

    σ-shape depends on `binders`:
      * Empty binders   -- σ is a `type_eq_thm` directly.
      * Non-empty       -- σ is `(user_vars, type_eq_thm)`, where
                           `user_vars` is a tuple of `Var`s aligning
                           positionally with `binders` (the user's
                           chosen names for the schematic positions).

    Computes the expected sides under accumulated substitutions, then
    substitutes `user_vars` for `binders` (with binders' types
    ty-substituted), compares to `arg._lhs` / `arg._rhs` definitionally,
    and enforces freshness of each user_var (not free in any
    `arg._asl` entry) -- the discipline that makes the binders
    effectively universal."""
    if binders:
        if not (isinstance(arg, tuple) and len(arg) == 2):
            raise HolError(
                f"{ctx}: TyEqAssume with binders requires σ "
                f"= (user_vars, type_eq_thm)"
            )
        user_vars, ty_eq = arg
        user_vars = tuple(user_vars)
        if len(user_vars) != len(binders):
            raise HolError(
                f"{ctx}: TyEqAssume σ has {len(user_vars)} user_vars "
                f"for {len(binders)} binders"
            )
        for uv, b in zip(user_vars, binders):
            if not isinstance(uv, Var):
                raise HolError(
                    f"{ctx}: TyEqAssume user_var must be a Var (got "
                    f"{uv!r})"
                )
            b_ty = type_subst(theta_ty, b.ty)
            if not type_eq(uv.ty, b_ty):
                raise HolError(
                    f"{ctx}: TyEqAssume user_var {uv.name} type "
                    f"{_pp_ty(uv.ty)} does not match binder type "
                    f"{_pp_ty(b_ty)}"
                )
    else:
        ty_eq = arg
        user_vars = ()
    if not isinstance(ty_eq, type_eq_thm):
        raise HolError(
            f"{ctx}: argument for TyEqAssume must be a type_eq_thm"
        )
    expected_lhs = _subst_full_type(theta_ty, theta_tm, tyop_theta, lhs)
    expected_rhs = _subst_full_type(theta_ty, theta_tm, tyop_theta, rhs)
    if binders:
        rename = [(uv, Var(b.name, type_subst(theta_ty, b.ty)))
                  for uv, b in zip(user_vars, binders)]
        expected_lhs = subst_in_type(rename, expected_lhs)
        expected_rhs = subst_in_type(rename, expected_rhs)
    if not type_eq(expected_lhs, ty_eq._lhs):
        raise HolError(
            f"{ctx}: TyEqAssume lhs {_pp_ty(ty_eq._lhs)} does not match "
            f"expected {_pp_ty(expected_lhs)}"
        )
    if not type_eq(expected_rhs, ty_eq._rhs):
        raise HolError(
            f"{ctx}: TyEqAssume rhs {_pp_ty(ty_eq._rhs)} does not match "
            f"expected {_pp_ty(expected_rhs)}"
        )
    for uv in user_vars:
        for a in ty_eq._asl:
            if vfree_in(uv, a):
                raise HolError(
                    f"{ctx}: user_var {uv.name} occurs free in "
                    f"TyEqAssume hypothesis {_pp_tm(a)}"
                )
    return ty_eq


def _subst_ty_eq_assume(binder, arg, out, ctx):
    ty_eq = _check_ty_eq_assume(
        arg, binder.binders, binder.lhs, binder.rhs,
        out.theta_ty, out.theta_tm, out.tyop_theta, ctx,
    )
    out.asl_extra[:] = term_union(out.asl_extra, ty_eq._asl)


def _dual_assume(binder, arg, lhs, rhs, asl_extra, ctx):
    needed_l = _check_assume_proof(
        arg, binder.formula, lhs.theta_ty, lhs.theta_tm, ctx,
        tyop_theta=lhs.tyop_theta,
    )
    needed_r = _subst_full_term(
        rhs.theta_ty, rhs.theta_tm, rhs.tyop_theta, binder.formula
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


def _dual_ty_eq_assume(binder, arg, lhs, rhs, asl_extra, ctx):
    """Symmetric case only: a single `type_eq_thm` discharges the
    obligation on both sides of the congruence (matches the symmetric
    `Assume` / `TyopVar` handling)."""
    ty_eq = _check_ty_eq_assume(
        arg, binder.binders, binder.lhs, binder.rhs,
        lhs.theta_ty, lhs.theta_tm, lhs.tyop_theta, ctx,
    )
    asl_extra[:] = term_union(asl_extra, ty_eq._asl)


_SLOT_DISPATCH: dict = {
    Tyvar:      _SlotHandlers(subst=_subst_tyvar,       dual=_dual_tyvar),
    TyopVar:    _SlotHandlers(subst=_subst_tyop,        dual=_dual_tyop),
    Var:        _SlotHandlers(subst=_subst_var,         dual=_dual_var),
    Assume:     _SlotHandlers(subst=_subst_assume,      dual=_dual_assume),
    TyEqAssume: _SlotHandlers(subst=_subst_ty_eq_assume,
                              dual=_dual_ty_eq_assume),
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
    equation is tagged at the LHS view `A[σ_l]`. The instantiated body
    types `A[σ_l]` and `A[σ_r]` must either agree definitionally, or
    `cod_eq` must bridge them (in either orientation); the bridge's
    hypotheses are absorbed."""
    try:
        phi = get_const_phi(name)
        decl_ty = get_const_type(name)
    except KeyError:
        raise HolError(f"TM_CONG_BASE: unknown constant {name}")
    result = _apply_phi_dual(phi, args, f"TM_CONG_BASE({name})")
    inst_ty_l = _subst_full_type(
        result.lhs.theta_ty, result.lhs.theta_tm, result.lhs.tyop_theta, decl_ty
    )
    inst_ty_r = _subst_full_type(
        result.rhs.theta_ty, result.rhs.theta_tm, result.rhs.tyop_theta, decl_ty
    )
    asl = result.asl_extra
    if not type_eq(inst_ty_l, inst_ty_r):
        if cod_eq is None:
            raise HolError(
                f"TM_CONG_BASE: instantiated types differ "
                f"({_pp_ty(inst_ty_l)} vs {_pp_ty(inst_ty_r)}); "
                f"pass cod_eq to bridge them"
            )
        if not _bridge_matches(cod_eq, inst_ty_l, inst_ty_r):
            raise HolError(
                f"TM_CONG_BASE: cod_eq bridge "
                f"{_pp_ty(cod_eq._lhs)} == {_pp_ty(cod_eq._rhs)} "
                f"does not connect {_pp_ty(inst_ty_l)} and "
                f"{_pp_ty(inst_ty_r)}"
            )
        asl = term_union(asl, cod_eq._asl)
    lhs_const = Const(name, inst_ty_l, tuple(result.lhs.term_args))
    rhs_const = Const(name, inst_ty_r, tuple(result.rhs.term_args))
    return thm(asl, safe_mk_eq(inst_ty_l, lhs_const, rhs_const))


def THM_CONG_BASE(staged: Staged, args: list) -> thm:
    """Staged-axiom congruence (analogue of TY_CONG_BASE / TM_CONG_BASE
    for a staged axiom):
            (Φ) ▷ F in theory      per-slot Φ-args
            -------------------------------------------
                  Gamma |- F[σ_l] = F[σ_r]  : bool

    Each `args[i]` matches Φ entry i (see `_apply_phi_dual`)."""
    if not isinstance(staged, Staged) or not isinstance(staged._body, JProp):
        raise HolError(
            "THM_CONG_BASE: first argument must be a Staged with JProp body"
        )
    phi = staged._phi
    F = staged._body.formula
    result = _apply_phi_dual(phi, args, "THM_CONG_BASE")
    F_l = _subst_full_term(
        result.lhs.theta_ty, result.lhs.theta_tm, result.lhs.tyop_theta, F
    )
    F_r = _subst_full_term(
        result.rhs.theta_ty, result.rhs.theta_tm, result.rhs.tyop_theta, F
    )
    return thm(result.asl_extra, safe_mk_eq(bool_ty, F_l, F_r))


# ---------------------------------------------------------------------------
# Predicate subtypes & subtyping
#
# Subtype(bvar:A, p) -- the refinement {y:A | p[y/bvar]}, represented
# as a hol_type alongside Tyvar/Tyapp/Pi. The system carries no
# separate `<:` judgment: refinement has three typing-layer primitives
# -- RESTRICT (intro from base typing + predicate proof),
# RESTRICT_PROOF (elim to the predicate), and FORGET_TYPING (elim to
# the base type). Subtype is the single canonical refinement type
# former; it appears at every position (top-level, codomain, equality
# index, Pi-domain) and Pi-domain refinement is encoded by a
# Subtype-typed bvar.
# ---------------------------------------------------------------------------


def RESTRICT(t_th: typing_thm, p_th: thm,
             subtype: hol_type) -> typing_thm:
    """Intro:  Gamma |- t : A    Delta |- p[t/y]
              ----------------------------------
                    Gamma + Delta |- t : A|p

    `subtype` is the target Subtype(y:A, p) so the caller pins down both
    `A` and the predicate `p` (since several refinements over the same A
    may be in play). The kernel checks:
      - subtype.bvar.ty matches t_th._ty (the base type),
      - p_th._concl alpha-eq predicate[t/y]."""
    if not isinstance(subtype, Subtype):
        raise HolError(
            f"RESTRICT: target must be a Subtype, got {_pp_ty(subtype)}"
        )
    if not type_eq(subtype.bvar.ty, t_th._ty):
        raise HolError(
            f"RESTRICT: base type mismatch -- t : {_pp_ty(t_th._ty)} but "
            f"subtype's base is {_pp_ty(subtype.bvar.ty)}"
        )
    needed = _vsubst([(t_th._tm, subtype.bvar)], subtype.predicate)
    if not _tm_alpha([], p_th._concl, needed):
        raise HolError(
            f"RESTRICT: p_th concludes {_pp_tm(p_th._concl)} but "
            f"required predicate at t is {_pp_tm(needed)}"
        )
    asl = term_union(t_th._asl, p_th._asl)
    return typing_thm(asl, t_th._tm, subtype)


def RESTRICT_PROOF(t_th: typing_thm) -> thm:
    """Elim (extract the proof):  Gamma |- t : A|p
                                  -----------------
                                  Gamma |- p[t/y]"""
    ty = t_th._ty
    if not isinstance(ty, Subtype):
        raise HolError(
            f"RESTRICT_PROOF: term type is not a Subtype (got {_pp_ty(ty)})"
        )
    return thm(
        t_th._asl,
        _vsubst([(t_th._tm, ty.bvar)], ty.predicate),
    )


def FORGET_TYPING(t_th: typing_thm) -> typing_thm:
    """Refinement projection at the typing layer.

      Gamma |- t : A|p
      ----------------
       Gamma |- t : A

    The typing-level companion of `RESTRICT_PROOF` (which extracts the
    predicate). Replaces the legacy `SUBSUME(t_th, ST_FORGET(t_th._ty))`
    idiom -- the subtype detour is no longer needed when all you want
    is to drop the refinement on a value's type. Follows Rabe 2026 where
    refinement projection is a typing primitive, not a subtype operation."""
    ty = t_th._ty
    if not isinstance(ty, Subtype):
        raise HolError(
            f"FORGET_TYPING: type is not a Subtype (got {_pp_ty(ty)})"
        )
    return typing_thm(t_th._asl, t_th._tm, ty.bvar.ty)


# ---------------------------------------------------------------------------
# Dependent implication formation (Rule D, Rabe 2026 Fig. 4).
#
# DHOL admits a typing rule that lets the consequent's well-formedness
# depend on the antecedent's truth:
#
#     Gamma |- F : bool    Gamma, |>F |- G : bool
#     -------------------------------------------
#               Gamma |- F ==> G : bool
#
# Like `safe_mk_eq` builds `=` directly without consulting `the_decls`,
# this rule synthesises the `==>` constant at type `bool -> bool -> bool`.
# That fixes the implication's name and arity at the kernel level (callers
# that prefer a different surface name should wrap this rule).
# ---------------------------------------------------------------------------


def IMP_TYPE(F_th: typing_thm, G_th: typing_thm) -> typing_thm:
    """Rule D (Rabe 2026 Fig. 4): build the typing for a dependent
    implication, discharging F from G's hypotheses.

      Gamma |- F : bool    Gamma, |>F |- G : bool
      -------------------------------------------
                Gamma |- F ==> G : bool

    The discharge is what makes this primitive: no structural typing
    rule can shrink an asl, so the implication's typing has to be
    introduced here rather than reassembled from APP + CONST."""
    _require_bool(F_th, "IMP_TYPE antecedent")
    _require_bool(G_th, "IMP_TYPE consequent")
    imp_ty = Pi(Var("_", bool_ty), Pi(Var("_", bool_ty), bool_ty))
    imp_const = Const("==>", imp_ty)
    tm = Comb(Comb(imp_const, F_th._tm), G_th._tm)
    asl = term_union(F_th._asl, term_remove(F_th._tm, G_th._asl))
    return typing_thm(asl, tm, bool_ty)


# ---------------------------------------------------------------------------
# Validity rules: REFL, ASSUME, BETA, EQ_TY_CONV, MK_COMB, ABS,
# EQ_MP, DEDUCT_ANTISYM_RULE, INST, INST_TYPE
# (HOL Light's 10-rule core minus TRANS, lifted to typing-as-derivation.
#  ETA, TRANS, DISCH, MP and the ==> defining equation are derived in
#  basics_dhol.)
# ---------------------------------------------------------------------------


def REFL(t_th: typing_thm) -> thm:
    return thm(t_th._asl, safe_mk_eq(t_th._ty, t_th._tm, t_th._tm))


def ASSUME(F_th: typing_thm) -> thm:
    _require_bool(F_th, "ASSUME")
    return thm([F_th._tm, *F_th._asl], F_th._tm)


def BETA(redex_th: typing_thm) -> thm:
    """Beta:  Gamma |- (\\x:A. t) u : B
             ----------------------------
             Gamma |- (\\x:A. t) u = t[u/x]

    Full beta a la Rabe 2026: the argument is arbitrary, not just the
    bound variable. Well-typedness of the redex (which `redex_th`
    certifies) is sufficient -- substitution preserves typing, so the
    RHS is typeable at the same type B = body-type[u/x].

    Preconditioned domains (e.g. `\\x:A|p. t`) have their refinement
    baked into the binder's type as a Subtype, so BETA needs no
    precondition handling: the binder being `x : A|p` already implies
    that any `x` in scope satisfies p."""
    tm = redex_th._tm
    if not (isinstance(tm, Comb) and isinstance(tm.fun, Abs)):
        raise HolError("BETA: not a beta-redex")
    rhs = _vsubst([(tm.arg, tm.fun.bvar)], tm.fun.body)
    return thm(redex_th._asl, safe_mk_eq(redex_th._ty, tm, rhs))


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


def MK_COMB(th1: thm, th2: thm,
            cod_eq: type_eq_thm | None = None) -> thm:
    """congAppl':  Gamma |- f =Pi(x:A).B f'    Gamma |- a =A a'
                  ----------------------------------------------
                          Gamma |- f a =B[a/x] f' a'

    th2's eq tag must definitionally match f's Pi-domain (pre-EQ_TY_CONV
    th2 to align if not). The substituted codomains `B[l2/x]` and
    `B[r2/x]` must either agree definitionally, or `cod_eq` must bridge
    them (in either orientation); the result is tagged at the LHS view
    `B[l2/x]` and the bridge's hypotheses are absorbed.

    Preconditioned domains live inside A as Subtype refinements; if
    `A = A0|p`, the argument equation must already be tagged at A0|p
    (which guarantees both sides satisfy p). No per-rule discharge."""
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
    if not type_eq(expected, arg_ty):
        raise HolError(
            f"MK_COMB: domain types do not agree "
            f"(expected {_pp_ty(expected)}, got {_pp_ty(arg_ty)}); "
            f"pre-EQ_TY_CONV th2 to align"
        )
    asl = term_union(th1._asl, th2._asl)
    l1, r1 = _lhs(c1), _rhs(c1)
    l2, r2 = _lhs(c2), _rhs(c2)
    result_ty_l = subst_in_type([(l2, f_ty.bvar)], f_ty.body)
    result_ty_r = subst_in_type([(r2, f_ty.bvar)], f_ty.body)
    if not type_eq(result_ty_l, result_ty_r):
        if cod_eq is None:
            raise HolError(
                f"MK_COMB: codomain types do not agree "
                f"({_pp_ty(result_ty_l)} vs {_pp_ty(result_ty_r)}); "
                f"pass cod_eq to bridge them"
            )
        if not _bridge_matches(cod_eq, result_ty_l, result_ty_r):
            raise HolError(
                f"MK_COMB: cod_eq bridge "
                f"{_pp_ty(cod_eq._lhs)} == {_pp_ty(cod_eq._rhs)} "
                f"does not connect codomains "
                f"{_pp_ty(result_ty_l)} and {_pp_ty(result_ty_r)}"
            )
        asl = term_union(asl, cod_eq._asl)
    return thm(asl, safe_mk_eq(result_ty_l, Comb(l1, l2), Comb(r1, r2)))


def ABS(v: Var, th: thm, ty_eq: type_eq_thm | None = None) -> thm:
    """congLambda':  Gamma |- A == A'   Gamma, x:A |- t =B t'
                    ------------------------------------------------
                    Gamma |- (\\x:A. t) =Pi(x:A).B (\\x:A'. t')

    Without `ty_eq` the binder type is shared (the standard
    homogeneous case). With `ty_eq` bridging `v.ty == A'`, the RHS
    abstraction is built over `Var(v.name, A')`; the bridge's
    hypotheses are absorbed.

    ``v`` must not occur free in any hypothesis of `th` or of
    `ty_eq`."""
    c = th._concl
    _require_eq(c, "ABS")
    if any(vfree_in(v, a) for a in th._asl):
        raise HolError("ABS: bound variable occurs free in hypotheses")
    body_ty = _eq_tag(c)
    l, r = _lhs(c), _rhs(c)
    new_ty = Pi(v, body_ty)
    if ty_eq is None:
        return thm(th._asl, safe_mk_eq(new_ty, Abs(v, l), Abs(v, r)))
    if not type_eq(ty_eq._lhs, v.ty):
        if type_eq(ty_eq._rhs, v.ty):
            ty_eq = TY_SYM(ty_eq)
        else:
            raise HolError(
                f"ABS: ty_eq bridge "
                f"{_pp_ty(ty_eq._lhs)} == {_pp_ty(ty_eq._rhs)} does not "
                f"connect binder type {_pp_ty(v.ty)}"
            )
    if any(vfree_in(v, a) for a in ty_eq._asl):
        raise HolError(
            "ABS: bound variable occurs free in ty_eq hypotheses"
        )
    v_rhs = Var(v.name, ty_eq._rhs)
    return thm(
        term_union(th._asl, ty_eq._asl),
        safe_mk_eq(new_ty, Abs(v, l), Abs(v_rhs, r)),
    )


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
    substitution into every type annotation, alpha-renaming bound
    variables when type instantiation would otherwise cause them to
    collide with a free one in the body. Well-formedness of replacement
    types is the caller's responsibility (honest-caller perimeter)."""
    if not theta:
        return th
    f = lambda tm: _inst_in_term(theta, tm)
    return thm(term_image(f, th._asl), f(th._concl))


# ---------------------------------------------------------------------------
# Axioms and definitions
# ---------------------------------------------------------------------------

the_axioms: list = []


def _validate_phi_body(asl, free_vars, free_tyvars, free_tyops,
                       phi, ctx, *, extra_allowed_tvs=()) -> None:
    """Validate that a cert payload is well-formed under Φ:
      * every asl entry alpha-matches an Assume(F) formula in Φ;
      * every free Var is bound by a Var entry in Φ;
      * every free Tyvar is bound by a Tyvar entry in Φ (or in
        `extra_allowed_tvs`, used by `new_basic_definition` where
        the constant's own lhs.ty already binds some tyvars);
      * every TyopApp name is bound by a TyopVar entry in Φ.

    Shared by every Φ-staged former (`new_axiom`, `new_type_eq_axiom`,
    `new_basic_definition`); the only thing the caller
    decides is which scanners to use to enumerate the free variables /
    tyvars / tyops of its specific payload."""
    expected_asl = _phi_asl(phi)
    for a in asl:
        if not any(_tm_alpha([], a, f) for f in expected_asl):
            raise HolError(
                f"{ctx}: asl entry {_pp_tm(a)} is not declared by any "
                f"Assume entry in Φ"
            )
    bound_vars = [b for b in phi if isinstance(b, Var)]
    for fv in free_vars:
        if fv not in bound_vars:
            raise HolError(
                f"{ctx}: free var {fv.name} is not bound by any Var "
                f"entry in Φ"
            )
    allowed_tvs = list(extra_allowed_tvs)
    for b in phi:
        if isinstance(b, Tyvar) and b not in allowed_tvs:
            allowed_tvs.append(b)
    for tv in free_tyvars:
        if tv not in allowed_tvs:
            raise HolError(
                f"{ctx}: type-var {tv.name} is not reflected in Φ"
            )
    allowed_tyops = {b.name for b in phi if isinstance(b, TyopVar)}
    for name in free_tyops:
        if name not in allowed_tyops:
            raise HolError(
                f"{ctx}: TyopApp {name!r} is not reflected by any "
                f"TyopVar entry in Φ"
            )


def _scan_J_payload(j: Judgement):
    """Compute `(free_vars, free_tyvars, free_tyops)` of a cert
    J-variant's payload. Lifts the term-vs-type scanner choice out of
    the axiom-formers so they share `_validate_phi_body`."""
    if isinstance(j, JProp):
        F = j.formula
        return frees(F), type_vars_in_term(F), tyop_names_in_term(F)
    if isinstance(j, JTyping):
        tm = j.tm
        return frees(tm), type_vars_in_term(tm), tyop_names_in_term(tm)
    if isinstance(j, JEq):
        fvs: list = []
        tvs: list = []
        tos: list = []
        for ty in (j.lhs, j.rhs):
            _uniq_extend(fvs, frees_in_type(ty))
            _uniq_extend(tvs, tyvars(ty))
            _uniq_extend(tos, tyop_names_in_type(ty))
        return fvs, tvs, tos
    raise HolError(f"_scan_J_payload: unsupported J {type(j).__name__}")


def _new_J_axiom(cert: Cert, phi, ctx: str) -> Staged:
    """Generic staged-axiom former. Dispatches on `cert._j`:
      * `JTyping(F, bool)` → `Staged(phi, JProp(F))` -- a validity axiom.
      * `JEq(L, R)`        → `Staged(phi, JEq(L, R))`.
    The Φ-body well-formedness scan is shared (`_validate_phi_body`).
    Registered in `the_axioms` and returned."""
    if phi is None:
        phi = ()
    _check_phi(phi, ctx)
    phi = tuple(phi)
    j = cert._j
    if isinstance(j, JTyping):
        if not type_eq(j.ty, bool_ty):
            raise HolError(f"{ctx}: non-bool type {_pp_ty(j.ty)}")
        body: Judgement = JProp(j.tm)
    elif isinstance(j, JEq):
        body = j
    else:
        raise HolError(
            f"{ctx}: unsupported certificate kind {type(cert).__name__}"
        )
    free_vars, free_tyvars, free_tyops = _scan_J_payload(body)
    _validate_phi_body(cert._asl, free_vars, free_tyvars, free_tyops,
                       phi, ctx)
    staged = Staged(phi, body)
    the_axioms.append(staged)
    return staged


def new_axiom(F_th: typing_thm, phi: tuple | None = None) -> Staged:
    """Declare an axiom `(Φ) ▷ F`. Returns a `Staged` with a `JProp`
    body; use `interpret(staged, σ)` to instantiate.

    Φ is a telescope of the usual Slot kinds. When Φ is empty (the
    default), the axiom is concrete: `F_th` must be unconditional, free
    of Vars, and free of Tyvars. Otherwise Φ binds the axiom's
    parameters per `_validate_phi_body` (asl matches Assume formulas,
    free Vars / Tyvars / TyopApps are reflected in Φ)."""
    return _new_J_axiom(F_th, phi, "new_axiom")


def new_type_eq_axiom(eq_th: type_eq_thm,
                      phi: tuple | None = None) -> Staged:
    """Declare a type-equality axiom `(Φ) ▷ lhs == rhs`. Returns a
    `Staged` with a `JEq` body; use `interpret(staged, σ)` to
    instantiate. TyEqAssume entries in Φ are pure type-equality
    preconditions and contribute no bool asl."""
    return _new_J_axiom(eq_th, phi, "new_type_eq_axiom")


def interpret(staged: Staged, sigma: tuple):
    """One-shot interpretation of a `Staged` judgement at σ.

    Dispatches on `staged._body`:
      * `JProp(F)`       → returns a concrete `thm`.
      * `JEq(L, R)`      → returns a concrete `type_eq_thm`.

    Walks Φ left-to-right, discharging slot-by-slot:
      * Tyvar slot       -- σ-entry is a `hol_type` (INST_TYPE-style);
      * TyopVar slot     -- σ-entry is a `TypeAbs` (rank-1 type op);
      * Var slot         -- σ-entry is a `typing_thm` (INST-style);
      * Assume slot      -- σ-entry is a `thm` (MP-style);
      * TyEqAssume slot  -- σ-entry is a `type_eq_thm` (sides matching
                            the schematic, freshness on binders).

    σ-shape is validated by `_apply_phi_subst` -- the same walker
    `mk_type` and `CONST` use. asl from σ-evidences is absorbed; the
    original Assume / TyEqAssume obligations are discharged."""
    if not isinstance(staged, Staged):
        raise HolError("interpret: first argument must be a Staged")
    phi = staged._phi
    result = _apply_phi_subst(phi, tuple(sigma), "interpret")
    f_tm = lambda tm: _subst_full_term(
        result.theta_ty, result.theta_tm, result.tyop_theta, tm
    )
    f_ty = lambda ty: _subst_full_type(
        result.theta_ty, result.theta_tm, result.tyop_theta, ty
    )
    b = staged._body
    if isinstance(b, JProp):
        return thm(result.asl_extra, f_tm(b.formula))
    if isinstance(b, JEq):
        return type_eq_thm(result.asl_extra, f_ty(b.lhs), f_ty(b.rhs))
    raise HolError(f"interpret: unknown Staged body {type(b).__name__}")


the_definitions: list = []


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
    ctx = f"new_basic_definition({lhs.name})"
    if phi is None:
        phi = tuple(Tyvar(tv.name) for tv in tyvars(lhs.ty))
    else:
        _check_phi(phi, ctx)
        phi = tuple(phi)
    free_vars, free_tyvars, free_tyops = _scan_J_payload(JTyping(rhs_th._tm, rhs_th._ty))
    _validate_phi_body(
        rhs_th._asl, free_vars, free_tyvars, free_tyops, phi, ctx,
        extra_allowed_tvs=tyvars(lhs.ty),
    )
    if any(isinstance(b, TyopVar) for b in phi):
        raise HolError(
            "new_basic_definition: TyopVar in Φ unsupported -- the "
            "defining equation would need to keep the operator unresolved, "
            "and the kernel has no representation for free TyopVars "
            "outside Φ."
        )
    if any(isinstance(b, TyEqAssume) for b in phi):
        raise HolError(
            "new_basic_definition: TyEqAssume in Φ unsupported -- the "
            "self-application σ has no canonical type_eq_thm to supply "
            "for a refl-like assertion."
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


