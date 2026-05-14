# ---------------------------------------------------------------------------
# Stage 2 -- the HF proof system (Świerczkowski-style).
# ---------------------------------------------------------------------------
#
# Logical axioms (shared with any first-order Hilbert system):
#   * Propositional tautologies (any standard finite axiomatisation).
#   * Quantifier axioms: !x. F[x] -> F[t/x]; F -> !x. F (x not free).
#   * Equality: t = t; substitution under equality.
#
# Non-logical axioms (HF; five closed formulas, signature: In_a /
# Insert_t / Empty_t / Eq_f added in hf_syntax.py):
#   HF1.  !x.       ~In x Empty
#   HF2.  !i s.     In i (Insert i s)
#   HF3. !i j s.   ~(i = j) -> (In j (Insert i s) <-> In j s)
#   HF4. !a b.     (!x. In x a <-> In x b) -> a = b
#   HF5. !x y.     In x y -> ?z. y = Insert x z          (HF predecessor)
#
# Robinson arithmetic axioms Q1-Q7 were removed 2026-05-10. Pure HF is
# the cleanest object theory for incompleteness (Świerczkowski 2003);
# numerals encode as von Neumann ordinals and arithmetic operations are
# HF-recursive in the meta-theory.
#
# Rules: modus ponens; generalization.
#
# Stage 2A (foundations):
#   * The five HF axioms as concrete encoded nat0 terms.
#   * ``is_hf_axiom``: decidable recogniser for the five HF axioms
#     (name retained for now to limit refactor blast radius).
#
# Stage 2B (proof system):
#   * ``is_mp``, ``is_gen``: modus-ponens / generalisation predicates
#     on godelnums.
#   * Eight logical-axiom schemas as sigma_1 predicates: ``is_K``,
#     ``is_S``, ``is_N`` (Mendelson propositional); ``is_UI``,
#     ``is_Vac``, ``is_FaImp`` (quantifier; ``is_Vac`` and
#     ``is_FaImp`` carry ``free_in`` side conditions); ``is_Refl``,
#     ``is_Subst`` (equality). The quantifier and equality schemas
#     reuse ``substitute`` and ``free_in`` from ``hf_syntax``.
#     ``is_FaImp`` is Mendelson's K6 -- ``!v.(F -> G) -> (F -> !v.G)``
#     when ``v`` not free in ``F`` -- adopted to make
#     PROV_HF_DT_GEN / DTChain.gen unconditionally proved.
#   * ``is_logical_axiom`` (disjunction over the eight schemas) and
#     ``is_axiom = is_hf_axiom \/ is_logical_axiom``.
#   * ``Prov_HF``: provability predicate, defined in ``hf_repr_core.py``
#     as existence of a ranked HF-set proof object:
#         Prov_HF n  :<=>  ?P. Proof_HF_set P n.
#   * Closure rules:
#         |- !n. is_axiom n ==> Prov_HF n.                  (PROV_HF_AXIOM)
#         |- !f g. Prov_HF f /\ Prov_HF (Imp_f f g)
#                  ==> Prov_HF g.                           (PROV_HF_MP)
#         |- !f x. Prov_HF f ==> Prov_HF (Forall_f x f).     (PROV_HF_GEN)
#
# Design note: Stage 3 originally planned to internalise a list-based
# ``Proof_HF``. That path has been removed. HF provability now uses
# ranked finite HF sets of proof-step records, so no list theory is
# needed in the proof checker.

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const, mk_app, mk_eq
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from tactics import (
    SPECL,
    SYM,
    DISJ1,
    DISJ2,
    EQ_MP,
)
from basics import mk_abs, rand
from axioms import mk_or
from fusion import REFL
from hf_syntax import (
    Eq_f,
    Not_f,
    Imp_f,
    Forall_f,
)

# The HF primitives Empty_t, Insert_t, In_a are referenced by name from
# parser strings in this file; importing hf_syntax above is sufficient
# to register them as kernel constants.


# ---------------------------------------------------------------------------
# Variable-index conventions for the HF axioms.
#
# The axioms below use two object-language variable slots; we choose
# nat0 indices 0 and SUC0 0:
#
#   Var_x  :=  Var_t 0
#   Var_y  :=  Var_t (SUC0 0)
#
# Both are concrete closed nat0 terms.
# ---------------------------------------------------------------------------


VAR_X_DEF = define("var_x", parse_type("nat0"), "Var_t 0")
var_x = mk_const("var_x", [])

VAR_Y_DEF = define("var_y", parse_type("nat0"), "Var_t (SUC0 0)")
var_y = mk_const("var_y", [])

# Third bound-variable slot, used by the HF axioms (HF3, HF4, HF5).
VAR_Z_DEF = define("var_z", parse_type("nat0"), "Var_t (SUC0 (SUC0 0))")
var_z = mk_const("var_z", [])


# ---------------------------------------------------------------------------
# HF axioms HF1-HF5 (Świerczkowski-style: HF as the object theory).
#
# These mirror the HOL theorems ``NOT_IN_EMPTY``, ``IN_INSERT_SAME``,
# ``IN_INSERT_DIFF``, ``IN_EXT`` from ``hf_sets.py``, plus a "predecessor"
# axiom (Q12) replacing the previous arithmetic foundation form. The
# encoding desugars absent connectives:
#
#   p /\ q       :=  ~(p -> ~q)
#   p <-> q      :=  (p -> q) /\ (q -> p)
#                =   ~( (p -> q) -> ~(q -> p) )
#   ?z. body     :=  ~!z. ~body
#
# Variable indices: var_x = 0, var_y = SUC0 0, var_z = SUC0 (SUC0 0).
#
# Q1-Q7 (Robinson arithmetic) were stripped 2026-05-10. Pure HF uses
# von Neumann numerals (numeral 0 := Empty, numeral (n+1) := Insert n n)
# and represents arithmetic operations as HF-recursive definitions; no
# arithmetic axioms appear in the object theory.
# ---------------------------------------------------------------------------


# HF1.  !x. ~In x Empty
HF1_AXIOM_DEF = define(
    "HF1_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Not_f (In_a var_x Empty_t))",
)
HF1_axiom = mk_const("HF1_axiom", [])


# HF2.  !x y. In x (Insert x y)        ("i in Insert i s" with i=x, s=y)
HF2_AXIOM_DEF = define(
    "HF2_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) (In_a var_x (Insert_t var_x var_y)))",
)
HF2_axiom = mk_const("HF2_axiom", [])


# HF3. !x y z. ~(x = y) -> (In y (Insert x z) <-> In y z)
# Iff body desugared:
#   A <-> B  :=  ~( (A -> B) -> ~(B -> A) )
# where A = In_a var_y (Insert_t var_x var_z),
#       B = In_a var_y var_z.
HF3_AXIOM_DEF = define(
    "HF3_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) (Forall_f (SUC0 (SUC0 0)) "
    "(Imp_f (Not_f (Eq_f var_x var_y)) "
    "(Not_f (Imp_f "
    "(Imp_f (In_a var_y (Insert_t var_x var_z)) (In_a var_y var_z)) "
    "(Not_f (Imp_f (In_a var_y var_z) (In_a var_y (Insert_t var_x var_z))))"
    ")))))",
)
HF3_axiom = mk_const("HF3_axiom", [])


# HF4. !a b. (!x. In x a <-> In x b) -> a = b
# (a, b, x) -> (var_x, var_y, var_z).
# Inner iff: Not_f (Imp_f (Imp_f (In z a) (In z b)) (Not_f (Imp_f (In z b) (In z a))))
HF4_AXIOM_DEF = define(
    "HF4_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) "
    "(Imp_f "
    "(Forall_f (SUC0 (SUC0 0)) "
    "(Not_f (Imp_f "
    "(Imp_f (In_a var_z var_x) (In_a var_z var_y)) "
    "(Not_f (Imp_f (In_a var_z var_y) (In_a var_z var_x)))"
    "))) "
    "(Eq_f var_x var_y)))",
)
HF4_axiom = mk_const("HF4_axiom", [])


# HF5. !x y. In x y -> ?z. y = Insert x z          (HF predecessor)
# Every member can be removed: if x is in y, then y was constructed by
# inserting x into some smaller HF set. Encoded as ~!z. ~(y = Insert x z).
# This replaces the previous arithmetic form ``In x y -> nat0_lt x y``,
# which leaned on Plus_t / Succ_t. The HF-native version is provable
# from extensionality + adjunction inside the standard HF model.
HF5_AXIOM_DEF = define(
    "HF5_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) "
    "(Imp_f (In_a var_x var_y) "
    "(Not_f (Forall_f (SUC0 (SUC0 0)) "
    "(Not_f (Eq_f var_y (Insert_t var_x var_z)))))))",
)
HF5_axiom = mk_const("HF5_axiom", [])


HF_AXIOMS = [
    ("HF1_axiom", HF1_axiom, HF1_AXIOM_DEF),
    ("HF2_axiom", HF2_axiom, HF2_AXIOM_DEF),
    ("HF3_axiom", HF3_axiom, HF3_AXIOM_DEF),
    ("HF4_axiom", HF4_axiom, HF4_AXIOM_DEF),
    ("HF5_axiom", HF5_axiom, HF5_AXIOM_DEF),
]


# ---------------------------------------------------------------------------
# HF axioms -- design notes.
#
# Q8-Q11 mirror the HOL theorems NOT_IN_EMPTY / IN_INSERT_SAME /
# IN_INSERT_DIFF / IN_EXT from hf_sets.py and bits.py, so the standard
# model of HF satisfies each axiom by one HOL citation. Q12 (HF
# predecessor) is provable from extensionality + adjunction in HF and
# also satisfied by the standard model.
#
# Świerczkowski's HF additionally has an induction-on-construction
# schema (HF_IND) that we have not yet axiomatised — it would require
# an axiom-schema recogniser. The five closed axioms above suffice for
# the diagonal lemma + first incompleteness; HF_IND is needed only for
# the consistency / Sigma_1-soundness arguments at Stage 6 (where it
# can either be added to the proof system or invoked at the meta-level
# as HOL induction over the HF construction in hf_sets.py).
#
# The structural recognisers in hf_syntax.py (is_term, is_form,
# free_in, substitute) carry matching disjuncts and AT-equations for
# Insert_t, In_a, Empty_t, Eq_f.
#
# TODO -- follow-up work at Stage 3C/3D:
#
#   * Rewrite the *_internal predicates in hf_repr_core.py against the HF
#     primitives:
#       - substitute_internal: Sigma_1 over an HF trace set of
#         (input-shape, output-shape) pairs.
#       - Proof_HF_internal: ranked finite HF set of proof-step records
#         with dependencies restricted to lower-ranked records.
#
#   * Discharge DIAG_REPRESENTS / DIAG_FUNCTIONAL in hf_godel1.py
#     by composing substitute_internal with the von Neumann numeral
#     predicate, both Sigma_1 and HF-expressible.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# is_hf_axiom -- decidable recogniser for the five HF axioms.
#
#   is_hf_axiom n  :<=>  n = HF1_axiom \/ ... \/ n = HF5_axiom
#
# No recursion -- a 5-fold disjunction of equalities with closed nat0
# numerals. Decidable trivially. Name retained as ``is_hf_axiom`` to
# limit the refactor diff; will rename to ``is_hf_axiom`` later.
# ---------------------------------------------------------------------------


_n_n0 = Var("n", nat0_ty)


def _disj_chain(eqs):
    """Build a right-associated disjunction ``eqs[0] \\/ eqs[1] \\/ ...``."""
    out = eqs[-1]
    for e in reversed(eqs[:-1]):
        out = mk_or(e, out)
    return out


_q_axiom_disj = _disj_chain(
    [mk_eq(_n_n0, ax_const) for (_, ax_const, _) in HF_AXIOMS]
)

# Pointwise:
#  |- !n. is_hf_axiom n =
#         (n = HF1_axiom \/ n = HF2_axiom \/ ... \/ n = HF5_axiom).
IS_HF_AXIOM_DEF, IS_HF_AXIOM_AT = define_with_at(
    "is_hf_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _q_axiom_disj),
)
is_hf_axiom = mk_const("is_hf_axiom", [])


# Each HF axiom is itself an HF axiom: |- is_hf_axiom HF{i}_axiom.
# Use direct disjunction-introduction.
def _prove_q_axiom_holds(name, axiom_const, position):
    """|- is_hf_axiom name_axiom -- discharge by DISJ at position.

    ``position`` is 1-indexed (1..len(HF_AXIOMS)).
    """
    eq_chain = [mk_eq(axiom_const, ax_const) for (_, ax_const, _) in HF_AXIOMS]
    idx = position - 1
    th = REFL(axiom_const)  # |- axiom_const = axiom_const
    if idx < len(eq_chain) - 1:
        right_tail = _disj_chain(eq_chain[idx + 1 :])
        th = DISJ1(th, right_tail)
    for j in range(idx - 1, -1, -1):
        th = DISJ2(eq_chain[j], th)
    spec = SPECL([axiom_const], IS_HF_AXIOM_AT)  # |- is_hf_axiom ax = body
    return EQ_MP(SYM(spec), th)


IS_HF_AXIOM_HOLDS = {
    name: _prove_q_axiom_holds(name, ax_const, i + 1)
    for i, (name, ax_const, _) in enumerate(HF_AXIOMS)
}


# ---------------------------------------------------------------------------
# Stage 2B (a) -- modus ponens / generalisation predicates.
#
#   is_mp f1 f2 g    :<=>  f2 = Imp_f f1 g
#                          ("g follows from f1 and f1 -> g by MP")
#   is_gen f g       :<=>  ?x. g = Forall_f x f
#                          ("g is the generalisation of f over some x")
#
# Both are simple equational predicates on godelnums; no recursion. We
# define them as plain HOL functions and immediately derive pointwise
# unfolds for downstream proof-checker reasoning.
# ---------------------------------------------------------------------------


_f1_n0 = Var("f1", nat0_ty)
_f2_n0 = Var("f2", nat0_ty)
_g_n0 = Var("g", nat0_ty)
_f_n0 = Var("f", nat0_ty)
_x_n0 = Var("x", nat0_ty)


# |- !f1 f2 g. is_mp f1 f2 g = (f2 = Imp_f f1 g).
IS_MP_DEF, IS_MP_AT = define_with_at(
    "is_mp",
    parse_type("nat0 -> nat0 -> nat0 -> bool"),
    "\\f1:nat0. \\f2:nat0. \\g:nat0. f2 = Imp_f f1 g",
)
is_mp = mk_const("is_mp", [])


from axioms import mk_exists  # noqa: E402 -- needed by the IS_GEN definition below


_is_gen_body = mk_exists(_x_n0, mk_eq(_g_n0, mk_app(Forall_f, _x_n0, _f_n0)))

# |- !f g. is_gen f g = (?x. g = Forall_f x f).
IS_GEN_DEF, IS_GEN_AT = define_with_at(
    "is_gen",
    parse_type("nat0 -> nat0 -> bool"),
    mk_abs(_f_n0, mk_abs(_g_n0, _is_gen_body)),
)
is_gen = mk_const("is_gen", [])


# ---------------------------------------------------------------------------
# Stage 2B (b) -- logical-axiom schema recognisers.
#
# Standard Hilbert axiomatisation (Mendelson, "Introduction to
# Mathematical Logic", §2.4, restricted to the connectives we have):
#
#   K-schema:  A -> (B -> A)
#   S-schema:  (A -> (B -> C)) -> ((A -> B) -> (A -> C))
#   N-schema:  (~B -> ~A) -> (A -> B)               (classical)
#   UI:        !x. F -> F[t/x]                       (universal inst.)
#   Vac:       F -> !x. F                            (vacuous gen.; x not free in F)
#   Refl:      t = t                                  (equality reflexivity)
#   Subst:     t1 = t2 -> F[t1/x] -> F[t2/x]          (equality substitution)
#
# Each schema is encoded as an existential predicate on a godelnum.
# All are sigma-1 (existential over wf-encoded objects + decidable
# checks), hence decidable and representable.
# ---------------------------------------------------------------------------


is_term = mk_const("is_term", [])
is_form = mk_const("is_form", [])
free_in = mk_const("free_in", [])
substitute = mk_const("substitute", [])


# Helpers used in several schemas.
_A_n0 = Var("A", nat0_ty)
_B_n0 = Var("B", nat0_ty)
_C_n0 = Var("C", nat0_ty)
_F_n0 = Var("F", nat0_ty)
_t_pf_n0 = Var("t", nat0_ty)
_t1_pf_n0 = Var("t1", nat0_ty)
_t2_pf_n0 = Var("t2", nat0_ty)
_x_pf_n0 = Var("x", nat0_ty)
_G_pf_n0 = Var("G", nat0_ty)


def _and_chain(props):
    from axioms import mk_and

    out = props[-1]
    for p_ in reversed(props[:-1]):
        out = mk_and(p_, out)
    return out


def _exists_chain(vars_, body):
    out = body
    for v in reversed(vars_):
        out = mk_exists(v, out)
    return out


def _isf(t):
    return mk_app(is_form, t)


def _ist(t):
    return mk_app(is_term, t)


# is_K(n) :<=> ?A B. is_form A /\ is_form B /\ n = A -> (B -> A).
_is_K_body = _exists_chain(
    [_A_n0, _B_n0],
    _and_chain(
        [
            _isf(_A_n0),
            _isf(_B_n0),
            mk_eq(_n_n0, mk_app(Imp_f, _A_n0, mk_app(Imp_f, _B_n0, _A_n0))),
        ]
    ),
)
IS_K_DEF, IS_K_AT = define_with_at(
    "is_K", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_K_body)
)
is_K = mk_const("is_K", [])


# is_S(n) :<=> ?A B C. is_form A /\ is_form B /\ is_form C /\
#                       n = (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
_is_S_body = _exists_chain(
    [_A_n0, _B_n0, _C_n0],
    _and_chain(
        [
            _isf(_A_n0),
            _isf(_B_n0),
            _isf(_C_n0),
            mk_eq(
                _n_n0,
                mk_app(
                    Imp_f,
                    mk_app(Imp_f, _A_n0, mk_app(Imp_f, _B_n0, _C_n0)),
                    mk_app(
                        Imp_f, mk_app(Imp_f, _A_n0, _B_n0), mk_app(Imp_f, _A_n0, _C_n0)
                    ),
                ),
            ),
        ]
    ),
)
IS_S_DEF, IS_S_AT = define_with_at(
    "is_S", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_S_body)
)
is_S = mk_const("is_S", [])


# is_N(n) :<=> ?A B. is_form A /\ is_form B /\
#                     n = (~B -> ~A) -> (A -> B).
_is_N_body = _exists_chain(
    [_A_n0, _B_n0],
    _and_chain(
        [
            _isf(_A_n0),
            _isf(_B_n0),
            mk_eq(
                _n_n0,
                mk_app(
                    Imp_f,
                    mk_app(Imp_f, mk_app(Not_f, _B_n0), mk_app(Not_f, _A_n0)),
                    mk_app(Imp_f, _A_n0, _B_n0),
                ),
            ),
        ]
    ),
)
IS_N_DEF, IS_N_AT = define_with_at(
    "is_N", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_N_body)
)
is_N = mk_const("is_N", [])


# is_UI(n) :<=> ?x F t. is_form F /\ is_term t /\
#                       n = Imp_f (Forall_f x F) (substitute F t x).
_is_UI_body = _exists_chain(
    [_x_pf_n0, _F_n0, _t_pf_n0],
    _and_chain(
        [
            _isf(_F_n0),
            _ist(_t_pf_n0),
            mk_eq(
                _n_n0,
                mk_app(
                    Imp_f,
                    mk_app(Forall_f, _x_pf_n0, _F_n0),
                    mk_app(substitute, _F_n0, _t_pf_n0, _x_pf_n0),
                ),
            ),
        ]
    ),
)
IS_UI_DEF, IS_UI_AT = define_with_at(
    "is_UI", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_UI_body)
)
is_UI = mk_const("is_UI", [])


# is_Vac(n) :<=> ?x F. is_form F /\ ~(free_in F x) /\
#                      n = Imp_f F (Forall_f x F).
from axioms import mk_not as _mk_not  # noqa: E402 -- aliased for the is_Vac definition below

_is_Vac_body = _exists_chain(
    [_x_pf_n0, _F_n0],
    _and_chain(
        [
            _isf(_F_n0),
            _mk_not(mk_app(free_in, _F_n0, _x_pf_n0)),
            mk_eq(_n_n0, mk_app(Imp_f, _F_n0, mk_app(Forall_f, _x_pf_n0, _F_n0))),
        ]
    ),
)
IS_VAC_DEF, IS_VAC_AT = define_with_at(
    "is_Vac", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Vac_body)
)
is_Vac = mk_const("is_Vac", [])


# is_FaImp(n) :<=> ?x F G. is_form F /\ is_form G /\ ~(free_in F x) /\
#                          n = Imp_f (Forall_f x (Imp_f F G))
#                                    (Imp_f F (Forall_f x G)).
#
# Mendelson's K6 / "generalisation in implication" axiom: when ``x`` is
# not free in ``F``, the universal binder distributes through the
# implication's consequent. Strictly stronger than Świerczkowski's
# K/S/N/UI/Vac/Refl/Subst (a Hilbert-Bernays meta-theorem there); we
# adopt it as a kernel axiom so PROV_HF_DT_GEN -- and therefore
# DTChain.gen -- becomes unconditionally proved.
_is_FaImp_body = _exists_chain(
    [_x_pf_n0, _F_n0, _G_pf_n0],
    _and_chain(
        [
            _isf(_F_n0),
            _isf(_G_pf_n0),
            _mk_not(mk_app(free_in, _F_n0, _x_pf_n0)),
            mk_eq(
                _n_n0,
                mk_app(
                    Imp_f,
                    mk_app(Forall_f, _x_pf_n0, mk_app(Imp_f, _F_n0, _G_pf_n0)),
                    mk_app(
                        Imp_f,
                        _F_n0,
                        mk_app(Forall_f, _x_pf_n0, _G_pf_n0),
                    ),
                ),
            ),
        ]
    ),
)
IS_FaImp_DEF, IS_FaImp_AT = define_with_at(
    "is_FaImp", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_FaImp_body)
)
is_FaImp = mk_const("is_FaImp", [])


# is_Refl(n) :<=> ?t. is_term t /\ n = Eq_f t t.
_is_Refl_body = _exists_chain(
    [_t_pf_n0],
    _and_chain(
        [
            _ist(_t_pf_n0),
            mk_eq(_n_n0, mk_app(Eq_f, _t_pf_n0, _t_pf_n0)),
        ]
    ),
)
IS_REFL_DEF, IS_REFL_AT = define_with_at(
    "is_Refl", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Refl_body)
)
is_Refl = mk_const("is_Refl", [])


# is_Subst(n) :<=> ?x F t1 t2. is_form F /\ is_term t1 /\ is_term t2 /\
#                              n = Imp_f (Eq_f t1 t2)
#                                        (Imp_f (substitute F t1 x)
#                                               (substitute F t2 x)).
_is_Subst_body = _exists_chain(
    [_x_pf_n0, _F_n0, _t1_pf_n0, _t2_pf_n0],
    _and_chain(
        [
            _isf(_F_n0),
            _ist(_t1_pf_n0),
            _ist(_t2_pf_n0),
            mk_eq(
                _n_n0,
                mk_app(
                    Imp_f,
                    mk_app(Eq_f, _t1_pf_n0, _t2_pf_n0),
                    mk_app(
                        Imp_f,
                        mk_app(substitute, _F_n0, _t1_pf_n0, _x_pf_n0),
                        mk_app(substitute, _F_n0, _t2_pf_n0, _x_pf_n0),
                    ),
                ),
            ),
        ]
    ),
)
IS_SUBST_DEF, IS_SUBST_AT = define_with_at(
    "is_Subst", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Subst_body)
)
is_Subst = mk_const("is_Subst", [])


# ---------------------------------------------------------------------------
# Stage 2B (c) -- is_logical_axiom and is_axiom.
#
#   is_logical_axiom(n)  :<=>  is_K n \/ is_S n \/ is_N n \/
#                              is_UI n \/ is_Vac n \/
#                              is_Refl n \/ is_Subst n \/ is_FaImp n.
#
#   is_axiom(n)          :<=>  is_hf_axiom n \/ is_logical_axiom n.
#
# Slot indices consumed by ``hf_logic._prov_of_logical``:
#   0=K, 1=S, 2=N, 3=UI, 4=Vac, 5=Refl, 6=Subst, 7=FaImp.
# ---------------------------------------------------------------------------


_is_logical_body = _disj_chain(
    [
        mk_app(is_K, _n_n0),
        mk_app(is_S, _n_n0),
        mk_app(is_N, _n_n0),
        mk_app(is_UI, _n_n0),
        mk_app(is_Vac, _n_n0),
        mk_app(is_Refl, _n_n0),
        mk_app(is_Subst, _n_n0),
        mk_app(is_FaImp, _n_n0),
    ]
)
IS_LOGICAL_AXIOM_DEF, IS_LOGICAL_AXIOM_AT = define_with_at(
    "is_logical_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _is_logical_body),
)
is_logical_axiom = mk_const("is_logical_axiom", [])


_is_axiom_body = mk_or(mk_app(is_hf_axiom, _n_n0), mk_app(is_logical_axiom, _n_n0))
IS_AXIOM_DEF, IS_AXIOM_AT = define_with_at(
    "is_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _is_axiom_body),
)
is_axiom = mk_const("is_axiom", [])


# ---------------------------------------------------------------------------
# Stage 2B (e) -- Prov_HF is defined in hf_repr_core.py.
#
#   Prov_HF n  :<=>  ?P. Proof_HF_set P n.
#
# The closure lemmas ``PROV_HF_AXIOM``, ``PROV_HF_MP``, and
# ``PROV_HF_GEN`` are derived in ``hf_repr_core.py`` from the set-native
# proof-object constructors.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2 (a) -- variable-index conventions.")
    print("    VAR_X_DEF      :", pp_thm(VAR_X_DEF))
    print("    VAR_Y_DEF      :", pp_thm(VAR_Y_DEF))
    print("    VAR_Z_DEF      :", pp_thm(VAR_Z_DEF))
    print()
    print("Stage 2 (b) -- the five HF axioms (encoded).")
    for name, _ax, def_th in HF_AXIOMS:
        print(f"    {name:<10} :", pp_thm(def_th))
    print()
    print("Stage 2 (c) -- is_hf_axiom recogniser.")
    print("    IS_HF_AXIOM_DEF :", pp_thm(IS_HF_AXIOM_DEF))
    print("    IS_HF_AXIOM_AT  :", pp_thm(IS_HF_AXIOM_AT))
    print("    Each axiom is recognised:")
    for name, _, _ in HF_AXIOMS:
        print(f"      is_hf_axiom {name:<10}:", pp_thm(IS_HF_AXIOM_HOLDS[name]))
    print()
    print("Stage 2B (a) -- modus ponens / generalisation predicates.")
    print("    IS_MP_AT       :", pp_thm(IS_MP_AT))
    print("    IS_GEN_AT      :", pp_thm(IS_GEN_AT))
    print()
    print("Stage 2B (b) -- logical-axiom schemas.")
    print("    IS_K_AT        :", pp_thm(IS_K_AT))
    print("    IS_S_AT        :", pp_thm(IS_S_AT))
    print("    IS_N_AT        :", pp_thm(IS_N_AT))
    print("    IS_UI_AT       :", pp_thm(IS_UI_AT))
    print("    IS_VAC_AT      :", pp_thm(IS_VAC_AT))
    print("    IS_REFL_AT     :", pp_thm(IS_REFL_AT))
    print("    IS_SUBST_AT    :", pp_thm(IS_SUBST_AT))
    print("    IS_FaImp_AT    :", pp_thm(IS_FaImp_AT))
    print()
    print("Stage 2B (c) -- is_logical_axiom and is_axiom.")
    print("    IS_LOGICAL_AXIOM_AT :", pp_thm(IS_LOGICAL_AXIOM_AT))
    print("    IS_AXIOM_AT         :", pp_thm(IS_AXIOM_AT))
    print()
    print("Stage 2B (d) -- Prov_HF is defined in hf_repr_core.py via ?P. Proof_HF_set P n.")
