# ---------------------------------------------------------------------------
# Stage 2 -- the Q proof system.
# ---------------------------------------------------------------------------
#
# Logical axioms (shared with any first-order Hilbert system):
#   * Propositional tautologies (any standard finite axiomatisation).
#   * Quantifier axioms: !x. F[x] -> F[t/x]; F -> !x. F (x not free).
#   * Equality: t = t; substitution under equality.
#
# Non-logical axioms (Robinson Q, seven closed formulas):
#   Q1.  !x.    ~(Succ x = Zero)
#   Q2.  !x y.  Succ x = Succ y  ->  x = y
#   Q3.  !x.    ~(x = Zero)  ->  ?y. x = Succ y
#   Q4.  !x.    Plus x Zero = x
#   Q5.  !x y.  Plus x (Succ y) = Succ (Plus x y)
#   Q6.  !x.    Times x Zero = Zero
#   Q7.  !x y.  Times x (Succ y) = Plus (Times x y) x
#
# Rules: modus ponens; generalization.
#
# This file implements Stage 2A:
#   * List encoding on nat0 (proofs are lists of formula godelnums).
#   * The seven Q axioms as concrete encoded nat0 terms.
#   * ``is_q_axiom``: decidable recogniser for the seven Q axioms.
#
# Stage 2B (deferred):
#   * Logical-axiom schema recogniser (~80 lines: pattern match on
#     each propositional / quantifier / equality schema).
#   * ``is_axiom = is_q_axiom \/ is_logical_axiom``.
#   * Modus-ponens / generalization checkers on godelnums.
#   * ``Proof_Q(p, n)`` via well-founded recursion on list length.
#   * ``Prov_Q(n) := ?p. Proof_Q(p, n)``.
#   * Closure rules: |- Prov_Q F /\ Prov_Q (F -> G) ==> Prov_Q G, etc.

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const, mk_app, mk_eq
from parser import define, parse_type
from nat0 import nat0_ty, ZERO, mk_suc0
from hf_sets import (
    Pair_ord,
    PAIR_ORD_INJ,
)
from proof import proof
from tactics import (
    SPECL, GEN, GENL, SYM, MP, CONJUNCT1, CONJUNCT2,
    AP_THM, BETA_CONV, TRANS, DISJ1, DISJ2, EQ_MP,
)
from basics import mk_abs, rand
from axioms import mk_or
from fusion import REFL
from q_syntax import (
    Zero_t, Succ_t, Var_t, Plus_t, Times_t,
    Eq_f, Not_f, Imp_f, Forall_f,
    SUCC_T_AT, VAR_T_AT, PLUS_T_AT, TIMES_T_AT,
    EQ_F_AT, NOT_F_AT, IMP_F_AT, FORALL_F_AT,
)


# ---------------------------------------------------------------------------
# List encoding on nat0.
#
# A list of nat0s is itself a nat0:
#
#   nil_l         :=  0                                   (= Empty in HF)
#   cons_l h t    :=  Pair_ord (SUC0 0) (Pair_ord h t)
#
# The leading ``SUC0 0`` tag distinguishes a non-empty list from the
# empty list (which is just ``0``); the inner ``Pair_ord h t`` carries
# the head and tail. PAIR_ORD_INJ gives projection / injectivity for
# free.
#
# We do not need decidable ``is_cons`` at this stage -- the list shape
# is fixed in every position where lists appear (proof = non-empty list
# of formula godelnums).
# ---------------------------------------------------------------------------


_h_n0 = Var("h", nat0_ty)
_t_n0 = Var("t", nat0_ty)
_h1_n0 = Var("h1", nat0_ty)
_t1_n0 = Var("t1", nat0_ty)
_h2_n0 = Var("h2", nat0_ty)
_t2_n0 = Var("t2", nat0_ty)


NIL_L_DEF = define("nil_l", parse_type("nat0"), "0")
nil_l = mk_const("nil_l", [])

CONS_L_DEF = define(
    "cons_l",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\h:nat0. \\t:nat0. Pair_ord (SUC0 0) (Pair_ord h t)",
)
cons_l = mk_const("cons_l", [])


def _at1(def_th, x):
    th = AP_THM(def_th, x)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GEN(x, th)


def _at2(def_th, x, y):
    th_x = AP_THM(def_th, x)
    th_x = TRANS(th_x, BETA_CONV(rand(th_x._concl)))
    th_xy = AP_THM(th_x, y)
    th_xy = TRANS(th_xy, BETA_CONV(rand(th_xy._concl)))
    return GENL([x, y], th_xy)


# Pointwise: |- !h t. cons_l h t = Pair_ord (SUC0 0) (Pair_ord h t).
CONS_L_AT = _at2(CONS_L_DEF, _h_n0, _t_n0)


# Injectivity:  |- !h1 t1 h2 t2. cons_l h1 t1 = cons_l h2 t2 ==>
#                                 h1 = h2 /\ t1 = t2.
@proof
def CONS_L_INJ(p):
    p.goal(
        "!h1 t1 h2 t2. cons_l h1 t1 = cons_l h2 t2 ==> "
        "(h1 = h2 /\\ t1 = t2)"
    )
    p.fix("h1 t1 h2 t2")
    p.assume("h: cons_l h1 t1 = cons_l h2 t2")
    cons_at_1 = SPECL([p._parse("h1"), p._parse("t1")], CONS_L_AT)
    cons_at_2 = SPECL([p._parse("h2"), p._parse("t2")], CONS_L_AT)
    p.have(
        "h_outer: Pair_ord (SUC0 0) (Pair_ord h1 t1) = "
        "Pair_ord (SUC0 0) (Pair_ord h2 t2)"
    ).by_rewrite_of("h", [cons_at_1, cons_at_2])
    p.have(
        "h_inner_conj: SUC0 0 = SUC0 0 /\\ Pair_ord h1 t1 = Pair_ord h2 t2"
    ).by(PAIR_ORD_INJ, "SUC0 0", "Pair_ord h1 t1", "SUC0 0", "Pair_ord h2 t2",
         "h_outer")
    p.split("h_inner_conj", "(_, h_inner)")
    p.thus("h1 = h2 /\\ t1 = t2").by(
        PAIR_ORD_INJ, "h1", "t1", "h2", "t2", "h_inner"
    )


# Disjointness with nil:  |- !h t. ~(cons_l h t = nil_l).
# Proof: cons_l h t = Pair_ord (SUC0 0) ..., and we need
# ~(Pair_ord (SUC0 0) (Pair_ord h t) = 0). The right way is via
# membership: Pair_ord a b is non-empty (contains Singleton a), but 0
# is empty. Defer the discharge until needed -- the fact is implied by
# nat0 inhabitation arguments at Pair_ord, parallel to the
# ``CTOR_NEQ_ZERO`` proofs in q_syntax.py.
#
# (Stage 2 itself does not consume cons_l =/= nil_l until the proof-
# checker is wired up; we list the lemma here as a TODO marker.)


# ---------------------------------------------------------------------------
# Variable-index conventions for the Q axioms.
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


# ---------------------------------------------------------------------------
# The seven Q axioms as concrete encoded nat0 terms.
#
# Each axiom is a closed Q sentence; its godelnum is a closed nat0
# numeral (a deeply nested ``Pair_ord``-tree). We define each as a
# named constant so downstream code can refer to them by name and the
# proof-checker has small concrete syntactic targets.
# ---------------------------------------------------------------------------


# Q1.  !x. ~(Succ x = Zero)
Q1_AXIOM_DEF = define(
    "Q1_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Not_f (Eq_f (Succ_t var_x) Zero_t))",
)
Q1_axiom = mk_const("Q1_axiom", [])


# Q2.  !x y. Succ x = Succ y -> x = y
Q2_AXIOM_DEF = define(
    "Q2_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) "
    "(Imp_f (Eq_f (Succ_t var_x) (Succ_t var_y)) (Eq_f var_x var_y)))",
)
Q2_axiom = mk_const("Q2_axiom", [])


# Q3.  !x. ~(x = Zero) -> ?y. x = Succ y
# Encoding: !x. ~(x = 0) -> ~!y. ~(x = Succ y)
# (Existence ``?y. body`` is sugar for ``~!y. ~body``; we expand
# inline since q_syntax.py does not commit to a desugaring layer.)
Q3_AXIOM_DEF = define(
    "Q3_axiom",
    parse_type("nat0"),
    "Forall_f 0 "
    "(Imp_f (Not_f (Eq_f var_x Zero_t)) "
    "(Not_f (Forall_f (SUC0 0) "
    "(Not_f (Eq_f var_x (Succ_t var_y))))))",
)
Q3_axiom = mk_const("Q3_axiom", [])


# Q4.  !x. Plus x Zero = x
Q4_AXIOM_DEF = define(
    "Q4_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Eq_f (Plus_t var_x Zero_t) var_x)",
)
Q4_axiom = mk_const("Q4_axiom", [])


# Q5.  !x y. Plus x (Succ y) = Succ (Plus x y)
Q5_AXIOM_DEF = define(
    "Q5_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) "
    "(Eq_f (Plus_t var_x (Succ_t var_y)) (Succ_t (Plus_t var_x var_y))))",
)
Q5_axiom = mk_const("Q5_axiom", [])


# Q6.  !x. Times x Zero = Zero
Q6_AXIOM_DEF = define(
    "Q6_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Eq_f (Times_t var_x Zero_t) Zero_t)",
)
Q6_axiom = mk_const("Q6_axiom", [])


# Q7.  !x y. Times x (Succ y) = Plus (Times x y) x
Q7_AXIOM_DEF = define(
    "Q7_axiom",
    parse_type("nat0"),
    "Forall_f 0 (Forall_f (SUC0 0) "
    "(Eq_f (Times_t var_x (Succ_t var_y)) "
    "(Plus_t (Times_t var_x var_y) var_x)))",
)
Q7_axiom = mk_const("Q7_axiom", [])


Q_AXIOMS = [
    ("Q1_axiom", Q1_axiom, Q1_AXIOM_DEF),
    ("Q2_axiom", Q2_axiom, Q2_AXIOM_DEF),
    ("Q3_axiom", Q3_axiom, Q3_AXIOM_DEF),
    ("Q4_axiom", Q4_axiom, Q4_AXIOM_DEF),
    ("Q5_axiom", Q5_axiom, Q5_AXIOM_DEF),
    ("Q6_axiom", Q6_axiom, Q6_AXIOM_DEF),
    ("Q7_axiom", Q7_axiom, Q7_AXIOM_DEF),
]


# ---------------------------------------------------------------------------
# is_q_axiom -- decidable recogniser for the seven Q axioms.
#
#   is_q_axiom n  :<=>  n = Q1_axiom \/ n = Q2_axiom \/ ... \/ n = Q7_axiom
#
# Closed under no recursion -- it is just a 7-fold disjunction of
# equalities with closed nat0 numerals. Decidable trivially (each
# disjunct is decidable equality between concrete nat0s).
# ---------------------------------------------------------------------------


_n_n0 = Var("n", nat0_ty)


def _disj_chain(eqs):
    """Build a right-associated disjunction ``eqs[0] \\/ eqs[1] \\/ ...``."""
    out = eqs[-1]
    for e in reversed(eqs[:-1]):
        out = mk_or(e, out)
    return out


_q_axiom_disj = _disj_chain([
    mk_eq(_n_n0, Q1_axiom),
    mk_eq(_n_n0, Q2_axiom),
    mk_eq(_n_n0, Q3_axiom),
    mk_eq(_n_n0, Q4_axiom),
    mk_eq(_n_n0, Q5_axiom),
    mk_eq(_n_n0, Q6_axiom),
    mk_eq(_n_n0, Q7_axiom),
])

IS_Q_AXIOM_DEF = define(
    "is_q_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _q_axiom_disj),
)
is_q_axiom = mk_const("is_q_axiom", [])


# Pointwise:
#  |- !n. is_q_axiom n =
#         (n = Q1_axiom \/ n = Q2_axiom \/ ... \/ n = Q7_axiom).
IS_Q_AXIOM_AT = _at1(IS_Q_AXIOM_DEF, _n_n0)


# Each Q axiom is itself a Q axiom: |- is_q_axiom Q{i}_axiom.
# Use direct disjunction-introduction.
def _prove_q_axiom_holds(name, axiom_const, position):
    """|- is_q_axiom name_axiom -- discharge by DISJ at position.

    ``position`` is 1-indexed (1..7).
    """
    eq_chain = [mk_eq(axiom_const, ax_const) for (_, ax_const, _) in Q_AXIOMS]
    idx = position - 1
    th = REFL(axiom_const)  # |- axiom_const = axiom_const
    if idx < len(eq_chain) - 1:
        right_tail = _disj_chain(eq_chain[idx + 1:])
        th = DISJ1(th, right_tail)
    for j in range(idx - 1, -1, -1):
        th = DISJ2(eq_chain[j], th)
    spec = SPECL([axiom_const], IS_Q_AXIOM_AT)  # |- is_q_axiom ax = body
    return EQ_MP(SYM(spec), th)


IS_Q_AXIOM_HOLDS = {
    name: _prove_q_axiom_holds(name, ax_const, i + 1)
    for i, (name, ax_const, _) in enumerate(Q_AXIOMS)
}


# ---------------------------------------------------------------------------
# Stage 2B (deferred) -- sketch.
# ---------------------------------------------------------------------------
#
# Logical-axiom recogniser. Standard Hilbert axiomatization (Mendelson):
#
#   K-schema:  A -> (B -> A)
#   S-schema:  (A -> (B -> C)) -> ((A -> B) -> (A -> C))
#   N-schema:  (~B -> ~A) -> (A -> B)            (classical negation)
#   Q-axiom:   !x. F -> F[t/x]                   (universal instantiation)
#   Q-vacuous: F -> !x. F                         (when x not free in F)
#   E1:        t = t                              (reflexivity)
#   E2:        t1 = t2 -> phi[t1] -> phi[t2]      (substitution)
#
# Each schema becomes an existential predicate on a candidate godelnum.
# E.g.:
#
#   is_K(n)  :<=>  ?A B. is_form A /\ is_form B /\
#                        n = Imp_f A (Imp_f B A)
#
# These are all sigma-1, hence decidable and representable.
#
# Modus ponens / generalisation:
#
#   is_mp(F1, F2, G)  :<=>  F2 = Imp_f F1 G
#   is_gen(F, G)      :<=>  ?x. G = Forall_f x F
#
# Proof_Q encoding:
#
#   Proof_Q(p, target)  :<=>
#     ?lst. p = lst /\ lst is non-empty /\
#           head(lst) = target /\
#           every prefix is a valid step:
#             at each i in 0..len(lst)-1, lst[i] is either an axiom
#             or follows from earlier lines by MP or Gen.
#
# Implementation via well-founded recursion on list length (list length
# = sum of nat0_lt-decreasing tail). The MONO-style obligation is
# straightforward: the body inspects only finitely many earlier list
# entries, each strictly smaller in the tail-of-list well-founded order.
#
# Prov_Q(n)  :<=>  ?p. Proof_Q(p, n).
#
# Closure rules (HOL theorems):
#   |- Prov_Q F /\ Prov_Q (Imp_f F G)  ==>  Prov_Q G
#   |- Prov_Q F  ==>  Prov_Q (Forall_f x F)
#
# Both are "extend the list" arguments: take the witnessing proof of the
# antecedent, append one MP/Gen line. ~30 lines each.


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2 (a) -- list encoding on nat0.")
    print("    NIL_L_DEF      :", pp_thm(NIL_L_DEF))
    print("    CONS_L_DEF     :", pp_thm(CONS_L_DEF))
    print("    CONS_L_AT      :", pp_thm(CONS_L_AT))
    print("    CONS_L_INJ     :", pp_thm(CONS_L_INJ))
    print()
    print("Stage 2 (b) -- variable-index conventions.")
    print("    VAR_X_DEF      :", pp_thm(VAR_X_DEF))
    print("    VAR_Y_DEF      :", pp_thm(VAR_Y_DEF))
    print()
    print("Stage 2 (c) -- the seven Q axioms (encoded).")
    for name, _ax, def_th in Q_AXIOMS:
        print(f"    {name:<10} :", pp_thm(def_th))
    print()
    print("Stage 2 (d) -- is_q_axiom recogniser.")
    print("    IS_Q_AXIOM_DEF :", pp_thm(IS_Q_AXIOM_DEF))
    print("    IS_Q_AXIOM_AT  :", pp_thm(IS_Q_AXIOM_AT))
    print("    Each axiom is recognised:")
    for name, _, _ in Q_AXIOMS:
        print(f"      is_q_axiom {name:<10}:", pp_thm(IS_Q_AXIOM_HOLDS[name]))
