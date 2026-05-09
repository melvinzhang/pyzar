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
# Stage 2A (foundations):
#   * List encoding on nat0 (proofs are lists of formula godelnums).
#   * The seven Q axioms as concrete encoded nat0 terms.
#   * ``is_q_axiom``: decidable recogniser for the seven Q axioms.
#
# Stage 2B (proof system):
#   * ``is_mp``, ``is_gen``: modus-ponens / generalisation predicates
#     on godelnums.
#   * Seven logical-axiom schemas as sigma_1 predicates: ``is_K``,
#     ``is_S``, ``is_N`` (Mendelson propositional); ``is_UI``,
#     ``is_Vac`` (quantifier; ``is_Vac`` carries a ``free_in`` side
#     condition); ``is_Refl``, ``is_Subst`` (equality). The
#     quantifier and equality schemas reuse ``substitute`` and
#     ``free_in`` from ``q_syntax``.
#   * ``is_logical_axiom`` (disjunction over the seven schemas) and
#     ``is_axiom = is_q_axiom \/ is_logical_axiom``.
#   * ``NAT0_LT_CONS_L_HEAD`` / ``NAT0_LT_CONS_L_TAIL``: list size
#     lemmas needed for any future well-founded recursion on lists.
#   * ``Prov_Q``: provability predicate, defined as the impredicative
#     intersection of all sets closed under the inference rules:
#         Prov_Q n  :<=>  !P:nat0->bool.
#                          ( (!m. is_axiom m ==> P m)
#                          /\ (!f g. P f /\ P (Imp_f f g) ==> P g)
#                          /\ (!f x. P f ==> P (Forall_f x f)) )
#                          ==> P n.
#   * Closure rules:
#         |- !n. is_axiom n ==> Prov_Q n.                  (PROV_Q_AXIOM)
#         |- !f g. Prov_Q f /\ Prov_Q (Imp_f f g)
#                  ==> Prov_Q g.                           (PROV_Q_MP)
#         |- !f x. Prov_Q f ==> Prov_Q (Forall_f x f).     (PROV_Q_GEN)
#
# Design note -- why ``Prov_Q`` via impredicative intersection rather
# than the textbook ``?p. Proof_Q(p, n)``:
#
# The ``godel_first.py`` blueprint specifies ``Prov_Q(n) :<=> ?p.
# Proof_Q(p, n)`` where ``Proof_Q`` is the list-based proof checker.
# In HOL the two definitions are provably equivalent (Knaster-Tarski:
# the impredicative intersection is the least fixed point of the
# closure operator, which agrees with the inductively generated set
# of provable godelnums). We pick the impredicative form here because:
#
#   (1) The closure rules (axiom inclusion, MP, generalisation) drop
#       out by direct specialisation -- no recursion, no MONO.
#   (2) A list-based ``Proof_Q`` would require ``mem_l`` (list
#       membership) defined via ``define_wf_lt``, which carries a
#       non-trivial MONO obligation under existential binders -- the
#       per-(h, t) iff has to use ``NAT0_LT_CONS_L_TAIL`` to discharge
#       the recursive call after CHOOSE'ing the cons witness.
#   (3) Stage 4 (diagonal lemma) and Stage 5 (the main incompleteness
#       theorem) only consume the closure rules and ``PROV_Q_AT``; they
#       never inspect an explicit proof witness.
#
# A list-based ``Proof_Q`` *is* needed in Stage 3 for representability
# -- the diagonal lemma's ``Prov_Q_internal`` formula must internalise
# explicit proofs into Q's own language. We build it there against
# this ``Prov_Q``, not as a defining predicate.

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const, mk_app, mk_eq
from parser import define, parse_type
from nat0 import nat0_ty
from hf_sets import (
    PAIR_ORD_INJ,
)
from proof import proof
from tactics import (
    SPECL,
    GEN,
    GENL,
    SYM,
    AP_THM,
    BETA_CONV,
    TRANS,
    DISJ1,
    DISJ2,
    EQ_MP,
)
from basics import mk_abs, rand
from axioms import mk_or
from fusion import REFL
from q_syntax import (
    Eq_f,
    Not_f,
    Imp_f,
    Forall_f,
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
    p.goal("!h1 t1 h2 t2. cons_l h1 t1 = cons_l h2 t2 ==> (h1 = h2 /\\ t1 = t2)")
    p.fix("h1 t1 h2 t2")
    p.assume("h: cons_l h1 t1 = cons_l h2 t2")
    cons_at_1 = SPECL([p._parse("h1"), p._parse("t1")], CONS_L_AT)
    cons_at_2 = SPECL([p._parse("h2"), p._parse("t2")], CONS_L_AT)
    p.have(
        "h_outer: Pair_ord (SUC0 0) (Pair_ord h1 t1) = "
        "Pair_ord (SUC0 0) (Pair_ord h2 t2)"
    ).by_rewrite_of("h", [cons_at_1, cons_at_2])
    p.have("h_inner_conj: SUC0 0 = SUC0 0 /\\ Pair_ord h1 t1 = Pair_ord h2 t2").by(
        PAIR_ORD_INJ, "SUC0 0", "Pair_ord h1 t1", "SUC0 0", "Pair_ord h2 t2", "h_outer"
    )
    p.split("h_inner_conj", "(_, h_inner)")
    p.thus("h1 = h2 /\\ t1 = t2").by(PAIR_ORD_INJ, "h1", "t1", "h2", "t2", "h_inner")


# Disjointness with nil:  |- !h t. ~(cons_l h t = nil_l).
#
# Direct: cons_l h t = Pair_ord (SUC0 0) (Pair_ord h t) and nil_l = 0;
# Pair_ord _ _ != 0 from ``_NEQ_PAIR_ORD_ZERO`` (q_syntax).


from q_syntax import _NEQ_PAIR_ORD_ZERO  # noqa: E402 -- imported just before CONS_L_NEQ_NIL


@proof
def CONS_L_NEQ_NIL(p):
    """|- !h t. ~(cons_l h t = nil_l)."""
    p.goal("!h t. ~(cons_l h t = nil_l)")
    p.fix("h t")
    cons_at_ht = SPECL([p._parse("h"), p._parse("t")], CONS_L_AT)
    with p.suppose("h_eq: cons_l h t = nil_l"):
        p.have("h_po: Pair_ord (SUC0 0) (Pair_ord h t) = 0").by_rewrite_of(
            "h_eq", [cons_at_ht, NIL_L_DEF]
        )
        p.have("h_neg: ~(Pair_ord (SUC0 0) (Pair_ord h t) = 0)").by(
            _NEQ_PAIR_ORD_ZERO, "SUC0 0", "Pair_ord h t"
        )
        p.absurd().by_conj("h_neg", "h_po")


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


_q_axiom_disj = _disj_chain(
    [
        mk_eq(_n_n0, Q1_axiom),
        mk_eq(_n_n0, Q2_axiom),
        mk_eq(_n_n0, Q3_axiom),
        mk_eq(_n_n0, Q4_axiom),
        mk_eq(_n_n0, Q5_axiom),
        mk_eq(_n_n0, Q6_axiom),
        mk_eq(_n_n0, Q7_axiom),
    ]
)

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
        right_tail = _disj_chain(eq_chain[idx + 1 :])
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


IS_MP_DEF = define(
    "is_mp",
    parse_type("nat0 -> nat0 -> nat0 -> bool"),
    "\\f1:nat0. \\f2:nat0. \\g:nat0. f2 = Imp_f f1 g",
)
is_mp = mk_const("is_mp", [])


def _at3(def_th, x, y, z):
    th = AP_THM(def_th, x)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    th = AP_THM(th, y)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    th = AP_THM(th, z)
    th = TRANS(th, BETA_CONV(rand(th._concl)))
    return GENL([x, y, z], th)


# |- !f1 f2 g. is_mp f1 f2 g = (f2 = Imp_f f1 g).
IS_MP_AT = _at3(IS_MP_DEF, _f1_n0, _f2_n0, _g_n0)


from axioms import mk_exists  # noqa: E402 -- needed by the IS_GEN definition below


_is_gen_body = mk_exists(_x_n0, mk_eq(_g_n0, mk_app(Forall_f, _x_n0, _f_n0)))

IS_GEN_DEF = define(
    "is_gen",
    parse_type("nat0 -> nat0 -> bool"),
    mk_abs(_f_n0, mk_abs(_g_n0, _is_gen_body)),
)
is_gen = mk_const("is_gen", [])


# |- !f g. is_gen f g = (?x. g = Forall_f x f).
IS_GEN_AT = _at2(IS_GEN_DEF, _f_n0, _g_n0)


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
IS_K_DEF = define("is_K", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_K_body))
is_K = mk_const("is_K", [])
IS_K_AT = _at1(IS_K_DEF, _n_n0)


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
IS_S_DEF = define("is_S", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_S_body))
is_S = mk_const("is_S", [])
IS_S_AT = _at1(IS_S_DEF, _n_n0)


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
IS_N_DEF = define("is_N", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_N_body))
is_N = mk_const("is_N", [])
IS_N_AT = _at1(IS_N_DEF, _n_n0)


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
IS_UI_DEF = define("is_UI", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_UI_body))
is_UI = mk_const("is_UI", [])
IS_UI_AT = _at1(IS_UI_DEF, _n_n0)


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
IS_VAC_DEF = define("is_Vac", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Vac_body))
is_Vac = mk_const("is_Vac", [])
IS_VAC_AT = _at1(IS_VAC_DEF, _n_n0)


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
IS_REFL_DEF = define(
    "is_Refl", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Refl_body)
)
is_Refl = mk_const("is_Refl", [])
IS_REFL_AT = _at1(IS_REFL_DEF, _n_n0)


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
IS_SUBST_DEF = define(
    "is_Subst", parse_type("nat0 -> bool"), mk_abs(_n_n0, _is_Subst_body)
)
is_Subst = mk_const("is_Subst", [])
IS_SUBST_AT = _at1(IS_SUBST_DEF, _n_n0)


# ---------------------------------------------------------------------------
# Stage 2B (c) -- is_logical_axiom and is_axiom.
#
#   is_logical_axiom(n)  :<=>  is_K n \/ is_S n \/ is_N n \/
#                              is_UI n \/ is_Vac n \/
#                              is_Refl n \/ is_Subst n.
#
#   is_axiom(n)          :<=>  is_q_axiom n \/ is_logical_axiom n.
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
    ]
)
IS_LOGICAL_AXIOM_DEF = define(
    "is_logical_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _is_logical_body),
)
is_logical_axiom = mk_const("is_logical_axiom", [])
IS_LOGICAL_AXIOM_AT = _at1(IS_LOGICAL_AXIOM_DEF, _n_n0)


_is_axiom_body = mk_or(mk_app(is_q_axiom, _n_n0), mk_app(is_logical_axiom, _n_n0))
IS_AXIOM_DEF = define(
    "is_axiom",
    parse_type("nat0 -> bool"),
    mk_abs(_n_n0, _is_axiom_body),
)
is_axiom = mk_const("is_axiom", [])
IS_AXIOM_AT = _at1(IS_AXIOM_DEF, _n_n0)


# ---------------------------------------------------------------------------
# Stage 2B (d) -- list size lemmas (head and tail strictly smaller than cons).
#
#   |- !h t. nat0_lt h (cons_l h t).
#   |- !h t. nat0_lt t (cons_l h t).
#
# Each is a two-layer descent through PAIR_ORD chained via NAT0_LT_TRANS.
# Same pattern as the constructor size lemmas in q_syntax.py.
# ---------------------------------------------------------------------------


from hf_sets import NAT0_LT_PAIR_ORD_L, NAT0_LT_PAIR_ORD_R  # noqa: E402 -- pair-order lemmas used right below
from nat0_order import NAT0_LT_TRANS  # noqa: E402 -- transitivity used right below


@proof
def NAT0_LT_CONS_L_HEAD(p):
    """|- !h t. nat0_lt h (cons_l h t)."""
    p.goal("!h t. nat0_lt h (cons_l h t)")
    p.fix("h t")
    cons_at_ht = SPECL([p._parse("h"), p._parse("t")], CONS_L_AT)
    p.have("h1: nat0_lt h (Pair_ord h t)").by(NAT0_LT_PAIR_ORD_L, "h", "t")
    p.have("h2: nat0_lt (Pair_ord h t) (Pair_ord (SUC0 0) (Pair_ord h t))").by(
        NAT0_LT_PAIR_ORD_R, "SUC0 0", "Pair_ord h t"
    )
    p.have("h3: nat0_lt h (Pair_ord (SUC0 0) (Pair_ord h t))").by(
        NAT0_LT_TRANS,
        "h",
        "Pair_ord h t",
        "Pair_ord (SUC0 0) (Pair_ord h t)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt h (cons_l h t)").by_rewrite_of("h3", [SYM(cons_at_ht)])


@proof
def NAT0_LT_CONS_L_TAIL(p):
    """|- !h t. nat0_lt t (cons_l h t)."""
    p.goal("!h t. nat0_lt t (cons_l h t)")
    p.fix("h t")
    cons_at_ht = SPECL([p._parse("h"), p._parse("t")], CONS_L_AT)
    p.have("h1: nat0_lt t (Pair_ord h t)").by(NAT0_LT_PAIR_ORD_R, "h", "t")
    p.have("h2: nat0_lt (Pair_ord h t) (Pair_ord (SUC0 0) (Pair_ord h t))").by(
        NAT0_LT_PAIR_ORD_R, "SUC0 0", "Pair_ord h t"
    )
    p.have("h3: nat0_lt t (Pair_ord (SUC0 0) (Pair_ord h t))").by(
        NAT0_LT_TRANS,
        "t",
        "Pair_ord h t",
        "Pair_ord (SUC0 0) (Pair_ord h t)",
        "h1",
        "h2",
    )
    p.thus("nat0_lt t (cons_l h t)").by_rewrite_of("h3", [SYM(cons_at_ht)])


# ---------------------------------------------------------------------------
# Stage 2B (e) -- Prov_Q is defined in q_repr.py.
#
#   Prov_Q n  :<=>  ?p. Proof_Q p n.
#
# The Sigma_1 form is the canonical one: it makes provability a witness
# predicate (every provable formula has an explicit list-of-formulas
# proof), and matches the shape that the diagonal lemma's internal
# provability formula will internalise. The closure lemmas
# ``PROV_Q_AXIOM``, ``PROV_Q_MP``, ``PROV_Q_GEN`` are derived from the
# explicit proof-list constructions ``AXIOM_HAS_PROOF``,
# ``MP_HAS_PROOF``, ``GEN_HAS_PROOF`` in q_repr.py.
#
# Historical note: an earlier draft defined ``Prov_Q`` via impredicative
# intersection (``!P. (closure clauses) ==> P n``) here in q_proof.py,
# before ``Proof_Q`` was available. That definition was equivalent
# (Knaster-Tarski) but redundant once the list-based ``Proof_Q`` was
# built. The audit found that nothing downstream used the impredicative
# shape essentially -- every consumer treats ``Prov_Q`` as a black box
# closed under axiom/MP/Gen -- so we collapsed to the single Sigma_1
# definition.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2 (a) -- list encoding on nat0.")
    print("    NIL_L_DEF      :", pp_thm(NIL_L_DEF))
    print("    CONS_L_DEF     :", pp_thm(CONS_L_DEF))
    print("    CONS_L_AT      :", pp_thm(CONS_L_AT))
    print("    CONS_L_INJ     :", pp_thm(CONS_L_INJ))
    print("    CONS_L_NEQ_NIL :", pp_thm(CONS_L_NEQ_NIL))
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
    print()
    print("Stage 2B (c) -- is_logical_axiom and is_axiom.")
    print("    IS_LOGICAL_AXIOM_AT :", pp_thm(IS_LOGICAL_AXIOM_AT))
    print("    IS_AXIOM_AT         :", pp_thm(IS_AXIOM_AT))
    print()
    print("Stage 2B (d) -- list size lemmas.")
    print("    NAT0_LT_CONS_L_HEAD :", pp_thm(NAT0_LT_CONS_L_HEAD))
    print("    NAT0_LT_CONS_L_TAIL :", pp_thm(NAT0_LT_CONS_L_TAIL))
    print()
    print("Stage 2B (e) -- Prov_Q is defined in q_repr.py via ?p. Proof_Q p n.")
