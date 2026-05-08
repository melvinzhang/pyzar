# ---------------------------------------------------------------------------
# Stage 3 -- representability of primitive recursive functions in Q.
# ---------------------------------------------------------------------------
#
# A predicate P : nat0 -> bool is *represented* in Q by a Q-formula
# F(x) -- with var_x as its sole free variable -- iff
#
#     |- !n. P n      ==> Prov_Q (substitute F (numeral n) var_x)
#     |- !n. ~ P n    ==> Prov_Q (Not_f (substitute F (numeral n) var_x))
#
# A function f : nat0 -> nat0 is represented by a Q-formula F(x, y) iff
#
#     |- !n. Prov_Q (substitute_2 F (numeral n) (numeral (f n)) var_x var_y)
#     |- !n. Prov_Q (Forall_f var_y
#                      (Imp_f (substitute_2 F (numeral n) y var_x var_y)
#                             (Eq_f y (numeral (f n))))).
#
# Theorem (representability). Every primitive recursive predicate /
# function on nat0 is representable in Q.
#
# This is the headline weak-arithmetic result. The standard proof
# (Boolos-Burgess-Jeffrey, "Computability and Logic" Ch. 16-17) goes:
#
#   * Constants, projections, successor, addition, multiplication --
#     direct unfolding against axioms Q4-Q7.
#   * Composition -- substitution; routine.
#   * Primitive recursion -- normally where induction enters. Q has no
#     induction schema, so we use Goedel's beta function: a fixed
#     ternary arithmetic predicate beta(a, b, i, y) such that for any
#     finite sequence (y_0, ..., y_k), there exist a, b with
#     beta(a, b, i, y_i) for each i. Construction via Chinese
#     remainder; existence is a numeric calculation that Q proves for
#     each numeral instance.
#
# In our HOL setting we don't need the full primitive recursion result
# -- we only need representability of three specific predicates:
#
#   (i)   ``Proof_Q``     (decidable, hence representable; the
#                          formula is an explicit bounded-quantifier
#                          encoding of the proof-checking procedure).
#   (ii)  ``substitute``  (primitive recursive on godelnums).
#   (iii) ``godelnum``    (degenerate -- just identity on encoded syntax;
#                          its numeral image is what matters).
#
# Each of these is several pages in textbook treatments. The slick HOL
# move is to define the representing formulas *by* the HOL definitions,
# transport through the bounded-quantifier translation, and then show
# by induction (in the *meta*theory; HOL has it) on syntactic
# complexity that Q proves the right characterisations. ~500 lines
# with the beta-function lemma factored out.
#
# (No saving here over PA: representability is exactly as hard with
# induction as without it; the beta-function trick was invented
# precisely so that the proof would not depend on induction. The
# saving over PA was at Stage 2.)
#
# ------------------------------------------------------------------
# Reconciliation with Stage 2's ``Prov_Q``:
# ------------------------------------------------------------------
#
# Stage 2 defines ``Prov_Q`` via impredicative intersection
# (``q_proof.PROV_Q_DEF``), not via an explicit list-based
# ``Proof_Q``. The two are HOL-equivalent (Knaster-Tarski) but the
# representability proof needs the list-based form: the diagonal
# lemma's ``Prov_Q_internal`` formula must internalise *explicit*
# proofs into Q's own language, so we want a Sigma_1 formula
# ``Proof_Q_internal`` saying "p is a list of formulas, each an axiom
# or following from earlier ones by MP/Gen, ending in n".
#
# Stage 3 therefore:
#   (a) Builds the list-based ``Proof_Q`` predicate (HOL function)
#       and proves ``Prov_Q n <=> ?p. Proof_Q p n`` against the
#       Stage-2 ``Prov_Q``.
#   (b) Defines ``Proof_Q_internal`` and ``Prov_Q_internal`` as
#       Q-formulas.
#   (c) Proves the representability theorem
#         |- !n. Prov_Q n <=> Prov_Q (godelnum (Prov_Q_internal (numeral n))).
#
# ------------------------------------------------------------------
# Output (eventual):
# ------------------------------------------------------------------
#
#   defn:  numeral : nat0 -> nat0
#          (numeral n = Succ_t^n Zero_t -- the n'th Q numeral)
#   defn:  represents_pred : nat0 -> (nat0 -> bool) -> bool
#   defn:  represents_func : nat0 -> (nat0 -> nat0) -> bool
#   defn:  Proof_Q         : nat0 -> nat0 -> bool
#   thm:   |- !n. Prov_Q n <=> ?p. Proof_Q p n
#   defn:  Proof_Q_internal, Prov_Q_internal : nat0 (Q-formulas)
#   thm:   |- !n. Prov_Q n <=>
#                Prov_Q (godelnum (Prov_Q_internal (numeral n)))
#
# ------------------------------------------------------------------
# This file (Stage 3A): foundations.
# ------------------------------------------------------------------
#
#   * ``numeral`` defined via ``define_unary_0``.
#   * ``IS_TERM_NUMERAL``: every numeral is a well-formed Q term.
#   * ``represents_pred``: representability of a unary nat0-predicate.
#
# Stage 3B (deferred): list-based ``Proof_Q``, the Prov_Q ↔
# ?p. Proof_Q p n equivalence, representability of ``substitute``.
#
# Stage 3C (deferred): ``Prov_Q_internal`` and the headline
# representability theorem.

# ---------------------------------------------------------------------------
# Imports.
# ---------------------------------------------------------------------------

from fusion import Var
from basics import mk_const, mk_app, mk_abs, rand
from parser import define, parse_type
from axioms import mk_forall, mk_imp, mk_not, mk_and
from nat0 import nat0_ty, define_unary_0
from proof import proof
from tactics import (
    SPEC, GEN, GENL, SYM, AP_THM, BETA_CONV, TRANS, DISJ1, REFL,
)

from q_syntax import (
    Zero_t, Succ_t,
    is_term_const,
    IS_TERM_REC, IS_TERM_AT_SUCC,
)
from q_proof import (
    var_x,
    Prov_Q,
)


# ---------------------------------------------------------------------------
# Stage 3A (a) -- the numeral function.
#
#   numeral 0          =  Zero_t.
#   numeral (SUC0 n)   =  Succ_t (numeral n).
#
# Defined by primitive recursion on nat0 via ``define_unary_0``. The
# resulting term ``numeral n`` is a closed Q-term encoding the n'th
# successor of Zero (i.e. the standard von Neumann numeral encoded
# through Stage 1's term constructors).
# ---------------------------------------------------------------------------


_n_n0 = Var("n", nat0_ty)
_a_n0 = Var("a", nat0_ty)


# Step body: \k a. Succ_t a.  (k unused; the new value is just Succ_t
# applied to the recursive result.)
_h_numeral = mk_abs(_n_n0, mk_abs(_a_n0, mk_app(Succ_t, _a_n0)))


NUMERAL_BASE, NUMERAL_STEP = define_unary_0(
    "numeral",
    parse_type("nat0 -> nat0"),
    Zero_t,
    _h_numeral,
    result_ty=nat0_ty,
)
numeral = mk_const("numeral", [])


# ---------------------------------------------------------------------------
# Stage 3A (b) -- IS_TERM_NUMERAL: every numeral is a well-formed Q term.
#
#   |- !n. is_term (numeral n).
#
# Direct induction on n. The base case is a single application of
# IS_TERM_REC at Zero_t (the leftmost disjunct collapses to REFL).
# The step case uses IS_TERM_AT_SUCC (the Succ_t-recursion equation
# from Stage 1) with witness ``numeral n`` and the inductive
# hypothesis.
# ---------------------------------------------------------------------------


is_term = is_term_const  # parser-friendly alias


@proof
def IS_TERM_ZERO(p):
    """|- is_term Zero_t.

    From IS_TERM_REC at Zero_t, the body's leftmost disjunct
    ``Zero_t = Zero_t`` is reflexive; lift to the iff RHS by DISJ1
    and EQ_MP through SYM.
    """
    p.goal("is_term Zero_t")

    rec_at_zero = SPEC(Zero_t, IS_TERM_REC)
    # rec_at_zero : |- is_term Zero_t = (Zero_t = Zero_t \/ ...rest)
    rhs = rand(rec_at_zero._concl)
    # rhs has shape: (Zero_t = Zero_t) \/ rest
    refl_zero = REFL(Zero_t)  # |- Zero_t = Zero_t
    from basics import rand as _rand, rator as _rator
    # Extract the right disjunct of rhs.
    # rhs is ((Zero_t = Zero_t) \/ rest); its rator is `Or (Zero_t=Zero_t)`,
    # its rand is `rest`.
    rest = _rand(rhs)
    rhs_th = DISJ1(refl_zero, rest)  # |- (Zero_t = Zero_t) \/ rest
    p.thus("is_term Zero_t").by_eq_mp(SYM(rec_at_zero), rhs_th)


@proof
def IS_TERM_SUCC(p):
    """|- !t. is_term t ==> is_term (Succ_t t).

    ``IS_TERM_AT_SUCC`` from Stage 1 already simplifies the
    Succ-disjunct of the body to the bare ``is_term t``: |- !t.
    is_term (Succ_t t) = is_term t. So this lemma is one EQ_MP step.
    """
    p.goal("!t. is_term t ==> is_term (Succ_t t)")
    p.fix("t")
    p.assume("ih: is_term t")
    at_succ_t = SPEC(p._parse("t"), IS_TERM_AT_SUCC)
    p.thus("is_term (Succ_t t)").by_eq_mp(SYM(at_succ_t), "ih")


@proof
def IS_TERM_NUMERAL(p):
    """|- !n. is_term (numeral n)."""
    p.goal("!n. is_term (numeral n)")
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.have("eq0: numeral 0 = Zero_t").by_thm(NUMERAL_BASE)
            p.thus("is_term (numeral 0)").by_rewrite_of(IS_TERM_ZERO, [SYM(p.fact("eq0"))])
        with p.step("IH"):
            p.have("eq_step: numeral (SUC0 n) = Succ_t (numeral n)").by(
                NUMERAL_STEP, "n"
            )
            p.have("succ_term: is_term (Succ_t (numeral n))").by(
                IS_TERM_SUCC, "numeral n", "IH"
            )
            p.thus("is_term (numeral (SUC0 n))").by_rewrite_of(
                "succ_term", [SYM(p.fact("eq_step"))]
            )


# ---------------------------------------------------------------------------
# Stage 3A (c) -- representability scaffolding.
#
# A unary predicate ``P : nat0 -> bool`` is *represented* by a
# Q-formula ``F`` (a nat0 godelnum, taken to be a Q-formula whose only
# free variable is ``var_x``) iff:
#
#   * (positive)  !n. P n      ==> Prov_Q (substitute F (numeral n) var_x).
#   * (negative)  !n. ~ P n    ==> Prov_Q (Not_f (substitute F (numeral n) var_x)).
#
# We package the conjunction of the two conditions as
# ``represents_pred F P``.
#
# ``represents_func`` and the various function-arity variants are
# deferred to Stage 3B/C.
# ---------------------------------------------------------------------------


substitute = mk_const("substitute", [])
Not_f = mk_const("Not_f", [])


_F_n0 = Var("F", nat0_ty)
_P_pred = Var("P", parse_type("nat0 -> bool"))


def _subst_at_numeral(F_term, n_term):
    """Build ``substitute F (numeral n) var_x``."""
    return mk_app(substitute, F_term, mk_app(numeral, n_term), var_x)


_pos_clause = mk_forall(_n_n0,
    mk_imp(mk_app(_P_pred, _n_n0),
           mk_app(Prov_Q, _subst_at_numeral(_F_n0, _n_n0))))
_neg_clause = mk_forall(_n_n0,
    mk_imp(mk_not(mk_app(_P_pred, _n_n0)),
           mk_app(Prov_Q,
                  mk_app(Not_f, _subst_at_numeral(_F_n0, _n_n0)))))

_represents_pred_body = mk_and(_pos_clause, _neg_clause)

REPRESENTS_PRED_DEF = define(
    "represents_pred",
    parse_type("nat0 -> (nat0 -> bool) -> bool"),
    mk_abs(_F_n0, mk_abs(_P_pred, _represents_pred_body)),
)
represents_pred = mk_const("represents_pred", [])


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


# |- !F P. represents_pred F P =
#          ((!n. P n ==> Prov_Q (substitute F (numeral n) var_x))
#        /\ (!n. ~ P n
#               ==> Prov_Q (Not_f (substitute F (numeral n) var_x)))).
REPRESENTS_PRED_AT = _at2(REPRESENTS_PRED_DEF, _F_n0, _P_pred)


# ---------------------------------------------------------------------------
# Roadmap -- Stage 3B and 3C.
# ---------------------------------------------------------------------------
#
# Stage 3B (proof witnesses inside HOL):
#
#   * Define ``mem_l`` (list membership) via ``define_wf_lt`` using
#     ``NAT0_LT_CONS_L_HEAD`` / ``NAT0_LT_CONS_L_TAIL`` from
#     ``q_proof``. The MONO obligation peels off the existential
#     under the cons-witness and uses the size lemmas to discharge
#     the recursive call.
#
#   * Define ``Proof_Q : nat0 -> nat0 -> bool`` via ``define_wf_lt``:
#         Proof_Q p n :<=>
#             p = nil_l
#               ? F      -- empty proofs prove nothing
#               : ?h t. p = cons_l h t /\ h = n /\ Proof_Q t h
#                       /\ valid_step t h
#     where ``valid_step t h`` says ``h`` is an axiom, follows by MP
#     from earlier members of ``t``, or follows by Gen from a member
#     of ``t``.
#
#   * Prove the equivalence with the impredicative ``Prov_Q``:
#         |- !n. Prov_Q n <=> ?p. Proof_Q p n.
#     Forward (?p ==> Prov_Q): induction on the proof list, using
#     PROV_Q_AXIOM / PROV_Q_MP / PROV_Q_GEN at each step.
#     Backward (Prov_Q ==> ?p): instantiate ``P := \n. ?p. Proof_Q p n``
#     in PROV_Q_AT and verify the three closure clauses by exhibiting
#     extended proof lists.
#
#   * Representability of ``substitute``: Sigma_1 formula
#     ``substitute_internal`` such that
#         |- !F t v. Prov_Q (substitute_internal_eq F t v
#                                                  (numeral
#                                                   (substitute F t v))).
#     Standard induction on F; ~200 lines with the recursion equations
#     from Stage 1.
#
# Stage 3C (representability of provability):
#
#   * Define ``Proof_Q_internal``: a Q-formula in two free variables
#     ``var_x``, ``var_y`` such that ``substitute_2 Proof_Q_internal
#     (numeral p) (numeral n) var_x var_y`` is Q-provable iff
#     ``Proof_Q p n`` holds. Constructed bottom-up from
#     ``substitute_internal``, ``is_axiom_internal``, ``is_mp_internal``,
#     ``is_gen_internal`` -- each itself a representable predicate.
#
#   * Define ``Prov_Q_internal n := ?_internal var_y. Proof_Q_internal``
#     where ``?_internal`` is encoded as ``~!y. ~``.
#
#   * Headline theorem:
#         |- !n. Prov_Q n <=>
#                 Prov_Q (godelnum (Prov_Q_internal (numeral n))).
#     Forward: Prov_Q n => ?p. Proof_Q p n => Q proves the Sigma_1
#     statement Proof_Q_internal(numeral p, numeral n) by Sigma_1
#     completeness => Q proves Prov_Q_internal(numeral n) by EXISTS.
#     Backward: Sigma_1 soundness (proved in Stage 6 from the HF model).


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3A (a) -- numeral function.")
    print("    NUMERAL_BASE :", pp_thm(NUMERAL_BASE))
    print("    NUMERAL_STEP :", pp_thm(NUMERAL_STEP))
    print()
    print("Stage 3A (b) -- IS_TERM_NUMERAL.")
    print("    IS_TERM_ZERO     :", pp_thm(IS_TERM_ZERO))
    print("    IS_TERM_SUCC     :", pp_thm(IS_TERM_SUCC))
    print("    IS_TERM_NUMERAL  :", pp_thm(IS_TERM_NUMERAL))
    print()
    print("Stage 3A (c) -- representability scaffolding.")
    print("    REPRESENTS_PRED_DEF :", pp_thm(REPRESENTS_PRED_DEF))
    print("    REPRESENTS_PRED_AT  :", pp_thm(REPRESENTS_PRED_AT))
