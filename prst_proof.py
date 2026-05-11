# ---------------------------------------------------------------------------
# Stage 2B (PRST) -- the PRST proof system.
# ---------------------------------------------------------------------------
#
# PRST is a quantifier-free theory: propositional axiom schemas
# (K, S, N), modus ponens, and equality axioms (Refl, Subst), with
# free Var_pt indices in axioms implicitly universally closed. No
# object-level Forall_pf, no UI/Gen rules. The non-logical axiom layer
# is purely equational:
#
#   * PR-defining-equation axioms (one per registered PR symbol's
#     defining clause). Recognised by ``is_pr_def`` from prst_pr.
#
# So:
#
#   is_pr_axiom n   :<=>   is_pr_def n  \/  is_logical_axiom n.
#
# Following Jensen-Karp 1971 ("Primitive Recursive Set Functions"):
# PRST has *no* set-theoretic axioms in the object language. PR
# symbols are uninterpreted at the syntactic level; their defining
# equations plus the standard nat0 HOL model do all the work. This is
# analogous to PRA, where natural numbers are not axiomatised -- 0 and
# S are primitive symbols, +/* have defining equations, and arithmetic
# facts come from the standard N-model.
#
# Prov_PRST is the corresponding closure predicate:
#
#   Prov_PRST n :<=> ?p. Proof_PRST p n,
#
# where Proof_PRST is a list-of-godelnums proof-checker.
#
# The closure rules are the standard Hilbert-style pair (minus
# generalisation, which has no object-level counterpart):
#
#   (1) |- !n. is_pr_axiom n ==> Prov_PRST n.
#   (2) |- !f g. Prov_PRST f /\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g.
#
# Specialisation of free Var_pt indices is provided by the derived
# rule PROV_PRST_SUBST_AXIOM: each axiom schema is closed under
# substitution into its free Var_pt slots.
#
# This file re-uses hf_proof's logical axiom schemas (IS_K / IS_S /
# ... / IS_SUBST), wraps them under is_pr_axiom, and defines the new
# closure predicate. Estimate: ~400 lines once filled in.
# ---------------------------------------------------------------------------


from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from hf_proof import (
    IS_LOGICAL_AXIOM_DEF,  # noqa: F401  -- re-used: propositional fragment only
    IS_LOGICAL_AXIOM_AT,  # noqa: F401  -- re-used
    is_mp,  # noqa: F401
)
from hf_repr_core import (
    numeral,  # noqa: F401  -- parser alias for PROV_PRST_NUMERAL_EVAL
    substitute,  # noqa: F401  -- parser alias for PROV_PRST_SUBSTITUTE_EVAL
)
from godel_first import (
    diag,  # noqa: F401  -- parser alias for PROV_PRST_DIAG_EVAL
)
from prst_pr import (
    is_pr_def,  # noqa: F401  -- parser alias
    is_pr_sym,  # noqa: F401  -- referenced by is_pr_axiom transitively via is_pterm
    zero_sym,  # noqa: F401  -- parser alias
    adj_sym,  # noqa: F401  -- parser alias
    proj_sym,  # noqa: F401  -- parser alias
    if_in_sym,  # noqa: F401  -- parser alias
    rec_sym,  # noqa: F401  -- parser alias
    comp_sym,  # noqa: F401  -- parser alias
    mu_sym,  # noqa: F401  -- parser alias for MU_CORRECTNESS
    numeral_pr,  # noqa: F401  -- parser alias
    substitute_pr,  # noqa: F401  -- parser alias
    diag_pr,  # noqa: F401  -- parser alias
    Proof_PRST_pr,  # noqa: F401  -- parser alias
    find_proof_pr,  # noqa: F401  -- parser alias for Prov_PRST_internal
    T_pt,  # noqa: F401  -- parser alias for MU_CORRECTNESS
    is_partial_pr_sym,  # noqa: F401  -- parser alias for MU_CORRECTNESS
    zero_def_axiom,  # noqa: F401  -- parser alias for PROV_PRST_ZERO_DEF
    Adj_pt,  # noqa: F401  -- parser alias for PROV_PRST_ADJ_DEF_AT
    proj_def_axiom_at,  # noqa: F401  -- parser alias
    if_in_true_def_axiom,  # noqa: F401  -- parser alias
    if_in_false_def_axiom,  # noqa: F401  -- parser alias
    rec_base_def_axiom_at,  # noqa: F401  -- parser alias
    rec_step_def_axiom_at,  # noqa: F401  -- parser alias
)
from hf_proof import (
    nil_l,  # noqa: F401  -- parser alias
    cons_l,  # noqa: F401  -- parser alias
    var_x,  # noqa: F401  -- parser alias
)
from prst_syntax import (
    Imp_pf,  # noqa: F401  -- parser alias for is_pr_axiom
    Eq_pf,  # noqa: F401  -- parser alias for Prov_PRST_internal
    Var_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
    App_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
)


# ---------------------------------------------------------------------------
# Stage 2B (a) -- the PRST axiom recogniser.
#
# is_pr_axiom n  <=>  is_pr_def n  \/  is_logical_axiom n.
#
# is_pr_def from prst_pr.py recognises defining equations for the PR
# function symbols (ZERO/PROJ/IF_IN/REC + derived symbols). adj_sym
# has no defining equation -- it is a primitive PR symbol whose
# semantics is fixed by the standard nat0 HOL model, not by an axiom.
# ---------------------------------------------------------------------------


IS_PR_AXIOM_DEF, IS_PR_AXIOM_AT = define_with_at(
    "is_pr_axiom",
    parse_type("nat0 -> bool"),
    "\\n:nat0. is_pr_def n \\/ is_logical_axiom n",
)
is_pr_axiom = mk_const("is_pr_axiom", [])

# Note on is_logical_axiom: the bundle re-used from hf_proof includes
# the quantifier schemas is_UI / is_Vac / is_FaImp. In PRST these
# branches are inert because the underlying schemas recognise formulas
# containing Forall_f, which PRST formulas (built without Forall_pf)
# never contain. So re-using is_logical_axiom verbatim is safe -- the
# unused branches never fire on PRST inputs.


# ---------------------------------------------------------------------------
# Stage 2B (b) -- Proof_PRST: the list-of-formulas proof checker.
#
# One cons_l step at a time, each step being either an axiom instance
# or a modus-ponens step from earlier lines. (No generalisation step:
# PRST is quantifier-free.)
#
# We model it via define_wf_lt on the proof list. Stub.
# ---------------------------------------------------------------------------


Proof_PRST_def = define(
    "Proof_PRST",
    parse_type("nat0 -> nat0 -> bool"),
    "\\p:nat0. \\n:nat0. F",
)
Proof_PRST = mk_const("Proof_PRST", [])


@proof
def PROOF_PRST_NIL(p):
    """|- !n. ~ Proof_PRST nil_l n. STUB (empty proof proves nothing)."""
    p.goal("!n. ~ Proof_PRST nil_l n", types={"n": nat0_ty})
    p.sorry()


@proof
def PROOF_PRST_CONS(p):
    """|- !h t n. Proof_PRST (cons_l h t) n =
            ( n = h
              /\\ ( is_pr_axiom h
                  \\/ (?f g. Proof_PRST t f
                              /\\ Proof_PRST t (Imp_pf f g)
                              /\\ h = g))).
    STUB (one-step extension of an existing proof; only axiom and
    modus-ponens steps -- PRST has no generalisation rule)."""
    p.goal(
        "!h t n. Proof_PRST (cons_l h t) n = "
        "( n = h "
        "  /\\ ( is_pr_axiom h "
        "      \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) /\\ h = g)))",
        types={"h": nat0_ty, "t": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (c) -- Prov_PRST: provability.
#
#   Prov_PRST n :<=> ?p. Proof_PRST p n.
# ---------------------------------------------------------------------------


PROV_PRST_DEF, PROV_PRST_AT = define_with_at(
    "Prov_PRST",
    parse_type("nat0 -> bool"),
    "\\n:nat0. ?p:nat0. Proof_PRST p n",
)
Prov_PRST = mk_const("Prov_PRST", [])


# ---------------------------------------------------------------------------
# Stage 2B (d) -- closure rules.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_AXIOM(p):
    """|- !n. is_pr_axiom n ==> Prov_PRST n.

    Proof: take the one-line proof ``cons_l n nil_l``, axiom branch of
    PROOF_PRST_CONS, EXISTS to close ``?p. Proof_PRST p n``, fold via
    PROV_PRST_AT. STUB.
    """
    p.goal("!n. is_pr_axiom n ==> Prov_PRST n")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (d.1) -- the PR-defining-equation axioms.
#
# Moved here from prst_pr because they refer to Prov_PRST.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 2B (d.1) -- PR-defining-equation theorems as one-line
# specialisations of PROV_PRST_AXIOM.
#
# Each axiom godelnum (from prst_pr) is in is_pr_def, hence is in
# is_pr_axiom, hence Prov_PRST holds of it. One MP per axiom; no fresh
# @proof body needed once the chain is in place.
#
# Pattern (filled in -- not a sorry; falls out of MP + IS_PR_DEF_HOLDS_*
# + IS_PR_AXIOM_DEF unfolding + PROV_PRST_AXIOM):
#
#     PROV_PRST_ZERO_DEF :=
#         MP PROV_PRST_AXIOM (DISJ1 IS_PR_DEF_HOLDS_ZERO)
#     |- Prov_PRST zero_def_axiom
#
# Stubs below carry the headline statement; the body just notes the
# specialisation. No new axioms posted; once IS_PR_DEF_HOLDS_* and
# PROV_PRST_AXIOM are real theorems, these are real theorems too.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_ZERO_DEF(p):
    """|- Prov_PRST zero_def_axiom.

    = SPEC zero_def_axiom PROV_PRST_AXIOM applied to
    IS_PR_DEF_HOLDS_ZERO (lifted through is_pr_axiom's disjunction).
    STUB.
    """
    p.goal("Prov_PRST zero_def_axiom")
    p.sorry()


# adj_sym is a primitive PR symbol -- no defining equation, hence no
# PROV_PRST_ADJ_DEF theorem. The downstream "concrete" form
# PROV_PRST_ADJ_DEF_AT is the reflexive equation App_pt adj_sym [x; y]
# = Adj_pt x y, which is REFL (Adj_pt unfolds to the App_pt
# expression). Listed below for symmetry with the other defining
# theorems; trivial discharge.


@proof
def PROV_PRST_PROJ_DEF(p):
    """|- !i n. nat0_lt i n ==> Prov_PRST (proj_def_axiom_at i n). STUB."""
    p.goal(
        "!i n. nat0_lt i n ==> Prov_PRST (proj_def_axiom_at i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_IF_IN_TRUE_DEF(p):
    """|- Prov_PRST if_in_true_def_axiom. STUB."""
    p.goal("Prov_PRST if_in_true_def_axiom")
    p.sorry()


@proof
def PROV_PRST_IF_IN_FALSE_DEF(p):
    """|- Prov_PRST if_in_false_def_axiom. STUB."""
    p.goal("Prov_PRST if_in_false_def_axiom")
    p.sorry()


@proof
def PROV_PRST_REC_BASE_DEF(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (rec_base_def_axiom_at g h). STUB."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_REC_STEP_DEF(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (rec_step_def_axiom_at g h). STUB."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (rec_step_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (d.2) -- substitute-into-axiom derived rule.
#
# Because PRST defining equations are stated with free Var_pt indices
# (implicit universal closure convention), consumers need to specialise
# them at concrete terms. PRST is quantifier-free, so the rule cannot
# come from Gen + UI; instead it is built into is_pr_def directly:
# is_pr_def is closed under substitution at any free Var_pt
# index, so every substitution instance of a defining axiom is itself
# a defining axiom, hence in is_pr_axiom, hence Prov_PRST.
#
#     PROV_PRST_SUBST_AXIOM :
#         |- !F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)
#
# Derivation: IS_PR_DEF_CLOSED_UNDER_SUBST (provided by prst_pr) gives
# is_pr_def (substitute_p F t v); PROV_PRST_AXIOM closes the goal in
# one MP. ~5 lines once the closure lemma is in place.
#
# A multi-variable variant (substitute several free vars at once) is
# the natural form for actual use sites; built by iterating this one.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_SUBST_AXIOM(p):
    """|- !F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v). STUB."""
    p.goal(
        "!F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


# Convenience corollaries for specific axioms at specific terms.
# Each is one application of PROV_PRST_SUBST_AXIOM at the appropriate
# axiom; the substitute_p reduces by AT-equations to give the
# HOL-quantified form that consumers actually want.
#
# Example (adj at concrete x, y):
#     PROV_PRST_ADJ_DEF_AT :
#         |- !x y. Prov_PRST (Eq_pf (App_pt adj_sym
#                                     (cons_l x (cons_l y nil_l)))
#                                   (Adj_pt x y)).
#
# Trivial discharge: Adj_pt is defined as App_pt adj_sym (cons_l x
# (cons_l y nil_l)), so the equation is the PRST-internal REFL on
# that term. The reason to state it as a named lemma is so downstream
# code can chain through "App_pt adj_sym ... = Adj_pt ..." without
# unfolding Adj_pt manually.


@proof
def PROV_PRST_ADJ_DEF_AT(p):
    """|- !x y. Prov_PRST (Eq_pf (App_pt adj_sym (cons_l x (cons_l y nil_l)))
                                 (Adj_pt x y)).

    The PRST-internal reflexivity of adj_sym applied to its arguments
    against the Adj_pt alias. Discharge: unfold Adj_pt, REFL, package
    via PRST equality axioms. STUB.
    """
    p.goal(
        "!x y. Prov_PRST (Eq_pf (App_pt adj_sym (cons_l x (cons_l y nil_l))) "
        "                       (Adj_pt x y))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.sorry()


# PROV_PRST_REC_BASE_DEF_AT, PROV_PRST_REC_STEP_DEF_AT, PROV_PRST_IF_IN_*_AT
# follow the same shape; omitted from this sketch.


# ---------------------------------------------------------------------------
# Stage 2B (d.3) -- mu-correctness axiom.
#
# The single non-PR axiom in the PRST + mu extension. For any (partial-)
# PR symbol f and any witness q certifying f at args, the mu-closure
# returns *some* witness that also certifies f. This is the
# quantifier-free internalisation of existential elimination needed for
# the second derivability condition (D2):
#
#     MU_CORRECTNESS :
#       |- !f q args.
#            is_partial_pr_sym f
#            /\ App_pt f (cons_l q args) = T_pt
#            ==> App_pt f (cons_l (App_pt (mu_sym f) args) args) = T_pt.
#
# Reading: "if any q makes f hold at args, then the witness returned by
# mu_sym f at args also makes f hold." No quantifier elimination, no
# bound proof-variable -- just a free q that gets specialised by
# PROV_PRST_SUBST_AXIOM at each use site.
# ---------------------------------------------------------------------------


@proof
def MU_CORRECTNESS(p):
    """|- !f q args.
            is_partial_pr_sym f
            /\\ App_pt f (cons_l q args) = T_pt
            ==> App_pt f (cons_l (App_pt (mu_sym f) args) args) = T_pt.

    The mu-correctness axiom (HOL-level statement; reflected into PRST
    via PROV_PRST_AXIOM at concrete (f, q, args) when used inside a
    Prov_PRST derivation). This is the only axiom about mu_sym and the
    only non-strict-PR commitment in the PRST + mu extension. Soundness
    holds in the standard nat0 HOL model under the convention that
    mu_sym f returns the classical least witness when one exists. STUB.
    """
    p.goal(
        "!f q args. is_partial_pr_sym f "
        "           /\\ App_pt f (cons_l q args) = T_pt "
        "           ==> App_pt f (cons_l (App_pt (mu_sym f) args) args) = T_pt",
        types={"f": nat0_ty, "q": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_MP(p):
    """|- !f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g.

    Proof: concatenate the two witnessing proofs, then append the
    modus-ponens step. STUB.
    """
    p.goal("!f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (e) -- internal arithmetic via PR symbols.
#
# Both ``substitute`` and ``numeral`` are PR symbols, so the
# corresponding term is *already* the result. The Prov_PRST version of
# ``substitute(F, numeral n, v) = result`` is one defining-equation
# lookup:
#
#   |- !F v. Prov_PRST (Eq_pf (App_pt substitute_pr
#                                  (cons_l F (cons_l (App_pt numeral_pr
#                                                       (cons_l n nil_l))
#                                                    (cons_l v nil_l))))
#                             <result computed at HOL level>).
#
# Free evaluation of PR-symbol applications inside Prov_PRST.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_SUBSTITUTE_EVAL(p):
    """|- !F t v. Prov_PRST (Eq_pf (App_pt substitute_pr
                                    (cons_l F (cons_l t (cons_l v nil_l))))
                                  (substitute F t v)).

    Where ``substitute`` on the RHS is HOL's substitute function (from
    hf_syntax). The defining equations of substitute_pr (in prst_pr)
    line up with the AT-equations of substitute, so this lemma is
    proved by structural induction on F, dispatching to PRST_REC_STEP
    at each constructor. STUB.

    The "free representability" theorem: since substitute_pr is a term
    constructor, its representability collapses to one defining-equation
    lookup.
    """
    p.goal(
        "!F t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (cons_l F (cons_l t (cons_l v nil_l)))) "
        "  (substitute F t v))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_NUMERAL_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt numeral_pr (cons_l n nil_l))
                               (numeral n)).

    Similar to PROV_PRST_SUBSTITUTE_EVAL, for numeral. STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt numeral_pr (cons_l n nil_l)) (numeral n))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_DIAG_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (cons_l n nil_l)) (diag n)).

    From DIAG_PR_DEFINING + PROV_PRST_SUBSTITUTE_EVAL + PROV_PRST_NUMERAL_EVAL,
    chained via PRST equality reasoning (PROV_PRST_EQ_TRANS). STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt diag_pr (cons_l n nil_l)) (diag n))",
        types={"n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (f) -- Prov_PRST_internal: the PRST formula expressing
# "Prov_PRST holds at x". PRST is quantifier-free, so "there exists a
# proof y of x" cannot be written with an object-level binder. Instead
# we use find_proof_pr := mu_sym Proof_PRST_pr (from prst_pr) -- the
# mu-closure of the decidable proof-checker, which returns a witness
# whenever one exists. The existential lives entirely at the
# meta-level inside mu_sym's interpretation; the formula below is
# binder-free:
#
#   Prov_PRST_internal := Eq_pf
#                           (App_pt Proof_PRST_pr
#                             (cons_l (App_pt find_proof_pr
#                                       (cons_l (Var_pt var_x) nil_l))
#                                     (cons_l (Var_pt var_x) nil_l)))
#                           T_pt.
#
# Reading: "the canonical witness mu_sym Proof_PRST_pr at x checks T_pt
# against x". By MU_CORRECTNESS, this is equivalent to "some witness
# checks T_pt", which is exactly the standard Sigma_1 provability
# predicate -- but stated quantifier-free.
#
# The representability theorem is one Prov_PRST step:
#
#   |- !n. Prov_PRST n <=> Prov_PRST (substitute_p Prov_PRST_internal
#                                                  (numeral n) var_x).
# ---------------------------------------------------------------------------


prov_prst_internal_def = define(
    "Prov_PRST_internal",
    parse_type("nat0"),
    "Eq_pf (App_pt Proof_PRST_pr "
    "         (cons_l (App_pt find_proof_pr (cons_l (Var_pt var_x) nil_l)) "
    "           (cons_l (Var_pt var_x) nil_l))) "
    "      T_pt",
)
Prov_PRST_internal = mk_const("Prov_PRST_internal", [])


@proof
def IS_PFORM_PROV_PRST_INTERNAL(p):
    """|- is_pform Prov_PRST_internal. STUB."""
    p.goal("is_pform Prov_PRST_internal")
    p.sorry()


@proof
def FREE_IN_PROV_PRST_INTERNAL(p):
    """|- !v. free_in_p Prov_PRST_internal v <=> v = var_x. STUB."""
    p.goal(
        "!v. free_in_p Prov_PRST_internal v = (v = var_x)",
        types={"v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_REPRESENTS(p):
    """|- !n. Prov_PRST n <=>
              Prov_PRST (substitute_p Prov_PRST_internal (numeral n) var_x).

    The headline representability theorem for PRST's own provability
    predicate. Reduces to:
      * Forward: from a Prov_PRST witness, exhibit the existential
        witness inside Prov_PRST_internal via PROV_PRST_DIAG_EVAL +
        equality-of-PR-terms reasoning.
      * Backward: from the existential witness, recover the Proof_PRST
        list and apply soundness.

    Estimate ~80 lines once filled in. STUB.
    """
    p.goal(
        "!n. Prov_PRST n = "
        "    Prov_PRST (substitute_p Prov_PRST_internal (numeral n) var_x)",
        types={"n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Module size estimate
# ---------------------------------------------------------------------------
#
# Filled in: ~400 lines.
#
# This module re-uses is_logical_axiom from hf_proof verbatim (one
# disjunct in is_pr_axiom), wraps it together with is_pr_def, and
# defines Prov_PRST. PRST has no set-theoretic axioms (Jensen-Karp
# 1971), and no quantifier rules. Any propositional fact needed inside
# PRST is re-derived directly from the Hilbert axioms.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2B (PRST) -- the PRST proof system.")
    print("    IS_PR_AXIOM_DEF        :", pp_thm(IS_PR_AXIOM_DEF))
    print("    PROV_PRST_DEF          :", pp_thm(PROV_PRST_DEF))
    print("    PROV_PRST_AXIOM        :", pp_thm(PROV_PRST_AXIOM))
    print("    PROV_PRST_MP           :", pp_thm(PROV_PRST_MP))
    print()
    print("Stage 2B (d.1) -- PR-defining-equation theorems (specialisations).")
    print("    PROV_PRST_ZERO_DEF       :", pp_thm(PROV_PRST_ZERO_DEF))
    print("    PROV_PRST_PROJ_DEF       :", pp_thm(PROV_PRST_PROJ_DEF))
    print("    PROV_PRST_IF_IN_TRUE_DEF :", pp_thm(PROV_PRST_IF_IN_TRUE_DEF))
    print("    PROV_PRST_REC_BASE_DEF   :", pp_thm(PROV_PRST_REC_BASE_DEF))
    print()
    print("Stage 2B (d.2) -- substitute-into-axiom derived rule.")
    print("    PROV_PRST_SUBST_AXIOM    :", pp_thm(PROV_PRST_SUBST_AXIOM))
    print("    PROV_PRST_ADJ_DEF_AT     :", pp_thm(PROV_PRST_ADJ_DEF_AT))
    print()
    print("Stage 2B (d.3) -- mu-correctness (the only non-PR axiom).")
    print("    MU_CORRECTNESS           :", pp_thm(MU_CORRECTNESS))
    print()
    print("Stage 2B (e) -- free evaluation of PR symbols.")
    print("    PROV_PRST_SUBSTITUTE_EVAL :", pp_thm(PROV_PRST_SUBSTITUTE_EVAL))
    print("    PROV_PRST_NUMERAL_EVAL    :", pp_thm(PROV_PRST_NUMERAL_EVAL))
    print("    PROV_PRST_DIAG_EVAL       :", pp_thm(PROV_PRST_DIAG_EVAL))
    print()
    print("Stage 2B (f) -- Prov_PRST_internal.")
    print("    IS_PFORM_PROV_PRST_INTERNAL :", pp_thm(IS_PFORM_PROV_PRST_INTERNAL))
    print("    FREE_IN_PROV_PRST_INTERNAL  :", pp_thm(FREE_IN_PROV_PRST_INTERNAL))
    print("    PROV_PRST_REPRESENTS        :", pp_thm(PROV_PRST_REPRESENTS))
