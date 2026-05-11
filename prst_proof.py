# ---------------------------------------------------------------------------
# Stage 2B (PRST) -- the PRST proof system.
# ---------------------------------------------------------------------------
#
# PRST is a quantifier-free theory: HF's propositional fragment
# (K, S, N axiom schemas, modus ponens) plus equality axioms
# (Refl, Subst), with free Var_pt indices in axioms implicitly
# universally closed. No object-level Forall_pf, no UI/Gen rules.
# The non-logical axiom layer differs from HF:
#
#   * HF1 - HF5 carry over verbatim (membership/insert/extensionality/
#     foundation).
#   * PR-defining-equation axioms (one per registered PR symbol's
#     defining clause). Recognised by ``is_pr_def`` from prst_pr.
#
# So:
#
#   is_pr_axiom n   :<=>   is_hf_axiom n  \/  is_pr_def n
#                                          \/  is_logical_axiom n.
#
# Prov_PRST is the corresponding closure predicate. Definition shape
# mirrors Prov_HF:
#
#   Prov_PRST n :<=> ?p. Proof_PRST p n,
#
# where Proof_PRST is a list-of-godelnums proof-checker.
#
# The closure rules drop out the same way (minus generalisation,
# which has no object-level counterpart):
#
#   (1) |- !n. is_pr_axiom n ==> Prov_PRST n.
#   (2) |- !f g. Prov_PRST f /\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g.
#
# Specialisation of free Var_pt indices is provided by the derived
# rule PROV_PRST_SUBST_AXIOM: each axiom schema is closed under
# substitution into its free Var_pt slots.
#
# This file is mostly *re-using* hf_proof's logical axiom schemas
# (IS_K/IS_S/.../IS_SUBST), wrapping them under is_pr_axiom, and
# defining the new closure predicate. Estimate: ~400 lines once
# filled in (vs ~900 in hf_proof, which had to write the equality and
# quantifier schemas from scratch).
# ---------------------------------------------------------------------------


from fusion import Var
from basics import mk_const, mk_app
from parser import define, parse_type
from nat0 import nat0_ty
from proof import proof, define_with_at
from hf_proof import (
    IS_HF_AXIOM_DEF,  # noqa: F401  -- re-used: HF1-5 carry over to PRST
    IS_HF_AXIOM_AT,  # noqa: F401  -- re-used
    IS_LOGICAL_AXIOM_DEF,  # noqa: F401  -- re-used: propositional fragment only
    IS_LOGICAL_AXIOM_AT,  # noqa: F401  -- re-used
    IS_AXIOM_DEF,  # noqa: F401  -- re-used as a building block
    IS_AXIOM_AT,  # noqa: F401  -- re-used
    is_mp,  # noqa: F401
)
from hf_repr_core import (
    Prov_HF,  # noqa: F401  -- used in PROV_HF_TO_PROV_PRST
    numeral,  # noqa: F401  -- parser alias for PROV_PRST_NUMERAL_EVAL
    substitute,  # noqa: F401  -- parser alias for PROV_PRST_SUBSTITUTE_EVAL
    Proof_HF,  # noqa: F401  -- parser alias
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
    numeral_pr,  # noqa: F401  -- parser alias
    substitute_pr,  # noqa: F401  -- parser alias
    diag_pr,  # noqa: F401  -- parser alias
    Proof_HF_pr,  # noqa: F401  -- parser alias
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
    is_pform,  # noqa: F401  -- parser alias for PROV_HF_TO_PROV_PRST
)


# ---------------------------------------------------------------------------
# Stage 2B (a) -- the PRST axiom recogniser.
#
# is_pr_axiom n  <=>  is_hf_axiom n  \/  is_pr_def n  \/  is_logical_axiom n.
#
# Note: ``is_hf_axiom`` and ``is_logical_axiom`` from hf_proof.py
# carry over unchanged. They were defined over the HF tag space
# (Eq_f, Not_f, ..., In_a), and since PRST re-uses those tags
# (prst_syntax inherits them), the recognisers still apply.
#
# is_pr_def from prst_pr.py recognises defining equations for the PR
# function symbols (ZERO/ADJ/PROJ/IF_IN/REC + derived symbols).
# ---------------------------------------------------------------------------


IS_PR_AXIOM_DEF, IS_PR_AXIOM_AT = define_with_at(
    "is_pr_axiom",
    parse_type("nat0 -> bool"),
    "\\n:nat0. is_hf_axiom n \\/ is_pr_def n \\/ is_logical_axiom n",
)
is_pr_axiom = mk_const("is_pr_axiom", [])

# Note on is_logical_axiom: HF's bundle includes the quantifier
# schemas is_UI / is_Vac / is_FaImp. In PRST these branches are inert
# because the underlying schemas recognise formulas containing Forall_f
# (= the HF Forall constructor), which PRST formulas (built without
# Forall_pf) never contain. So re-using is_logical_axiom verbatim is
# safe -- the unused branches never fire on PRST inputs.


# ---------------------------------------------------------------------------
# Stage 2B (b) -- Proof_PRST: the list-of-formulas proof checker.
#
# Same shape as Proof_HF (one cons_l step at a time, each step being
# either an axiom instance, a modus-ponens step from earlier lines, or
# a generalisation of an earlier line).
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
#         MP PROV_PRST_AXIOM (DISJ2 ... (DISJ1 IS_PR_DEF_HOLDS_ZERO))
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
# them at concrete terms. PRST is quantifier-free, so we cannot derive
# the rule via Gen + UI as HF does; instead it is built into is_pr_def
# directly: is_pr_def is closed under substitution at any free Var_pt
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


@proof
def PROV_PRST_MP(p):
    """|- !f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g.

    Proof: concatenate the two witnessing proofs, then append the
    modus-ponens step. STUB.
    """
    p.goal("!f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g")
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (e) -- bridge: every quantifier-free HF theorem is a PRST theorem.
#
# is_pr_axiom is a superset of is_hf_axiom and shares is_logical_axiom,
# so any Forall-free HF proof is automatically a PRST proof. Formally:
#
#   |- !n. is_pform n /\ Prov_HF n ==> Prov_PRST n.
#
# (The is_pform side condition restricts to Forall-free formulas;
# Forall_f-containing HF theorems have no PRST counterpart since PRST
# formulas don't include Forall_pf.) This lets us re-use the
# propositional / equality fragment of the hf_logic toolkit
# (PROV_HF_K, PROV_HF_AND_INTRO, PROV_HF_IFF_INTRO, ...) inside PRST
# by pushing each Forall-free Prov_HF conclusion through the bridge.
# ---------------------------------------------------------------------------


@proof
def PROV_HF_TO_PROV_PRST(p):
    """|- !n. is_pform n /\\ Prov_HF n ==> Prov_PRST n.

    Proof: induction on the Prov_HF witness, restricted to is_pform
    (= Forall-free) conclusions. The axiom branch uses is_hf_axiom ==>
    is_pr_axiom (via disjunction); the MP branch goes through
    PROV_PRST_MP. The GEN branch of Prov_HF cannot fire on an is_pform
    conclusion because Forall_f-headed formulas fail is_pform. STUB.
    """
    p.goal(
        "!n. is_pform n /\\ Prov_HF n ==> Prov_PRST n",
        types={"n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (f) -- internal arithmetic via PR symbols.
#
# In HF, "HF proves P(numeral n)" requires evaluating substitute
# externally and then having SUBSTITUTE_REPRESENTS push the equality
# into HF. In PRST, both ``substitute`` and ``numeral`` are PR symbols,
# so the corresponding term is *already* the result. The Prov_PRST
# version of ``substitute(F, numeral n, v) = result`` is one
# defining-equation lookup:
#
#   |- !F v. Prov_PRST (Eq_pf (App_pt substitute_pr
#                                  (cons_l F (cons_l (App_pt numeral_pr
#                                                       (cons_l n nil_l))
#                                                    (cons_l v nil_l))))
#                             <result computed at HOL level>).
#
# Stub: this is the "free evaluation" the PRST move buys us.
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

    Once available, this is the "free representability" theorem -- it
    replaces ~3000 lines of SUBSTITUTE_REPRESENTS infrastructure.
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
    chained via PRST equality reasoning (PROV_HF_EQ_TRANS lifted through
    PROV_HF_TO_PROV_PRST). STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt diag_pr (cons_l n nil_l)) (diag n))",
        types={"n": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (g) -- Prov_PRST_internal: the PRST formula expressing
# "Prov_PRST holds at x". This is the analog of Prov_HF_internal from
# hf_repr_thms.py, but built differently. PRST is quantifier-free, so
# we cannot write "there exists a proof y of x" as an Exists_pf formula
# directly. Instead we use a *search* PR symbol find_proof_pr that
# returns a proof of x when one exists (and a sentinel otherwise), and
# define:
#
#   Prov_PRST_internal := Eq_pf
#                           (App_pt Proof_HF_pr
#                             (cons_l (App_pt find_proof_pr
#                                       (cons_l (Var_pt x) nil_l))
#                                     (cons_l (Var_pt x) nil_l)))
#                           T_pt.
#
# I.e. "Proof_HF_pr(find_proof_pr(x), x) = T_pt". Because find_proof_pr
# is a PR symbol (registered in prst_pr), this is a closed PRST formula
# with no quantifiers. The representability theorem is one Prov_PRST
# step:
#
#   |- !n. Prov_PRST n <=> Prov_PRST (substitute_p Prov_PRST_internal
#                                                  (numeral n) var_x).
#
# (find_proof_pr is not primitive recursive in the usual sense -- it
# requires unbounded search -- so this layer relies on the partial-PR
# extension; that is the analog of the HF Sigma_1 existential. See
# prst_pr for the construction.)
# ---------------------------------------------------------------------------


prov_prst_internal_def = define(
    "Prov_PRST_internal",
    parse_type("nat0"),
    "0",  # placeholder; real body uses App_pt find_proof_pr + Proof_HF_pr
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
    predicate. In HF this was the most expensive single theorem in the
    development (~1000 lines). In PRST it reduces to:
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
# Comparison to hf_proof.py + the Prov_HF parts of hf_repr_core.py:
#   hf_proof.py            = ~900 lines.
#   hf_repr_core.py (Prov_HF part) = ~500 lines.
#   prst_proof.py replaces both, taking ~400 lines.
#
# The saving comes from re-using is_hf_axiom and is_logical_axiom
# verbatim (one disjunct in is_pr_axiom), and from PROV_HF_TO_PROV_PRST
# letting us inherit the whole hf_logic.py toolkit.
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
    print("Stage 2B (e) -- bridge.")
    print("    PROV_HF_TO_PROV_PRST   :", pp_thm(PROV_HF_TO_PROV_PRST))
    print()
    print("Stage 2B (f) -- free evaluation of PR symbols.")
    print("    PROV_PRST_SUBSTITUTE_EVAL :", pp_thm(PROV_PRST_SUBSTITUTE_EVAL))
    print("    PROV_PRST_NUMERAL_EVAL    :", pp_thm(PROV_PRST_NUMERAL_EVAL))
    print("    PROV_PRST_DIAG_EVAL       :", pp_thm(PROV_PRST_DIAG_EVAL))
    print()
    print("Stage 2B (g) -- Prov_PRST_internal.")
    print("    IS_PFORM_PROV_PRST_INTERNAL :", pp_thm(IS_PFORM_PROV_PRST_INTERNAL))
    print("    FREE_IN_PROV_PRST_INTERNAL  :", pp_thm(FREE_IN_PROV_PRST_INTERNAL))
    print("    PROV_PRST_REPRESENTS        :", pp_thm(PROV_PRST_REPRESENTS))
