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
from nat0_order import define_wf_lt
from hf_proof import (
    IS_LOGICAL_AXIOM_DEF,  # noqa: F401  -- re-used: propositional fragment only
    IS_LOGICAL_AXIOM_AT,  # noqa: F401  -- re-used
    is_mp,  # noqa: F401
)
from hf_repr_core import (
    numeral,  # noqa: F401  -- parser alias for PROV_PRST_NUMERAL_EVAL
    substitute,  # noqa: F401  -- parser alias for PROV_PRST_SUBSTITUTE_EVAL
)
from hf_godel1 import (
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
    IS_PR_DEF_HOLDS_ZERO,
    IS_PR_DEF_HOLDS_PROJ,
    IS_PR_DEF_HOLDS_IF_IN_TRUE,
    IS_PR_DEF_HOLDS_IF_IN_FALSE,
    IS_PR_DEF_HOLDS_REC_BASE,
    IS_PR_DEF_HOLDS_REC_STEP,
)
from hf_proof import (
    var_x,  # noqa: F401  -- parser alias
)
from prst_syntax import (
    Imp_pf,  # noqa: F401  -- parser alias for is_pr_axiom
    Eq_pf,  # noqa: F401  -- parser alias for Prov_PRST_internal
    Var_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
    App_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
    Tup_pt,  # noqa: F401  -- parser alias; args- and proof-list cons cells
    Empty_pt,  # noqa: F401  -- parser alias; nil-tuple / empty proof list
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
# One Tup_pt step at a time, each step being either an axiom instance
# or a modus-ponens step from earlier lines. (No generalisation step:
# PRST is quantifier-free.)
#
# We model it via define_wf_lt recursing on the proof list. The
# recursive call ``rec t ...`` for any tail t is well-founded because
# t < Tup_pt h t by NAT0_LT_TUP_PT_R.
# ---------------------------------------------------------------------------


_PROOF_PRST_F_DEF = define(
    "_Proof_PRST_F",
    parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool"),
    "\\rec:nat0->nat0->bool. \\p:nat0. \\n:nat0. "
    "?h t. p = Tup_pt h t /\\ n = h /\\ "
    "      (is_pr_axiom h \\/ "
    "       (?f g. rec t f /\\ rec t (Imp_pf f g) /\\ h = g))",
)
_PROOF_PRST_F = mk_const("_Proof_PRST_F", [])


@proof
def PROOF_PRST_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
              ==> _Proof_PRST_F f p = _Proof_PRST_F g p. STUB (Layer 2)."""
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_Proof_PRST_F f p = _Proof_PRST_F g p",
        types={
            "f": parse_type("nat0 -> nat0 -> bool"),
            "g": parse_type("nat0 -> nat0 -> bool"),
            "p": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.sorry()


Proof_PRST_def, _PROOF_PRST_REC = define_wf_lt(
    "Proof_PRST",
    parse_type("nat0 -> nat0 -> bool"),
    _PROOF_PRST_F,
    PROOF_PRST_MONO,
)
Proof_PRST = mk_const("Proof_PRST", [])


# Binary at-form of _PROOF_PRST_REC: SPEC at p, AP_THM at n, BETA on RHS.
# Result: |- !p n. Proof_PRST p n = ?h t. p = Tup_pt h t /\ n = h /\ ...
def _proof_prst_at():
    from tactics import SPEC, GEN, AP_THM, BETA_CONV, TRANS
    from basics import rand
    from prst_syntax import _unfold_prst_rec as _unfold
    eq_fun = _unfold(_PROOF_PRST_REC, _PROOF_PRST_F_DEF)
    # eq_fun: !p. Proof_PRST p = \n. <body[p, n]>
    from fusion import Var
    p_var = Var("p", nat0_ty)
    n_var = Var("n", nat0_ty)
    eq_p = SPEC(p_var, eq_fun)
    # eq_p: Proof_PRST p = \n. body[p, n]
    eq_pn = AP_THM(eq_p, n_var)
    # eq_pn: Proof_PRST p n = (\n. body[p, n]) n
    rhs_beta = BETA_CONV(rand(eq_pn._concl))
    return GEN(p_var, GEN(n_var, TRANS(eq_pn, rhs_beta)))


PROOF_PRST_AT = _proof_prst_at()


@proof
def PROOF_PRST_NIL(p):
    """|- !n. ~ Proof_PRST Empty_pt n.

    Empty proof proves nothing: PROOF_PRST_AT specialised at Empty_pt
    asserts the body ``?h t. Empty_pt = Tup_pt h t /\\ ...``, but
    Empty_pt is not a Tup_pt (TUP_PT_DISJOINT_EMPTY_PT).
    """
    from prst_syntax import TUP_PT_NEQ_EMPTY_PT
    from tactics import SPECL, SYM
    p.goal("!n. ~ Proof_PRST Empty_pt n", types={"n": nat0_ty})
    p.fix("n")
    with p.suppose("h_pf: Proof_PRST Empty_pt n"):
        at_empty = SPECL([p._parse("Empty_pt"), p._parse("n")], PROOF_PRST_AT)
        p.have(
            "h_body: ?h t. Empty_pt = Tup_pt h t /\\ n = h /\\ "
            "        (is_pr_axiom h \\/ "
            "         (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) "
            "                /\\ h = g))"
        ).by_eq_mp(at_empty, "h_pf")
        # Explicit eq_label names dodge the default `h_eq` collision
        # (an `h_eq` label gets auto-registered elsewhere).
        p.choose("hh", "h_body", eq_label="hh_outer")
        p.choose("tt", "hh_outer", eq_label="tt_outer")
        p.split("tt_outer", "(h_tup, _h_rest)")
        # Empty_pt = Tup_pt h t contradicts TUP_PT_NEQ_EMPTY_PT.
        p.have("h_neq: ~(Tup_pt hh tt = Empty_pt)").by(
            TUP_PT_NEQ_EMPTY_PT, "hh", "tt"
        )
        p.have("h_eq_sym: Tup_pt hh tt = Empty_pt").by_thm(
            SYM(p.fact("h_tup"))
        )
        p.absurd().by_conj("h_neq", "h_eq_sym")


@proof
def PROOF_PRST_CONS(p):
    """|- !h t n. Proof_PRST (Tup_pt h t) n =
            ( n = h
              /\\ ( is_pr_axiom h
                  \\/ (?f g. Proof_PRST t f
                              /\\ Proof_PRST t (Imp_pf f g)
                              /\\ h = g))).

    SORRY: the `?h0 t0. Tup_pt h t = Tup_pt h0 t0 /\\ P(h0, t0)` form
    produced by PROOF_PRST_AT collapses to `P(h, t)` via TUP_PT_INJ,
    but the DSL's CHOOSE_WITNESS-based elimination produces SELECT
    terms that REWRITE_RULE refuses to rewrite under the inner `?f g.`
    binder (see `_bottom_up` line 998: rules with non-empty asl are
    filtered out under binders). Downstream consumers can use
    PROOF_PRST_AT directly; CONS is convenience, not load-bearing.
    """
    p.goal(
        "!h t n. Proof_PRST (Tup_pt h t) n = "
        "( n = h "
        "  /\\ ( is_pr_axiom h "
        "      \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) /\\ h = g)))",
        types={"h": nat0_ty, "t": nat0_ty, "n": nat0_ty},
    )
    p.sorry()
    return  # unreachable; kept code below for future try
    from prst_syntax import TUP_PT_INJ
    from tactics import SPECL, REFL, SYM, CONJ
    from fusion import TRANS
    p.fix("h t n")
    # Reduce LHS via PROOF_PRST_AT.
    at_tup = SPECL(
        [p._parse("Tup_pt h t"), p._parse("n")], PROOF_PRST_AT
    )
    # at_tup: Proof_PRST (Tup_pt h t) n = ?h' t'. Tup_pt h t = Tup_pt h' t' /\ ...
    # Strategy: prove both directions of the iff between the body's
    # outer existential and the goal's CONS-form RHS, then chain through
    # at_tup.
    rhs_body_str = (
        "n = h /\\ ( is_pr_axiom h "
        "          \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf t f g for clarity) ))"
    )
    # forward: ?h' t'. ... ==> RHS  (CHOOSE + TUP_PT_INJ).
    inner_ex_str = (
        "?h0 t0. Tup_pt h t = Tup_pt h0 t0 /\\ n = h0 /\\ "
        "  (is_pr_axiom h0 \\/ "
        "   (?f g. Proof_PRST t0 f /\\ Proof_PRST t0 (Imp_pf f g) /\\ h0 = g))"
    )
    rhs_cons_str = (
        "n = h /\\ ( is_pr_axiom h "
        "          \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) "
        "                    /\\ h = g))"
    )
    # fwd built at the kernel level to avoid p.choose's SELECT-binder
    # explosion under by_rewrite_of (the inner SELECT pulls the whole
    # body into every reference of h0 / t0).
    from fusion import ASSUME
    from tactics import CHOOSE_WITNESS, DISCH, REWRITE_RULE, MP, CONJUNCT1, CONJUNCT2
    from basics import rand, rator
    inner_ex_term = p._parse(inner_ex_str)
    h_ex_th = ASSUME(inner_ex_term)
    # Outer existential ?h0. ?t0. <body>: pull out h0 via CHOOSE_WITNESS,
    # then t0 via another CHOOSE_WITNESS. The "witness" terms produced
    # are SELECT terms but they are NOT free vars, so REWRITE_RULE
    # against TUP_PT_INJ's projections rewrites the entire body in one
    # pass (no recursion through the SELECT body).
    outer_pred = rand(inner_ex_term)
    chose_h0 = CHOOSE_WITNESS(outer_pred, h_ex_th)
    inner_pred = rand(chose_h0._concl)
    chose_both = CHOOSE_WITNESS(inner_pred, chose_h0)
    # chose_both: |- (Tup_pt h t = Tup_pt h0_wit t0_wit) /\ <rest>
    h_tup_th = CONJUNCT1(chose_both)
    rest_th = CONJUNCT2(chose_both)
    # Apply TUP_PT_INJ to h_tup_th to get (h = h0_wit) /\ (t = t0_wit).
    # h_tup_th: Tup_pt h t = Tup_pt h0_wit t0_wit. TUP_PT_INJ gives
    # h = h0_wit /\ t = t0_wit; SYM each gets h0_wit = h, t0_wit = t.
    h0_wit = rand(rator(rand(h_tup_th._concl)))
    t0_wit = rand(rand(h_tup_th._concl))
    inj_th = MP(
        SPECL([p._parse("h"), p._parse("t"), h0_wit, t0_wit], TUP_PT_INJ),
        h_tup_th,
    )
    h_eq_inj = SYM(CONJUNCT1(inj_th))  # h0_wit = h
    t_eq_inj = SYM(CONJUNCT2(inj_th))  # t0_wit = t
    rest_h_eq_t = REWRITE_RULE([h_eq_inj, t_eq_inj], rest_th)
    # rest_h_eq_t: |- (n = h) /\ (is_pr_axiom h \/ ...) with h_assumption (inner_ex_term) as hyp.
    fwd_th = DISCH(inner_ex_term, rest_h_eq_t)
    p.have("fwd: (" + inner_ex_str + ") ==> " + rhs_cons_str).by_thm(fwd_th)
    # backward: RHS ==> ?h' t'. ...   (witness h, t)
    with p.have("bwd: " + rhs_cons_str + " ==> (" + inner_ex_str + ")").proof():
        p.assume("h_rhs: " + rhs_cons_str)
        p.have(
            "h_refl_tup: Tup_pt h t = Tup_pt h t"
        ).by_thm(REFL(p._parse("Tup_pt h t")))
        # Build the inner conjunction body for the witness (h, t).
        p.have(
            "h_inner: Tup_pt h t = Tup_pt h t /\\ n = h /\\ "
            "         (is_pr_axiom h \\/ "
            "          (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) "
            "                 /\\ h = g))"
        ).by_thm(CONJ(p.fact("h_refl_tup"), p.fact("h_rhs")))
        p.thus(inner_ex_str).by_exists(["h", "t"], "h_inner")
    p.have("iff_body: (" + inner_ex_str + ") = " + rhs_cons_str).by_iff("fwd", "bwd")
    p.thus(
        "Proof_PRST (Tup_pt h t) n = " + rhs_cons_str
    ).by_thm(TRANS(at_tup, p.fact("iff_body")))


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

    One-line proof: witness ``p := Tup_pt n Empty_pt``, the at-form
    body ``?h t. Tup_pt n Empty_pt = Tup_pt h t /\\ n = h /\\
    (is_pr_axiom h \\/ ...)`` discharges by witnessing ``h := n``,
    ``t := Empty_pt`` and picking the ``is_pr_axiom`` branch of the
    disjunction.

    Bypasses PROOF_PRST_CONS (which has DSL/SELECT friction) and goes
    through PROOF_PRST_AT directly.
    """
    from tactics import SPECL, REFL, SYM
    p.goal("!n. is_pr_axiom n ==> Prov_PRST n", types={"n": nat0_ty})
    p.fix("n")
    p.assume("h_ax: is_pr_axiom n")
    # Step 1: build Proof_PRST (Tup_pt n Empty_pt) n via PROOF_PRST_AT.
    at_pn = SPECL(
        [p._parse("Tup_pt n Empty_pt"), p._parse("n")], PROOF_PRST_AT
    )
    # at_pn: Proof_PRST (Tup_pt n Empty_pt) n = ?h t. <body>.
    # Build the body witnessing h := n, t := Empty_pt.
    p.have("h_refl_tup: Tup_pt n Empty_pt = Tup_pt n Empty_pt").by_thm(
        REFL(p._parse("Tup_pt n Empty_pt"))
    )
    p.have("h_refl_n: n = n").by_thm(REFL(p._parse("n")))
    p.have(
        "h_disj: is_pr_axiom n "
        "        \\/ (?f g. Proof_PRST Empty_pt f "
        "                   /\\ Proof_PRST Empty_pt (Imp_pf f g) /\\ n = g)"
    ).by_disj("h_ax")
    # Need fresh bound names to avoid the alpha trap.
    p.have(
        "h_ex: ?hh tt. Tup_pt n Empty_pt = Tup_pt hh tt "
        "      /\\ n = hh "
        "      /\\ (is_pr_axiom hh "
        "          \\/ (?f g. Proof_PRST tt f "
        "                    /\\ Proof_PRST tt (Imp_pf f g) /\\ hh = g))"
    ).by_exists(["n", "Empty_pt"], "h_refl_tup", "h_refl_n", "h_disj")
    # Bridge to Proof_PRST (Tup_pt n Empty_pt) n via at_pn (SYM).
    p.have(
        "h_proof: Proof_PRST (Tup_pt n Empty_pt) n"
    ).by_eq_mp(SYM(at_pn), "h_ex")
    # Wrap in Prov_PRST via PROV_PRST_AT.
    p.have("h_exists: ?p. Proof_PRST p n").by_exists(
        ["Tup_pt n Empty_pt"], "h_proof"
    )
    p.thus("Prov_PRST n").by_unfold("h_exists", PROV_PRST_AT)


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


# Helper: lift `is_pr_def n` to `is_pr_axiom n` via DISJ1 of
# `is_pr_def n \/ is_logical_axiom n` (the body of IS_PR_AXIOM_DEF).
def _is_pr_axiom_from_pr_def(p, axiom_name_str, is_pr_def_fact):
    """Inside an @proof body, derive `is_pr_axiom <axiom_name>` from a
    fact `is_pr_def <axiom_name>` via DISJ1 + IS_PR_AXIOM_DEF unfold.
    `axiom_name_str` is parenthesised so multi-token forms like
    'proj_def_axiom_at i n' parse correctly."""
    n_paren = "(" + axiom_name_str + ")"
    p.have(
        "h_disj: is_pr_def " + n_paren + " "
        "\\/ is_logical_axiom " + n_paren
    ).by_disj(is_pr_def_fact)
    p.have("h_axiom: is_pr_axiom " + n_paren).by_unfold(
        "h_disj", IS_PR_AXIOM_DEF
    )


@proof
def PROV_PRST_ZERO_DEF(p):
    """|- Prov_PRST zero_def_axiom.

    IS_PR_DEF_HOLDS_ZERO + DISJ1 to lift into is_pr_axiom + SPEC of
    PROV_PRST_AXIOM at zero_def_axiom.
    """
    p.goal("Prov_PRST zero_def_axiom")
    p.have("h_pr_def: is_pr_def zero_def_axiom").by_thm(IS_PR_DEF_HOLDS_ZERO)
    _is_pr_axiom_from_pr_def(p, "zero_def_axiom", "h_pr_def")
    p.thus("Prov_PRST zero_def_axiom").by(
        PROV_PRST_AXIOM, "zero_def_axiom", "h_axiom"
    )


# adj_sym is a primitive PR symbol -- no defining equation, hence no
# PROV_PRST_ADJ_DEF theorem. The downstream "concrete" form
# PROV_PRST_ADJ_DEF_AT is the reflexive equation App_pt adj_sym [x; y]
# = Adj_pt x y, which is REFL (Adj_pt unfolds to the App_pt
# expression). Listed below for symmetry with the other defining
# theorems; trivial discharge.


@proof
def PROV_PRST_PROJ_DEF(p):
    """|- !i n. nat0_lt i n ==> Prov_PRST (proj_def_axiom_at i n)."""
    p.goal(
        "!i n. nat0_lt i n ==> Prov_PRST (proj_def_axiom_at i n)",
        types={"i": nat0_ty, "n": nat0_ty},
    )
    p.fix("i n")
    p.assume("h_lt: nat0_lt i n")
    p.have("h_pr_def: is_pr_def (proj_def_axiom_at i n)").by(
        IS_PR_DEF_HOLDS_PROJ, "i", "n", "h_lt"
    )
    _is_pr_axiom_from_pr_def(p, "proj_def_axiom_at i n", "h_pr_def")
    p.thus("Prov_PRST (proj_def_axiom_at i n)").by(
        PROV_PRST_AXIOM, "proj_def_axiom_at i n", "h_axiom"
    )


@proof
def PROV_PRST_IF_IN_TRUE_DEF(p):
    """|- Prov_PRST if_in_true_def_axiom."""
    p.goal("Prov_PRST if_in_true_def_axiom")
    p.have("h_pr_def: is_pr_def if_in_true_def_axiom").by_thm(
        IS_PR_DEF_HOLDS_IF_IN_TRUE
    )
    _is_pr_axiom_from_pr_def(p, "if_in_true_def_axiom", "h_pr_def")
    p.thus("Prov_PRST if_in_true_def_axiom").by(
        PROV_PRST_AXIOM, "if_in_true_def_axiom", "h_axiom"
    )


@proof
def PROV_PRST_IF_IN_FALSE_DEF(p):
    """|- Prov_PRST if_in_false_def_axiom."""
    p.goal("Prov_PRST if_in_false_def_axiom")
    p.have("h_pr_def: is_pr_def if_in_false_def_axiom").by_thm(
        IS_PR_DEF_HOLDS_IF_IN_FALSE
    )
    _is_pr_axiom_from_pr_def(p, "if_in_false_def_axiom", "h_pr_def")
    p.thus("Prov_PRST if_in_false_def_axiom").by(
        PROV_PRST_AXIOM, "if_in_false_def_axiom", "h_axiom"
    )


@proof
def PROV_PRST_REC_BASE_DEF(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (rec_base_def_axiom_at g h)."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("h_conj: is_pr_sym g /\\ is_pr_sym h")
    p.have("h_pr_def: is_pr_def (rec_base_def_axiom_at g h)").by(
        IS_PR_DEF_HOLDS_REC_BASE, "g", "h", "h_conj"
    )
    _is_pr_axiom_from_pr_def(p, "rec_base_def_axiom_at g h", "h_pr_def")
    p.thus("Prov_PRST (rec_base_def_axiom_at g h)").by(
        PROV_PRST_AXIOM, "rec_base_def_axiom_at g h", "h_axiom"
    )


@proof
def PROV_PRST_REC_STEP_DEF(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (rec_step_def_axiom_at g h)."""
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (rec_step_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("h_conj: is_pr_sym g /\\ is_pr_sym h")
    p.have("h_pr_def: is_pr_def (rec_step_def_axiom_at g h)").by(
        IS_PR_DEF_HOLDS_REC_STEP, "g", "h", "h_conj"
    )
    _is_pr_axiom_from_pr_def(p, "rec_step_def_axiom_at g h", "h_pr_def")
    p.thus("Prov_PRST (rec_step_def_axiom_at g h)").by(
        PROV_PRST_AXIOM, "rec_step_def_axiom_at g h", "h_axiom"
    )


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
#                                     (Tup_pt x (Tup_pt y Empty_pt)))
#                                   (Adj_pt x y)).
#
# Trivial discharge: Adj_pt is defined as App_pt adj_sym (Tup_pt x
# (Tup_pt y Empty_pt)), so the equation is the PRST-internal REFL on
# that term. The reason to state it as a named lemma is so downstream
# code can chain through "App_pt adj_sym ... = Adj_pt ..." without
# unfolding Adj_pt manually.


@proof
def PROV_PRST_ADJ_DEF_AT(p):
    """|- !x y. Prov_PRST (Eq_pf (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt)))
                                 (Adj_pt x y)).

    The PRST-internal reflexivity of adj_sym applied to its arguments
    against the Adj_pt alias. Discharge: unfold Adj_pt, REFL, package
    via PRST equality axioms. STUB.
    """
    p.goal(
        "!x y. Prov_PRST (Eq_pf (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))) "
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
#            /\ App_pt f (Tup_pt q args) = T_pt
#            ==> App_pt f (Tup_pt (App_pt (mu_sym f) args) args) = T_pt.
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
            /\\ App_pt f (Tup_pt q args) = T_pt
            ==> App_pt f (Tup_pt (App_pt (mu_sym f) args) args) = T_pt.

    The mu-correctness axiom (HOL-level statement; reflected into PRST
    via PROV_PRST_AXIOM at concrete (f, q, args) when used inside a
    Prov_PRST derivation). This is the only axiom about mu_sym and the
    only non-strict-PR commitment in the PRST + mu extension. Soundness
    holds in the standard nat0 HOL model under the convention that
    mu_sym f returns the classical least witness when one exists. STUB.
    """
    p.goal(
        "!f q args. is_partial_pr_sym f "
        "           /\\ App_pt f (Tup_pt q args) = T_pt "
        "           ==> App_pt f (Tup_pt (App_pt (mu_sym f) args) args) = T_pt",
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
#                                  (Tup_pt F (Tup_pt (App_pt numeral_pr
#                                                       (Tup_pt n Empty_pt))
#                                                    (Tup_pt v Empty_pt))))
#                             <result computed at HOL level>).
#
# Free evaluation of PR-symbol applications inside Prov_PRST.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_SUBSTITUTE_EVAL(p):
    """|- !F t v. Prov_PRST (Eq_pf (App_pt substitute_pr
                                    (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt))))
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
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_NUMERAL_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt))
                               (numeral n)).

    Similar to PROV_PRST_SUBSTITUTE_EVAL, for numeral. STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt)) (numeral n))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_DIAG_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n)).

    From DIAG_PR_DEFINING + PROV_PRST_SUBSTITUTE_EVAL + PROV_PRST_NUMERAL_EVAL,
    chained via PRST equality reasoning (PROV_PRST_EQ_TRANS). STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n))",
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
#                             (Tup_pt (App_pt find_proof_pr
#                                       (Tup_pt (Var_pt var_x) Empty_pt))
#                                     (Tup_pt (Var_pt var_x) Empty_pt)))
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
    "         (Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
    "           (Tup_pt (Var_pt var_x) Empty_pt))) "
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
