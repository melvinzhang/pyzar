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
#   * PR-defining-equation axiom instances (one per registered PR symbol's
#     defining clause, after optional term substitution). Recognised by
#     ``is_pr_def_instance`` from prst_pr.
#
# So:
#
#   is_pr_axiom n   :<=>   is_pr_def_instance n
#                          \/ is_pr_refl n
#                          \/ is_logical_axiom n.
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
# Specialisation of free Var_pt indices is handled by the axiom-instance
# recogniser: substituting into a PR-defining template produces an
# is_pr_def_instance, hence a PRST axiom.
#
# This file re-uses hf_proof's logical axiom schemas (IS_K / IS_S /
# ... / IS_SUBST), wraps them under is_pr_axiom, and defines the new
# closure predicate. Estimate: ~400 lines once filled in.
# ---------------------------------------------------------------------------


from fusion import Var, new_axiom
from basics import mk_const, mk_app
from parser import define, parse_type, parse
from nat0 import nat0_ty
from proof import proof, define_with_at
from nat0_order import define_wf_lt
from hf_proof import (
    IS_LOGICAL_AXIOM_DEF,  # noqa: F401  -- re-used: propositional fragment only
    IS_LOGICAL_AXIOM_AT,  # noqa: F401  -- re-used
    is_mp,  # noqa: F401
)
from hf_repr_core import (
    quote_hf,  # noqa: F401  -- parser alias for PROV_PRST_NUMERAL_EVAL
    substitute,  # noqa: F401  -- parser alias for PROV_PRST_SUBSTITUTE_EVAL
)
from hf_godel1 import (
    diag,  # noqa: F401  -- parser alias for PROV_PRST_DIAG_EVAL
)
from prst_pr import (
    is_pr_def,  # noqa: F401  -- parser alias
    is_pr_def_instance,  # noqa: F401  -- parser alias
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
    eq_nat_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    or_bool_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    and_bool_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    is_tup_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    tup_head_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    mem_t_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    exists_mp_witness_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    valid_step_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    valid_proof_list_pr,  # noqa: F401  -- parser alias for checker correctness stubs
    Proof_PRST_pr,  # noqa: F401  -- parser alias
    find_proof_pr,  # noqa: F401  -- parser alias for Prov_PRST_internal
    T_pt,  # noqa: F401  -- parser alias for MU_CORRECTNESS
    F_pt,  # noqa: F401  -- parser alias for false PR-evaluation internalisation
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
    IS_PR_DEF_INSTANCE_FROM_DEF,
    IS_PR_DEF_INSTANCE_SUBST,
    IS_PR_SYM_PROOF_PRST_PR,
)
from hf_proof import (
    var_x,  # noqa: F401  -- parser alias
)
from prst_syntax import (
    Imp_pf,  # noqa: F401  -- parser alias for is_pr_axiom
    Eq_pf,  # noqa: F401  -- parser alias for Prov_PRST_internal
    Not_pf,  # noqa: F401  -- parser alias for substitute_pr clauses
    In_pa,  # noqa: F401  -- parser alias for substitute_pr clauses
    is_pterm,  # noqa: F401  -- parser alias for is_pr_refl
    Var_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
    App_pt,  # noqa: F401  -- parser alias for Prov_PRST_internal
    Tup_pt,  # noqa: F401  -- parser alias; args- and proof-list cons cells
    Empty_pt,  # noqa: F401  -- parser alias; nil-tuple / empty proof list
)


# ---------------------------------------------------------------------------
# Stage 2B (a) -- the PRST axiom recogniser.
#
# is_pr_axiom n  <=>  is_pr_def_instance n
#                     \/ is_pr_refl n
#                     \/ is_logical_axiom n.
#
# is_pr_def_instance from prst_pr.py recognises defining equations for the PR
# function symbols and their term-substitution instances.
#
# is_pr_refl is PRST-local equality reflexivity over is_pterm/Eq_pf. HF's
# inherited is_Refl ranges over is_term/Eq_f, which does not cover App_pt and
# Tup_pt terms.
#
# adj_sym has no defining equation -- it is a primitive PR symbol whose
# semantics is fixed by the standard nat0 HOL model, not by an axiom.
# ---------------------------------------------------------------------------


IS_PR_REFL_DEF, IS_PR_REFL_AT = define_with_at(
    "is_pr_refl",
    parse_type("nat0 -> bool"),
    "\\n:nat0. ?t:nat0. is_pterm t /\\ n = Eq_pf t t",
)
is_pr_refl = mk_const("is_pr_refl", [])


IS_PR_AXIOM_DEF, IS_PR_AXIOM_AT = define_with_at(
    "is_pr_axiom",
    parse_type("nat0 -> bool"),
    "\\n:nat0. is_pr_def_instance n \\/ is_pr_refl n \\/ is_logical_axiom n",
)
is_pr_axiom = mk_const("is_pr_axiom", [])


@proof
def IS_PR_REFL_HOLDS(p):
    """|- !t. is_pterm t ==> is_pr_refl (Eq_pf t t)."""
    from tactics import REFL

    p.goal("!t. is_pterm t ==> is_pr_refl (Eq_pf t t)", types={"t": nat0_ty})
    p.fix("t")
    p.assume("h_pt: is_pterm t")
    p.have("h_refl: Eq_pf t t = Eq_pf t t").by_thm(
        REFL(p._parse("Eq_pf t t"))
    )
    p.have("h_ex: ?u. is_pterm u /\\ Eq_pf t t = Eq_pf u u").by_exists(
        ["t"], "h_pt", "h_refl"
    )
    p.thus("is_pr_refl (Eq_pf t t)").by_unfold("h_ex", IS_PR_REFL_DEF)

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
              ==> _Proof_PRST_F f p = _Proof_PRST_F g p.

    Body has an inner ?f' g'. with two recursive calls (rec t f',
    rec t (Imp_pf f' g')) on the SAME tail t. Existing hf_syntax
    mono_iff_* helpers are built for pointwise-rewrite shapes; here we
    proceed at function-equation level instead: derive `f t = g t`
    (a function equation over nat0 -> bool) once, then propagate
    through the body via kernel-level AP_THM / OR_CONG / MK_COMB.

    DSL friction (inline notes below): the `_bottom_up` line-998 filter
    excludes rules with non-empty asl from REWRITE under binders, so the
    inner ?f' g'. block can't accept `f t = g t` as a REWRITE rule. The
    kernel-level approach avoids that filter entirely by building each
    equality step by hand.
    """
    from tactics import (
        AP_TERM, AP_THM, BETA_CONV, OR_CONG, SPEC, SPECL, MP, REFL, SYM, TRANS,
    )
    from fusion import DEDUCT_ANTISYM_RULE, MK_COMB, ABS, aty
    from basics import mk_const, mk_app, mk_abs, mk_eq, rand, rator
    from axioms import mk_exists, mk_or, mk_and
    from prst_syntax import NAT0_LT_TUP_PT_R

    # DSL friction: there is no public MK_EXISTS / EXISTS_CONG helper to
    # lift `body1 = body2` to `(?v. body1) = (?v. body2)`. We build it
    # inline as AP_TERM(? : (v.ty -> bool) -> bool, ABS(v, eq)).
    def MK_EXISTS_CONG(v_var, eq_th):
        exists_c = mk_const("?", [(v_var.ty, aty)])
        return AP_TERM(exists_c, ABS(v_var, eq_th))

    rec_ty = parse_type("nat0 -> nat0 -> bool")
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_Proof_PRST_F f p = _Proof_PRST_F g p",
        types={
            "f": rec_ty,
            "g": rec_ty,
            "p": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g p")
    p.assume("h_hyp: !k. nat0_lt k p ==> f k = g k")
    h_hyp_th = p.fact("h_hyp")

    # Term-level building blocks for the body.
    f_const = p._parse("f")
    g_const = p._parse("g")
    p_const = p._parse("p")
    n_var = Var("n", nat0_ty)
    h_var = Var("h", nat0_ty)
    t_var = Var("t", nat0_ty)
    # DSL friction: the inner ?f g. existential in _PROOF_PRST_F_DEF uses
    # bvars literally named `f` and `g` (of type nat0). These collide with
    # the recursion functions f, g (of type nat0 -> nat0 -> bool) only at
    # the Python-Var-name level -- different types make them distinct
    # kernel Vars, and the kernel handles the scoping correctly. We MUST
    # match the def's bvar names exactly so post-BETA terms are
    # syntactically identical (TRANS uses syntactic equality, not aconv).
    fp_var = Var("f", nat0_ty)
    gp_var = Var("g", nat0_ty)
    Tup_pt_c = mk_const("Tup_pt", [])
    Imp_pf_c = mk_const("Imp_pf", [])
    is_pr_axiom_c = mk_const("is_pr_axiom", [])

    def inner_body(rec_t_expr):
        # rec_t_expr f' /\ rec_t_expr (Imp_pf f' g') /\ h = g'
        imp_app = mk_app(mk_app(Imp_pf_c, fp_var), gp_var)
        return mk_and(
            mk_app(rec_t_expr, fp_var),
            mk_and(
                mk_app(rec_t_expr, imp_app),
                mk_eq(h_var, gp_var),
            ),
        )

    def inner_ex(rec_t_expr):
        # ?f' g'. inner_body(rec_t_expr)
        return mk_exists(fp_var, mk_exists(gp_var, inner_body(rec_t_expr)))

    def disj_body(rec_t_expr):
        # is_pr_axiom h \/ inner_ex(rec_t_expr)
        return mk_or(mk_app(is_pr_axiom_c, h_var), inner_ex(rec_t_expr))

    def full_body(rec_const):
        # p = Tup_pt h t /\ n = h /\ disj_body(rec_const t)
        rec_t = mk_app(rec_const, t_var)
        return mk_and(
            mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var)),
            mk_and(
                mk_eq(n_var, h_var),
                disj_body(rec_t),
            ),
        )

    def outer_ex(rec_const):
        # ?h t. full_body(rec_const)
        return mk_exists(h_var, mk_exists(t_var, full_body(rec_const)))

    # Step 1: prove `?h t. full_body[f]  =  ?h t. full_body[g]`.
    # We need a per-(h, t) iff and then lift via MK_EXISTS (built by ABS
    # + AP_TERM(?, ...)).
    #
    # Strategy for the per-(h, t) iff: build the equation
    #     `full_body[f] = full_body[g]`
    # as a theorem with assumption `p = Tup_pt h t` (the constructor
    # equality). Under that assumption, NAT0_LT_TUP_PT_R + h_hyp gives
    # `f t = g t`, and AP_THM swaps `f t X` ↔ `g t X` at each application.
    #
    # Then DISCH the assumption to get `(p = Tup_pt h t) ==> body[f] = body[g]`.
    # But that's still not the iff of the bodies themselves -- the iff has
    # `p = Tup_pt h t` as a conjunct, so an inner iff equating the bodies
    # *includes* the conjunct, hence can use it.
    #
    # Use DEDUCT_ANTISYM on the inner conjunction.

    from fusion import ASSUME
    from tactics import DISCH

    # Assume the full body with rec = f. Then we have p = Tup_pt h t
    # available, hence f t = g t, hence inner_ex[f] = inner_ex[g] (via
    # AP_THM), hence the disjunction is equal, hence the whole conjunction
    # is equal -- and we can EQ_MP to get body[g].

    def build_body_eq(src_rec, tgt_rec):
        """Build a theorem `[ASSUME body[src_rec]] |- body[tgt_rec]`."""
        body_src = full_body(src_rec)
        h_body_src = ASSUME(body_src)
        # Project: p_eq, rest
        from tactics import CONJUNCT1, CONJUNCT2, CONJ, DISJ_CASES, DISJ1, DISJ2
        p_eq_th = CONJUNCT1(h_body_src)  # |- p = Tup_pt h t
        rest1 = CONJUNCT2(h_body_src)  # n = h /\ disj
        n_eq_th = CONJUNCT1(rest1)
        disj_th = CONJUNCT2(rest1)  # is_pr_axiom h \/ inner_ex[src_rec t]

        # Derive nat0_lt t p:
        # NAT0_LT_TUP_PT_R: |- !a b. nat0_lt b (Tup_pt a b).
        # Specialise at (h, t): nat0_lt t (Tup_pt h t).
        # Rewrite via SYM(p_eq) to get nat0_lt t p.
        lt_tup = SPECL([h_var, t_var], NAT0_LT_TUP_PT_R)
        # lt_tup: nat0_lt t (Tup_pt h t)
        # Goal: nat0_lt t p. Use TRANS-style: have `Tup_pt h t = p` (SYM
        # p_eq), AP_TERM(nat0_lt t, ...) -> `nat0_lt t (Tup_pt h t) =
        # nat0_lt t p`, EQ_MP.
        from tactics import EQ_MP
        nat0_lt_c = mk_const("nat0_lt", [])
        nlt_t_partial = mk_app(nat0_lt_c, t_var)  # \rhs. nat0_lt t rhs (as a Comb)
        eq_lt = AP_TERM(nlt_t_partial, SYM(p_eq_th))
        # eq_lt: nat0_lt t (Tup_pt h t) = nat0_lt t p
        lt_t_p = EQ_MP(eq_lt, lt_tup)  # |- nat0_lt t p (with p_eq as asl)

        # Specialise h_hyp at t: nat0_lt t p ==> f t = g t.
        hyp_at_t = SPEC(t_var, h_hyp_th)
        # f t = g t (with p_eq as asl, plus original h_hyp's asl).
        # Note: src_rec might be f or g, so we need the right direction.
        if src_rec == f_const and tgt_rec == g_const:
            ft_eq_gt = MP(hyp_at_t, lt_t_p)  # f t = g t
        elif src_rec == g_const and tgt_rec == f_const:
            ft_eq_gt = SYM(MP(hyp_at_t, lt_t_p))  # g t = f t
        else:
            raise ValueError("src/tgt must be f/g")

        # Now lift ft_eq_gt through the inner body via AP_THM at each app.
        # Inner body: src_rec_t f' /\ src_rec_t (Imp_pf f' g') /\ h = g'
        #   where src_rec_t := src_rec t
        # Target: tgt_rec_t f' /\ tgt_rec_t (Imp_pf f' g') /\ h = g'.
        #
        # Build the function-equation lifted to applied form:
        #   eq_f1: src_rec t f' = tgt_rec t f' (AP_THM of ft_eq_gt at f')
        #   eq_f2: src_rec t (Imp_pf f' g') = tgt_rec t (Imp_pf f' g')
        eq_f1 = AP_THM(ft_eq_gt, fp_var)
        imp_app = mk_app(mk_app(Imp_pf_c, fp_var), gp_var)
        eq_f2 = AP_THM(ft_eq_gt, imp_app)

        # DSL friction: there is no public AND_CONG helper. Build it inline:
        #   from a=c, b=d derive (a/\b) = (c/\d) via MK_COMB(AP_TERM(/\, a=c), b=d).
        AND_c = mk_const("/\\", [])
        def AND_CONG(eq_l, eq_r):
            return MK_COMB(AP_TERM(AND_c, eq_l), eq_r)

        # Inner conjunct equation: (eq_f2 /\ h = g')
        inner_rest_eq = AND_CONG(eq_f2, REFL(mk_eq(h_var, gp_var)))
        # Full inner-body equation: (eq_f1 /\ (eq_f2 /\ h = g'))
        inner_body_eq = AND_CONG(eq_f1, inner_rest_eq)
        # inner_body_eq: src_rec_t f' /\ src_rec_t (...) /\ h = g'
        #                 = tgt_rec_t f' /\ tgt_rec_t (...) /\ h = g'

        # Lift to ?g' then ?f' via MK_EXISTS_CONG.
        eq_ex_g = MK_EXISTS_CONG(gp_var, inner_body_eq)
        eq_inner_ex = MK_EXISTS_CONG(fp_var, eq_ex_g)
        # eq_inner_ex: inner_ex[src_rec] = inner_ex[tgt_rec]

        # Lift through disjunction with OR_CONG.
        disj_eq = OR_CONG(REFL(mk_app(is_pr_axiom_c, h_var)), eq_inner_ex)
        # disj_eq: disj_body[src_rec] = disj_body[tgt_rec]

        # Lift through outer conjunction: (n_eq /\ disj_body) = (n_eq /\ disj_body')
        rest_eq = AND_CONG(REFL(mk_eq(n_var, h_var)), disj_eq)
        # Full body: (p_eq_term /\ rest)
        full_eq = AND_CONG(REFL(mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var))), rest_eq)
        # full_eq: full_body[src_rec] = full_body[tgt_rec]

        # Now apply full_eq to body_src to obtain body_tgt.
        body_tgt = EQ_MP(full_eq, h_body_src)
        return body_tgt  # [body_src] |- body_tgt

    body_f_to_g = build_body_eq(f_const, g_const)
    body_g_to_f = build_body_eq(g_const, f_const)

    # Build the iff of bodies at fixed (h, t).
    from fusion import ASSUME
    from tactics import DISCH
    body_f = full_body(f_const)
    body_g = full_body(g_const)
    body_iff = DEDUCT_ANTISYM_RULE(
        DISCH(body_g, body_g_to_f),
        DISCH(body_f, body_f_to_g),
    )
    # body_iff: |- full_body[f] = full_body[g]  (with h_hyp asl)
    # Wait -- DEDUCT_ANTISYM_RULE expects two implications. Actually it
    # takes two theorems and yields equality of their conclusions, with
    # one as antecedent for the other; let me re-check.

    # DSL friction note: DEDUCT_ANTISYM_RULE(t1, t2) yields `t1._concl =
    # t2._concl` with hyps from both (minus their conclusions used as
    # assumptions). With body_g_to_f : [body_g] |- body_f and
    # body_f_to_g : [body_f] |- body_g, DEDUCT_ANTISYM_RULE(body_g_to_f,
    # body_f_to_g) gives `body_g = body_f`.
    body_iff = DEDUCT_ANTISYM_RULE(body_g_to_f, body_f_to_g)
    # DEDUCT_ANTISYM_RULE(th1, th2) returns th1._concl = th2._concl. With
    # body_g_to_f (concl = body_f) and body_f_to_g (concl = body_g), the
    # result is `body_f = body_g`. No SYM needed.

    # Lift through ?h t. via MK_EXISTS_CONG.
    eq_ex_t = MK_EXISTS_CONG(t_var, body_iff)
    eq_outer_ex = MK_EXISTS_CONG(h_var, eq_ex_t)
    # eq_outer_ex: outer_ex[f] = outer_ex[g]

    # Now lift to _Proof_PRST_F f p = _Proof_PRST_F g p.
    # _Proof_PRST_F f p (after BETA) reduces to:
    #   \n. outer_ex[f]  (with rec=f everywhere)
    # Need to lift over the outer \n. ABS over n_var, then equate to the
    # unfolded def.
    eq_abs_n = ABS(n_var, eq_outer_ex)
    # eq_abs_n: (\n. outer_ex[f]) = (\n. outer_ex[g])

    # Connect to _Proof_PRST_F via def unfolding.
    # _Proof_PRST_F_DEF: _Proof_PRST_F = \rec. \p. \n. <body>
    # We want: _Proof_PRST_F f p = \n. outer_ex[f].
    # Build:  _Proof_PRST_F f = (\rec. \p. \n. body) f
    #                        = \p. \n. body[f/rec]  (BETA)
    #         _Proof_PRST_F f p = (\p. \n. body[f/rec]) p
    #                          = \n. body[f/rec, p/p]  (BETA)
    # The body[f/rec, p/p, n] = `?h t. p = Tup_pt h t /\ n = h /\ disj`
    # which is exactly outer_ex[f] (with the body's `f t` referring to
    # the substituted f).
    from fusion import INST
    def unfold_F_at(rec_const):
        # _Proof_PRST_F = \rec. \p. \n. body (rec, p, n)
        # AP_THM at rec_const: _Proof_PRST_F rec_const = (\rec. ...) rec_const
        eq0 = AP_THM(_PROOF_PRST_F_DEF, rec_const)
        # RHS is (\rec. \p. \n. body) rec_const, beta-reduce:
        rhs = rand(eq0._concl)
        beta1 = BETA_CONV(rhs)
        # beta1: (\rec. \p. \n. body) rec_const = \p. \n. body[rec_const/rec]
        eq1 = TRANS(eq0, beta1)
        # eq1: _Proof_PRST_F rec_const = \p. \n. body[rec_const/rec]
        eq2 = AP_THM(eq1, p_const)
        # eq2: _Proof_PRST_F rec_const p = (\p. \n. body[rec_const/rec]) p
        rhs2 = rand(eq2._concl)
        beta2 = BETA_CONV(rhs2)
        eq3 = TRANS(eq2, beta2)
        # eq3: _Proof_PRST_F rec_const p = \n. body[rec_const/rec, p/p]
        return eq3

    unfold_f = unfold_F_at(f_const)  # _Proof_PRST_F f p = \n. body[f]
    unfold_g = unfold_F_at(g_const)  # _Proof_PRST_F g p = \n. body[g]
    # Chain: _Proof_PRST_F f p = \n. body[f] = \n. body[g] = _Proof_PRST_F g p
    final_eq = TRANS(TRANS(unfold_f, eq_abs_n), SYM(unfold_g))

    p.thus("_Proof_PRST_F f p = _Proof_PRST_F g p").by_thm(final_eq)


_MEM_PRST_F_DEF = define(
    "_Mem_PRST_F",
    parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool"),
    "\\rec:nat0->nat0->bool. \\p:nat0. \\x:nat0. "
    "?h t. p = Tup_pt h t /\\ (x = h \\/ rec t x)",
)
_MEM_PRST_F = mk_const("_Mem_PRST_F", [])


@proof
def MEM_PRST_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
              ==> _Mem_PRST_F f p = _Mem_PRST_F g p."""
    from axioms import mk_and, mk_exists, mk_or
    from basics import mk_app, mk_const, mk_eq, rand
    from fusion import ASSUME, DEDUCT_ANTISYM_RULE, MK_COMB, ABS, aty
    from tactics import (
        AP_TERM,
        AP_THM,
        BETA_CONV,
        CONJUNCT1,
        CONJUNCT2,
        EQ_MP,
        MP,
        OR_CONG,
        REFL,
        SPEC,
        SPECL,
        SYM,
        TRANS,
    )
    from prst_syntax import NAT0_LT_TUP_PT_R

    rec_ty = parse_type("nat0 -> nat0 -> bool")
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_Mem_PRST_F f p = _Mem_PRST_F g p",
        types={"f": rec_ty, "g": rec_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h_hyp: !k. nat0_lt k p ==> f k = g k")

    def MK_EXISTS_CONG(v_var, eq_th):
        exists_c = mk_const("?", [(v_var.ty, aty)])
        return AP_TERM(exists_c, ABS(v_var, eq_th))

    AND_c = mk_const("/\\", [])

    def AND_CONG(eq_l, eq_r):
        return MK_COMB(AP_TERM(AND_c, eq_l), eq_r)

    f_const = p._parse("f")
    g_const = p._parse("g")
    p_const = p._parse("p")
    x_var = Var("x", nat0_ty)
    h_var = Var("h", nat0_ty)
    t_var = Var("t", nat0_ty)
    Tup_pt_c = mk_const("Tup_pt", [])
    nat0_lt_c = mk_const("nat0_lt", [])

    def full_body(rec_const):
        rec_t = mk_app(rec_const, t_var)
        return mk_and(
            mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var)),
            mk_or(mk_eq(x_var, h_var), mk_app(rec_t, x_var)),
        )

    def build_body_eq(src_rec, tgt_rec):
        body_src = full_body(src_rec)
        h_body_src = ASSUME(body_src)
        p_eq_th = CONJUNCT1(h_body_src)

        lt_tup = SPECL([h_var, t_var], NAT0_LT_TUP_PT_R)
        eq_lt = AP_TERM(mk_app(nat0_lt_c, t_var), SYM(p_eq_th))
        lt_t_p = EQ_MP(eq_lt, lt_tup)
        ft_eq_gt = MP(SPEC(t_var, p.fact("h_hyp")), lt_t_p)
        if src_rec == g_const and tgt_rec == f_const:
            ft_eq_gt = SYM(ft_eq_gt)

        rec_x_eq = AP_THM(ft_eq_gt, x_var)
        rest_eq = OR_CONG(REFL(mk_eq(x_var, h_var)), rec_x_eq)
        full_eq = AND_CONG(
            REFL(mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var))),
            rest_eq,
        )
        return EQ_MP(full_eq, h_body_src)

    body_f_to_g = build_body_eq(f_const, g_const)
    body_g_to_f = build_body_eq(g_const, f_const)
    body_iff = DEDUCT_ANTISYM_RULE(body_g_to_f, body_f_to_g)

    eq_ex_t = MK_EXISTS_CONG(t_var, body_iff)
    eq_ex_h = MK_EXISTS_CONG(h_var, eq_ex_t)
    eq_abs_x = ABS(x_var, eq_ex_h)

    def unfold_at(rec_const):
        eq0 = AP_THM(_MEM_PRST_F_DEF, rec_const)
        eq1 = TRANS(eq0, BETA_CONV(rand(eq0._concl)))
        eq2 = AP_THM(eq1, p_const)
        return TRANS(eq2, BETA_CONV(rand(eq2._concl)))

    unfold_f = unfold_at(f_const)
    unfold_g = unfold_at(g_const)
    p.thus("_Mem_PRST_F f p = _Mem_PRST_F g p").by_thm(
        TRANS(TRANS(unfold_f, eq_abs_x), SYM(unfold_g))
    )


MEM_PRST_DEF, _MEM_PRST_REC = define_wf_lt(
    "Mem_PRST",
    parse_type("nat0 -> nat0 -> bool"),
    _MEM_PRST_F,
    MEM_PRST_MONO,
)
Mem_PRST = mk_const("Mem_PRST", [])


_VALID_PROOF_PRST_F_DEF = define(
    "_ValidProof_PRST_F",
    parse_type("(nat0 -> bool) -> nat0 -> bool"),
    "\\rec:nat0->bool. \\p:nat0. "
    "p = Empty_pt \\/ "
    "(?h t. p = Tup_pt h t /\\ rec t /\\ "
    "       (is_pr_axiom h \\/ "
    "        (?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t)))",
)
_VALID_PROOF_PRST_F = mk_const("_ValidProof_PRST_F", [])


@proof
def VALID_PROOF_PRST_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
              ==> _ValidProof_PRST_F f p = _ValidProof_PRST_F g p."""
    from axioms import mk_and, mk_exists, mk_or
    from basics import mk_app, mk_const, mk_eq, rand
    from fusion import ASSUME, DEDUCT_ANTISYM_RULE, MK_COMB, ABS, aty
    from tactics import (
        AP_TERM,
        AP_THM,
        BETA_CONV,
        CONJUNCT1,
        CONJUNCT2,
        EQ_MP,
        MP,
        OR_CONG,
        REFL,
        SPEC,
        SPECL,
        SYM,
        TRANS,
    )
    from prst_syntax import NAT0_LT_TUP_PT_R

    rec_ty = parse_type("nat0 -> bool")
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_ValidProof_PRST_F f p = _ValidProof_PRST_F g p",
        types={"f": rec_ty, "g": rec_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h_hyp: !k. nat0_lt k p ==> f k = g k")

    def MK_EXISTS_CONG(v_var, eq_th):
        exists_c = mk_const("?", [(v_var.ty, aty)])
        return AP_TERM(exists_c, ABS(v_var, eq_th))

    AND_c = mk_const("/\\", [])

    def AND_CONG(eq_l, eq_r):
        return MK_COMB(AP_TERM(AND_c, eq_l), eq_r)

    f_const = p._parse("f")
    g_const = p._parse("g")
    p_const = p._parse("p")
    h_var = Var("h", nat0_ty)
    t_var = Var("t", nat0_ty)
    z_var = Var("f", nat0_ty)
    Tup_pt_c = mk_const("Tup_pt", [])
    Empty_pt_c = mk_const("Empty_pt", [])
    Imp_pf_c = mk_const("Imp_pf", [])
    Mem_PRST_c = mk_const("Mem_PRST", [])
    is_pr_axiom_c = mk_const("is_pr_axiom", [])
    nat0_lt_c = mk_const("nat0_lt", [])

    def mp_witness_body():
        return mk_and(
            mk_app(mk_app(Mem_PRST_c, z_var), t_var),
            mk_app(
                mk_app(Mem_PRST_c, mk_app(mk_app(Imp_pf_c, z_var), h_var)),
                t_var,
            ),
        )

    step_term = mk_or(
        mk_app(is_pr_axiom_c, h_var),
        mk_exists(z_var, mp_witness_body()),
    )

    def cons_body(rec_const):
        return mk_and(
            mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var)),
            mk_and(mk_app(rec_const, t_var), step_term),
        )

    def full_body(rec_const):
        return mk_or(
            mk_eq(p_const, Empty_pt_c),
            mk_exists(h_var, mk_exists(t_var, cons_body(rec_const))),
        )

    def build_body_eq(src_rec, tgt_rec):
        body_src = cons_body(src_rec)
        h_body_src = ASSUME(body_src)
        p_eq_th = CONJUNCT1(h_body_src)

        lt_tup = SPECL([h_var, t_var], NAT0_LT_TUP_PT_R)
        eq_lt = AP_TERM(mk_app(nat0_lt_c, t_var), SYM(p_eq_th))
        lt_t_p = EQ_MP(eq_lt, lt_tup)
        ft_eq_gt = MP(SPEC(t_var, p.fact("h_hyp")), lt_t_p)
        if src_rec == g_const and tgt_rec == f_const:
            ft_eq_gt = SYM(ft_eq_gt)

        rest_eq = AND_CONG(ft_eq_gt, REFL(step_term))
        full_eq = AND_CONG(
            REFL(mk_eq(p_const, mk_app(mk_app(Tup_pt_c, h_var), t_var))),
            rest_eq,
        )
        return EQ_MP(full_eq, h_body_src)

    body_f_to_g = build_body_eq(f_const, g_const)
    body_g_to_f = build_body_eq(g_const, f_const)
    body_iff = DEDUCT_ANTISYM_RULE(body_g_to_f, body_f_to_g)
    eq_ex_t = MK_EXISTS_CONG(t_var, body_iff)
    eq_ex_h = MK_EXISTS_CONG(h_var, eq_ex_t)
    full_eq = OR_CONG(REFL(mk_eq(p_const, Empty_pt_c)), eq_ex_h)

    def unfold_at(rec_const):
        eq0 = AP_THM(_VALID_PROOF_PRST_F_DEF, rec_const)
        eq1 = TRANS(eq0, BETA_CONV(rand(eq0._concl)))
        eq2 = AP_THM(eq1, p_const)
        return TRANS(eq2, BETA_CONV(rand(eq2._concl)))

    unfold_f = unfold_at(f_const)
    unfold_g = unfold_at(g_const)
    p.thus("_ValidProof_PRST_F f p = _ValidProof_PRST_F g p").by_thm(
        TRANS(TRANS(unfold_f, full_eq), SYM(unfold_g))
    )


VALID_PROOF_PRST_DEF, _VALID_PROOF_PRST_REC = define_wf_lt(
    "ValidProof_PRST",
    parse_type("nat0 -> bool"),
    _VALID_PROOF_PRST_F,
    VALID_PROOF_PRST_MONO,
)
ValidProof_PRST = mk_const("ValidProof_PRST", [])


_PROOF_PRST_VALID_F_DEF = define(
    "_Proof_PRST_valid_F",
    parse_type("(nat0 -> nat0 -> bool) -> nat0 -> nat0 -> bool"),
    "\\rec:nat0->nat0->bool. \\p:nat0. \\n:nat0. "
    "?h t. p = Tup_pt h t /\\ n = h /\\ ValidProof_PRST p",
)
_PROOF_PRST_VALID_F = mk_const("_Proof_PRST_valid_F", [])


@proof
def PROOF_PRST_VALID_MONO(p):
    """|- !f g p. (!k. nat0_lt k p ==> f k = g k)
              ==> _Proof_PRST_valid_F f p = _Proof_PRST_valid_F g p."""
    from basics import rand
    from tactics import AP_THM, BETA_CONV, SYM, TRANS

    rec_ty = parse_type("nat0 -> nat0 -> bool")
    p.goal(
        "!f g p. (!k. nat0_lt k p ==> f k = g k) ==> "
        "_Proof_PRST_valid_F f p = _Proof_PRST_valid_F g p",
        types={"f": rec_ty, "g": rec_ty, "p": nat0_ty, "k": nat0_ty},
    )
    p.fix("f g p")
    p.assume("h_hyp: !k. nat0_lt k p ==> f k = g k")

    def unfold_at(rec_const):
        eq0 = AP_THM(_PROOF_PRST_VALID_F_DEF, rec_const)
        eq1 = TRANS(eq0, BETA_CONV(rand(eq0._concl)))
        eq2 = AP_THM(eq1, p._parse("p"))
        return TRANS(eq2, BETA_CONV(rand(eq2._concl)))

    unfold_f = unfold_at(p._parse("f"))
    unfold_g = unfold_at(p._parse("g"))
    p.thus("_Proof_PRST_valid_F f p = _Proof_PRST_valid_F g p").by_thm(
        TRANS(unfold_f, SYM(unfold_g))
    )


Proof_PRST_def, _PROOF_PRST_REC = define_wf_lt(
    "Proof_PRST",
    parse_type("nat0 -> nat0 -> bool"),
    _PROOF_PRST_VALID_F,
    PROOF_PRST_VALID_MONO,
)
Proof_PRST = mk_const("Proof_PRST", [])


# Binary at-form of _PROOF_PRST_REC: SPEC at p, AP_THM at n, BETA on RHS.
# Result: |- !p n. Proof_PRST p n = ?h t. p = Tup_pt h t /\ n = h /\ ...
def _proof_prst_at():
    from tactics import SPEC, GEN, AP_THM, BETA_CONV, TRANS
    from basics import rand
    from prst_syntax import _unfold_prst_rec as _unfold
    eq_fun = _unfold(_PROOF_PRST_REC, _PROOF_PRST_VALID_F_DEF)
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
    """|- !n. ~ Proof_PRST Empty_pt n."""
    from tactics import SPECL, SYM
    from prst_syntax import TUP_PT_NEQ_EMPTY_PT

    p.goal("!n. ~ Proof_PRST Empty_pt n", types={"n": nat0_ty})
    p.fix("n")
    proof_at = SPECL([p._parse("Empty_pt"), p._parse("n")], PROOF_PRST_AT)
    with p.suppose("h_proof: Proof_PRST Empty_pt n"):
        p.have(
            "h_body: "
            "?h t. Empty_pt = Tup_pt h t /\\ n = h /\\ ValidProof_PRST Empty_pt"
        ).by_eq_mp(proof_at, "h_proof")
        p.choose("hd tl", "h_body", eq_label="body")
        p.split("body", "(p_eq, _)")
        p.have("p_eq_sym: Tup_pt hd tl = Empty_pt").by_thm(SYM(p.fact("p_eq")))
        p.have("p_neq: ~(Tup_pt hd tl = Empty_pt)").by(
            TUP_PT_NEQ_EMPTY_PT, "hd", "tl"
        )
        p.absurd().by_conj("p_neq", "p_eq_sym")


@proof
def PROOF_PRST_CONS(p):
    """|- !h t n. Proof_PRST (Tup_pt h t) n =
            (n = h /\\ ValidProof_PRST (Tup_pt h t))."""
    from tactics import SPECL, SYM, CONJ
    from prst_syntax import TUP_PT_INJ

    p.goal(
        "!h t n. Proof_PRST (Tup_pt h t) n = "
        "(n = h /\\ ValidProof_PRST (Tup_pt h t))",
        types={"h": nat0_ty, "t": nat0_ty, "n": nat0_ty},
    )
    p.fix("h t n")
    proof_at = SPECL([p._parse("Tup_pt h t"), p._parse("n")], PROOF_PRST_AT)

    with p.have(
        "fwd: Proof_PRST (Tup_pt h t) n ==> "
        "(n = h /\\ ValidProof_PRST (Tup_pt h t))"
    ).proof():
        p.assume("h_proof: Proof_PRST (Tup_pt h t) n")
        p.have(
            "h_body: ?h0 t0. "
            "Tup_pt h t = Tup_pt h0 t0 /\\ "
            "n = h0 /\\ ValidProof_PRST (Tup_pt h t)"
        ).by_eq_mp(proof_at, "h_proof")
        p.choose("h0 t0", "h_body", eq_label="body")
        p.split("body", "(p_eq, (n_eq0, h_valid))")
        p.have("inj: h = h0 /\\ t = t0").by(
            TUP_PT_INJ, "h", "t", "h0", "t0", "p_eq"
        )
        p.split("inj", "(h_eq0, _)")
        p.have("n_eq: n = h").by_rewrite_of("n_eq0", [SYM(p.fact("h_eq0"))])
        p.thus("n = h /\\ ValidProof_PRST (Tup_pt h t)").by(
            CONJ, "n_eq", "h_valid"
        )

    with p.have(
        "rev: (n = h /\\ ValidProof_PRST (Tup_pt h t)) ==> "
        "Proof_PRST (Tup_pt h t) n"
    ).proof():
        p.assume("(n_eq, h_valid): n = h /\\ ValidProof_PRST (Tup_pt h t)")
        p.have(
            "body: ?h0 t0. "
            "Tup_pt h t = Tup_pt h0 t0 /\\ "
            "n = h0 /\\ ValidProof_PRST (Tup_pt h t)"
        ).by_exists(["h", "t"], "n_eq", "h_valid")
        p.thus("Proof_PRST (Tup_pt h t) n").by_eq_mp(SYM(proof_at), "body")

    p.thus(
        "Proof_PRST (Tup_pt h t) n = "
        "(n = h /\\ ValidProof_PRST (Tup_pt h t))"
    ).by_iff("fwd", "rev")


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
def PROOF_PRST_SINGLETON_AX(p):
    """|- !n. is_pr_axiom n ==> Proof_PRST (Tup_pt n Empty_pt) n."""
    from tactics import SPEC, SPECL, SYM, CONJ
    from prst_syntax import _unfold_prst_rec as _unfold

    p.goal(
        "!n. is_pr_axiom n ==> Proof_PRST (Tup_pt n Empty_pt) n",
        types={"n": nat0_ty},
    )
    p.fix("n")
    p.assume("h_ax: is_pr_axiom n")

    valid_rec = _unfold(_VALID_PROOF_PRST_REC, _VALID_PROOF_PRST_F_DEF)

    empty_body = (
        "Empty_pt = Empty_pt \\/ "
        "(?h t. Empty_pt = Tup_pt h t /\\ ValidProof_PRST t /\\ "
        "       (is_pr_axiom h \\/ "
        "        (?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t)))"
    )
    valid_empty_at = SPEC(p._parse("Empty_pt"), valid_rec)
    p.have("empty_refl: Empty_pt = Empty_pt").by_rewrite([])
    p.have(f"valid_empty_body: {empty_body}").by_disj("empty_refl")
    p.have("valid_empty: ValidProof_PRST Empty_pt").by_eq_mp(
        SYM(valid_empty_at), "valid_empty_body"
    )

    p.have(
        "step_ok: is_pr_axiom n \\/ "
        "(?f. Mem_PRST f Empty_pt /\\ Mem_PRST (Imp_pf f n) Empty_pt)"
    ).by_disj("h_ax")
    p.have(
        "single_ex: ?h t. "
        "Tup_pt n Empty_pt = Tup_pt h t /\\ ValidProof_PRST t /\\ "
        "(is_pr_axiom h \\/ "
        " (?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t))"
    ).by_exists(["n", "Empty_pt"], "valid_empty", "step_ok")

    single_body = (
        "Tup_pt n Empty_pt = Empty_pt \\/ "
        "(?h t. Tup_pt n Empty_pt = Tup_pt h t /\\ ValidProof_PRST t /\\ "
        "       (is_pr_axiom h \\/ "
        "        (?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t)))"
    )
    valid_single_at = SPEC(p._parse("Tup_pt n Empty_pt"), valid_rec)
    p.have(f"valid_single_body: {single_body}").by_disj("single_ex")
    p.have("valid_single: ValidProof_PRST (Tup_pt n Empty_pt)").by_eq_mp(
        SYM(valid_single_at), "valid_single_body"
    )

    p.have("n_refl: n = n").by_rewrite([])
    p.have("proof_view: n = n /\\ ValidProof_PRST (Tup_pt n Empty_pt)").by(
        CONJ, "n_refl", "valid_single"
    )
    proof_cons = SPECL(
        [p._parse("n"), p._parse("Empty_pt"), p._parse("n")], PROOF_PRST_CONS
    )
    p.thus("Proof_PRST (Tup_pt n Empty_pt) n").by_eq_mp(
        SYM(proof_cons), "proof_view"
    )


@proof
def PROV_PRST_AX(p):
    """|- !n. is_pr_axiom n ==> Prov_PRST n.

    Witness the singleton proof list via PROOF_PRST_SINGLETON_AX, then fold
    through Prov_PRST.
    """
    from tactics import SPEC, SYM

    p.goal("!n. is_pr_axiom n ==> Prov_PRST n", types={"n": nat0_ty})
    p.fix("n")
    p.assume("h_ax: is_pr_axiom n")
    p.have("proof_n: Proof_PRST (Tup_pt n Empty_pt) n").by(
        PROOF_PRST_SINGLETON_AX, "n", "h_ax"
    )
    p.have("ex_n: ?p. Proof_PRST p n").by_exists(
        ["Tup_pt n Empty_pt"], "proof_n"
    )
    p.thus("Prov_PRST n").by_eq_mp(
        SYM(SPEC(p._parse("n"), PROV_PRST_AT)), "ex_n"
    )


# ---------------------------------------------------------------------------
# Stage 2B (d.1) -- the PR-defining-equation axioms.
#
# Moved here from prst_pr because they refer to Prov_PRST.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 2B (d.1) -- PR-defining-equation theorems as one-line
# specialisations of PROV_PRST_AX.
#
# Each axiom godelnum (from prst_pr) is in is_pr_def, hence is in
# is_pr_def_instance, hence is in
# is_pr_axiom, hence Prov_PRST holds of it. One MP per axiom; no fresh
# @proof body needed once the chain is in place.
#
# Pattern (filled in -- not a sorry; falls out of MP + IS_PR_DEF_HOLDS_*
# + IS_PR_DEF_INSTANCE_FROM_DEF + IS_PR_AXIOM_DEF unfolding
# + PROV_PRST_AX):
#
#     PROV_PRST_ZERO_DEF :=
#         MP PROV_PRST_AX (DISJ1 IS_PR_DEF_HOLDS_ZERO)
#     |- Prov_PRST zero_def_axiom
#
# Stubs below carry the headline statement; the body just notes the
# specialisation. No new axioms posted; once IS_PR_DEF_HOLDS_* and
# PROV_PRST_AX are real theorems, these are real theorems too.
# ---------------------------------------------------------------------------


# Helper: lift `is_pr_def n` to `is_pr_axiom n` via
# IS_PR_DEF_INSTANCE_FROM_DEF and DISJ1 of
# `is_pr_def_instance n \/ is_pr_refl n \/ is_logical_axiom n`
# (IS_PR_AXIOM_DEF).
def _is_pr_axiom_from_pr_def(p, axiom_name_str, is_pr_def_fact):
    """Inside an @proof body, derive `is_pr_axiom <axiom_name>` from a
    fact `is_pr_def <axiom_name>` via is_pr_def_instance + DISJ1 +
    IS_PR_AXIOM_DEF unfold.
    `axiom_name_str` is parenthesised so multi-token forms like
    'proj_def_axiom_at i n' parse correctly."""
    n_paren = "(" + axiom_name_str + ")"
    p.have("h_inst: is_pr_def_instance " + n_paren).by(
        IS_PR_DEF_INSTANCE_FROM_DEF, n_paren, is_pr_def_fact
    )
    p.have(
        "h_disj: is_pr_def_instance " + n_paren + " "
        "\\/ is_pr_refl " + n_paren + " "
        "\\/ is_logical_axiom " + n_paren
    ).by_disj("h_inst")
    p.have("h_axiom: is_pr_axiom " + n_paren).by_unfold(
        "h_disj", IS_PR_AXIOM_DEF
    )


@proof
def PROV_PRST_ZERO_DEF(p):
    """|- Prov_PRST zero_def_axiom.

    IS_PR_DEF_HOLDS_ZERO + DISJ1 to lift into is_pr_axiom + SPEC of
    PROV_PRST_AX at zero_def_axiom.
    """
    p.goal("Prov_PRST zero_def_axiom")
    p.have("h_pr_def: is_pr_def zero_def_axiom").by_thm(IS_PR_DEF_HOLDS_ZERO)
    _is_pr_axiom_from_pr_def(p, "zero_def_axiom", "h_pr_def")
    p.thus("Prov_PRST zero_def_axiom").by(
        PROV_PRST_AX, "zero_def_axiom", "h_axiom"
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
        PROV_PRST_AX, "proj_def_axiom_at i n", "h_axiom"
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
        PROV_PRST_AX, "if_in_true_def_axiom", "h_axiom"
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
        PROV_PRST_AX, "if_in_false_def_axiom", "h_axiom"
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
        PROV_PRST_AX, "rec_base_def_axiom_at g h", "h_axiom"
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
        PROV_PRST_AX, "rec_step_def_axiom_at g h", "h_axiom"
    )


@proof
def PROV_PRST_CONST_DEF(p):
    """|- !c. Prov_PRST (const_def_axiom_at c).

    Unconditional defining-equation theorem for const_sym -- one-line
    specialisation of PROV_PRST_AX at any c, via IS_PR_DEF_HOLDS_CONST.
    """
    from prst_pr import IS_PR_DEF_HOLDS_CONST, const_def_axiom_at  # noqa: F401
    p.goal(
        "!c. Prov_PRST (const_def_axiom_at c)",
        types={"c": nat0_ty},
    )
    p.fix("c")
    p.have("h_pr_def: is_pr_def (const_def_axiom_at c)").by(
        IS_PR_DEF_HOLDS_CONST, "c"
    )
    _is_pr_axiom_from_pr_def(p, "const_def_axiom_at c", "h_pr_def")
    p.thus("Prov_PRST (const_def_axiom_at c)").by(
        PROV_PRST_AX, "const_def_axiom_at c", "h_axiom"
    )


@proof
def PROV_PRST_COURSE_REC_BASE_DEF(p):
    """|- !g h. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (course_rec_base_def_axiom_at g h)."""
    from prst_pr import (  # noqa: F401
        IS_PR_DEF_HOLDS_COURSE_REC_BASE, course_rec_base_def_axiom_at,
    )
    p.goal(
        "!g h. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (course_rec_base_def_axiom_at g h)",
        types={"g": nat0_ty, "h": nat0_ty},
    )
    p.fix("g h")
    p.assume("h_conj: is_pr_sym g /\\ is_pr_sym h")
    p.have("h_pr_def: is_pr_def (course_rec_base_def_axiom_at g h)").by(
        IS_PR_DEF_HOLDS_COURSE_REC_BASE, "g", "h", "h_conj"
    )
    _is_pr_axiom_from_pr_def(
        p, "course_rec_base_def_axiom_at g h", "h_pr_def"
    )
    p.thus("Prov_PRST (course_rec_base_def_axiom_at g h)").by(
        PROV_PRST_AX, "course_rec_base_def_axiom_at g h", "h_axiom"
    )


@proof
def PROV_PRST_COURSE_REC_STEP_DEF(p):
    """|- !g h a b. is_pr_sym g /\\ is_pr_sym h
            ==> Prov_PRST (course_rec_step_def_axiom_at g h a b)."""
    from prst_pr import (  # noqa: F401
        IS_PR_DEF_HOLDS_COURSE_REC_STEP, course_rec_step_def_axiom_at,
    )
    p.goal(
        "!g h a b. is_pr_sym g /\\ is_pr_sym h "
        "==> Prov_PRST (course_rec_step_def_axiom_at g h a b)",
        types={"g": nat0_ty, "h": nat0_ty,
               "a": nat0_ty, "b": nat0_ty},
    )
    p.fix("g h a b")
    p.assume("h_conj: is_pr_sym g /\\ is_pr_sym h")
    p.have(
        "h_pr_def: is_pr_def (course_rec_step_def_axiom_at g h a b)"
    ).by(IS_PR_DEF_HOLDS_COURSE_REC_STEP, "g", "h", "a", "b", "h_conj")
    _is_pr_axiom_from_pr_def(
        p, "course_rec_step_def_axiom_at g h a b", "h_pr_def"
    )
    p.thus("Prov_PRST (course_rec_step_def_axiom_at g h a b)").by(
        PROV_PRST_AX, "course_rec_step_def_axiom_at g h a b", "h_axiom"
    )


@proof
def PROV_PRST_PAIR_LEFT_DEF(p):
    """|- !a b. Prov_PRST (pair_left_def_axiom_at a b)."""
    from prst_pr import (  # noqa: F401
        IS_PR_DEF_HOLDS_PAIR_LEFT, pair_left_def_axiom_at,
    )
    p.goal(
        "!a b. Prov_PRST (pair_left_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have("h_pr_def: is_pr_def (pair_left_def_axiom_at a b)").by(
        IS_PR_DEF_HOLDS_PAIR_LEFT, "a", "b"
    )
    _is_pr_axiom_from_pr_def(p, "pair_left_def_axiom_at a b", "h_pr_def")
    p.thus("Prov_PRST (pair_left_def_axiom_at a b)").by(
        PROV_PRST_AX, "pair_left_def_axiom_at a b", "h_axiom"
    )


@proof
def PROV_PRST_PAIR_RIGHT_DEF(p):
    """|- !a b. Prov_PRST (pair_right_def_axiom_at a b)."""
    from prst_pr import (  # noqa: F401
        IS_PR_DEF_HOLDS_PAIR_RIGHT, pair_right_def_axiom_at,
    )
    p.goal(
        "!a b. Prov_PRST (pair_right_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have("h_pr_def: is_pr_def (pair_right_def_axiom_at a b)").by(
        IS_PR_DEF_HOLDS_PAIR_RIGHT, "a", "b"
    )
    _is_pr_axiom_from_pr_def(p, "pair_right_def_axiom_at a b", "h_pr_def")
    p.thus("Prov_PRST (pair_right_def_axiom_at a b)").by(
        PROV_PRST_AX, "pair_right_def_axiom_at a b", "h_axiom"
    )


@proof
def PROV_PRST_PAIR_ORD_DEF(p):
    """|- !a b. Prov_PRST (pair_ord_def_axiom_at a b)."""
    from prst_pr import (  # noqa: F401
        IS_PR_DEF_HOLDS_PAIR_ORD, pair_ord_def_axiom_at,
    )
    p.goal(
        "!a b. Prov_PRST (pair_ord_def_axiom_at a b)",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.have("h_pr_def: is_pr_def (pair_ord_def_axiom_at a b)").by(
        IS_PR_DEF_HOLDS_PAIR_ORD, "a", "b"
    )
    _is_pr_axiom_from_pr_def(p, "pair_ord_def_axiom_at a b", "h_pr_def")
    p.thus("Prov_PRST (pair_ord_def_axiom_at a b)").by(
        PROV_PRST_AX, "pair_ord_def_axiom_at a b", "h_axiom"
    )


# ---------------------------------------------------------------------------
# Stage 2B (d.2) -- substitute-into-axiom derived rule.
#
# Because PRST defining equations are stated with free Var_pt indices
# (implicit universal closure convention), consumers need to specialise
# them at concrete terms. PRST is quantifier-free, so the rule does not
# come from object-level Gen + UI in the way HF gets it. Instead,
# is_pr_axiom recognises is_pr_def_instance, and prst_pr proves that
# substituting into an is_pr_def template yields such an instance.
#
#     PROV_PRST_SUBST :
#         |- !F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)
#
# This is now a theorem over the axiom-instance recogniser, not a primitive
# axiom or a sorry obligation.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_SUBST(p):
    """|- !F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)."""
    p.goal(
        "!F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.fix("F t v")
    p.assume("h_def: is_pr_def F")
    p.have("h_inst: is_pr_def_instance (substitute_p F t v)").by(
        IS_PR_DEF_INSTANCE_SUBST, "F", "t", "v", "h_def"
    )
    p.have(
        "h_disj: is_pr_def_instance (substitute_p F t v) "
        "\\/ is_pr_refl (substitute_p F t v) "
        "\\/ is_logical_axiom (substitute_p F t v)"
    ).by_disj("h_inst")
    p.have("h_axiom: is_pr_axiom (substitute_p F t v)").by_unfold(
        "h_disj", IS_PR_AXIOM_DEF
    )
    p.thus("Prov_PRST (substitute_p F t v)").by(
        PROV_PRST_AX, "substitute_p F t v", "h_axiom"
    )


# Convenience corollaries for specific axioms at specific terms.
# Each is one application of PROV_PRST_SUBST at the appropriate
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


# ---------------------------------------------------------------------------
# PROV_PRST_REFL -- reflexivity of Eq_pf for is_pterm-typed terms.
#
# This is now a derived PRST theorem. is_pr_axiom contains a PRST-local
# is_pr_refl branch over is_pterm/Eq_pf, avoiding the mismatch with HF's
# inherited is_Refl, which ranges over is_term/Eq_f.
# ---------------------------------------------------------------------------


@proof
def PROV_PRST_REFL(p):
    """|- !t. is_pterm t ==> Prov_PRST (Eq_pf t t)."""
    p.goal(
        "!t. is_pterm t ==> Prov_PRST (Eq_pf t t)",
        types={"t": nat0_ty},
    )
    p.fix("t")
    p.assume("h_pt: is_pterm t")
    p.have("h_refl: is_pr_refl (Eq_pf t t)").by(
        IS_PR_REFL_HOLDS, "t", "h_pt"
    )
    p.have(
        "h_disj: is_pr_def_instance (Eq_pf t t) "
        "\\/ is_pr_refl (Eq_pf t t) "
        "\\/ is_logical_axiom (Eq_pf t t)"
    ).by_disj("h_refl")
    p.have("h_axiom: is_pr_axiom (Eq_pf t t)").by_unfold(
        "h_disj", IS_PR_AXIOM_DEF
    )
    p.thus("Prov_PRST (Eq_pf t t)").by(
        PROV_PRST_AX, "Eq_pf t t", "h_axiom"
    )


@proof
def PROV_PRST_ADJ_DEF_AT(p):
    """|- !x y. is_pterm x /\\ is_pterm y
              ==> Prov_PRST (Eq_pf (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt)))
                                   (Adj_pt x y)).

    Signature changed from the original (which had no preconditions) to
    require `is_pterm x /\\ is_pterm y` -- the lemma is otherwise
    underivable, since PRST's inherited is_Refl schema requires is_term
    (HF-side, recognising only Var_t/Empty_t/Adj_t), and App_pt-typed
    terms aren't is_term.

    Derivation:
      1. Unfold ADJ_PT_DEF at (x, y): Adj_pt x y = App_pt adj_sym ...
         So the LHS and RHS of the Eq_pf are HOL-equal.
      2. Build is_pterm of the LHS by chaining IS_PTERM_AT_APP /
         IS_PTERM_AT_TUP / IS_PTERM_AT_EMPTY with IS_PR_SYM_ADJ +
         IS_PR_SYM_IMP_PARTIAL for the App_pt's symbol slot.
      3. By PROV_PRST_REFL at LHS: Prov_PRST (Eq_pf LHS LHS).
      4. Rewrite the second LHS to Adj_pt x y via SYM(adj_at) to recover
         the goal shape.
    """
    from prst_pr import ADJ_PT_DEF, IS_PR_SYM_ADJ
    from prst_syntax import (
        IS_PTERM_AT_APP, IS_PTERM_AT_TUP, IS_PTERM_AT_EMPTY,
        IS_PR_SYM_IMP_PARTIAL,
    )
    from tactics import SPECL, SPEC, MP, SYM, AP_TERM
    from basics import mk_const

    p.goal(
        "!x y. is_pterm x /\\ is_pterm y ==> "
        "Prov_PRST (Eq_pf (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))) "
        "                 (Adj_pt x y))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.assume("(h_x, h_y): is_pterm x /\\ is_pterm y")

    # Step 1: applied-form of ADJ_PT_DEF at (x, y).
    # adj_at: Adj_pt x y = App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt)).
    adj_at = p.unfold(ADJ_PT_DEF, "x", "y")

    # Step 2: build is_pterm of T = App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt)).
    # Bottom up: is_pterm Empty_pt; is_pterm (Tup_pt y Empty_pt); is_pterm
    # (Tup_pt x (Tup_pt y Empty_pt)); is_pterm (App_pt adj_sym ...).
    p.have("h_pt_empty: is_pterm Empty_pt").by_thm(IS_PTERM_AT_EMPTY)

    # DSL friction: IS_PTERM_AT_TUP is `is_pterm (Tup_pt a b) = is_pterm a
    # /\ is_pterm b`. To go from the conjunction to is_pterm we EQ_MP
    # backwards (SYM of the AT-equation, packaging the two parts with CONJ
    # since by_eq_mp takes a single fact). Direct CONJ call rather than
    # building via p.have(...).by_thm to keep the proof linear.
    from tactics import CONJ
    h_conj_y_empty = CONJ(p.fact("h_y"), p.fact("h_pt_empty"))
    p.have("h_pt_tup_y: is_pterm (Tup_pt y Empty_pt)").by_eq_mp(
        SYM(SPECL([p._parse("y"), p._parse("Empty_pt")], IS_PTERM_AT_TUP)),
        h_conj_y_empty,
    )
    h_conj_x_tup = CONJ(p.fact("h_x"), p.fact("h_pt_tup_y"))
    p.have("h_pt_tup_xy: is_pterm (Tup_pt x (Tup_pt y Empty_pt))").by_eq_mp(
        SYM(SPECL([p._parse("x"), p._parse("Tup_pt y Empty_pt")], IS_PTERM_AT_TUP)),
        h_conj_x_tup,
    )

    # is_partial_pr_sym adj_sym from IS_PR_SYM_ADJ + IS_PR_SYM_IMP_PARTIAL.
    p.have("h_ppr_adj: is_partial_pr_sym adj_sym").by(
        IS_PR_SYM_IMP_PARTIAL, "adj_sym", IS_PR_SYM_ADJ,
    )
    h_conj_app = CONJ(p.fact("h_ppr_adj"), p.fact("h_pt_tup_xy"))
    p.have(
        "h_pt_app: is_pterm (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt)))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("adj_sym"), p._parse("Tup_pt x (Tup_pt y Empty_pt)")],
            IS_PTERM_AT_APP,
        )),
        h_conj_app,
    )

    # Step 3: PROV_PRST_REFL at LHS.
    p.have(
        "h_refl: Prov_PRST (Eq_pf "
        "  (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))) "
        "  (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))))"
    ).by(
        PROV_PRST_REFL,
        "App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))",
        "h_pt_app",
    )

    # Step 4: rewrite the second occurrence of the App_pt term to Adj_pt x y
    # via SYM(adj_at).
    # adj_at: Adj_pt x y = App_pt adj_sym (...). SYM gives App_pt ... = Adj_pt x y.
    # AP_TERM(Eq_pf (App_pt ...), SYM(adj_at)):
    #   Eq_pf (App_pt ...) (App_pt ...) = Eq_pf (App_pt ...) (Adj_pt x y).
    Eq_pf_c = mk_const("Eq_pf", [])
    LHS_term = p._parse("App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))")
    eq_pf_lhs = mk_app(Eq_pf_c, LHS_term)
    eq_rewrite = AP_TERM(eq_pf_lhs, SYM(adj_at))
    # eq_rewrite: Eq_pf LHS LHS = Eq_pf LHS (Adj_pt x y)
    # Now lift to Prov_PRST level: Prov_PRST (Eq_pf LHS LHS) = Prov_PRST (Eq_pf LHS (Adj_pt x y))
    Prov_PRST_c = mk_const("Prov_PRST", [])
    prov_eq = AP_TERM(Prov_PRST_c, eq_rewrite)
    p.thus(
        "Prov_PRST (Eq_pf (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))) "
        "                 (Adj_pt x y))"
    ).by_eq_mp(prov_eq, "h_refl")


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
# PROV_PRST_SUBST at each use site.
# ---------------------------------------------------------------------------


MU_CORRECTNESS = new_axiom(parse(
    "!f:nat0 q:nat0 args:nat0. is_partial_pr_sym f "
    "           /\\ App_pt f (Tup_pt q args) = T_pt "
    "           ==> App_pt f (Tup_pt (App_pt (mu_sym f) args) args) = T_pt"
))


@proof
def FIND_PROOF_PR_MU_CORRECT(p):
    """|- !pf n. App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt
              ==> App_pt Proof_PRST_pr
                    (Tup_pt (App_pt find_proof_pr (Tup_pt n Empty_pt))
                            (Tup_pt n Empty_pt)) = T_pt.

    This is the mu-strength check specialized to the proof checker. It uses
    only MU_CORRECTNESS; no leastness or totality property of mu is needed.
    """
    from prst_pr import FIND_PROOF_PR_DEF, IS_PR_SYM_PROOF_PRST_PR
    from prst_syntax import IS_PR_SYM_IMP_PARTIAL
    from tactics import CONJ, SYM

    p.goal(
        "!pf n. "
        "App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt "
        "==> App_pt Proof_PRST_pr "
        "      (Tup_pt (App_pt find_proof_pr (Tup_pt n Empty_pt)) "
        "              (Tup_pt n Empty_pt)) = T_pt",
        types={"pf": nat0_ty, "n": nat0_ty},
    )
    p.fix("pf n")
    p.assume(
        "h_pf: App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt"
    )
    p.have("h_pr_proof: is_pr_sym Proof_PRST_pr").by_thm(
        IS_PR_SYM_PROOF_PRST_PR
    )
    p.have(
        "h_pp_proof: is_partial_pr_sym Proof_PRST_pr"
    ).by(IS_PR_SYM_IMP_PARTIAL, "Proof_PRST_pr", "h_pr_proof")
    p.have(
        "h_mu_payload: is_partial_pr_sym Proof_PRST_pr /\\ "
        "App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt"
    ).by_thm(CONJ(p.fact("h_pp_proof"), p.fact("h_pf")))
    p.have(
        "h_mu: App_pt Proof_PRST_pr "
        "        (Tup_pt (App_pt (mu_sym Proof_PRST_pr) (Tup_pt n Empty_pt)) "
        "                (Tup_pt n Empty_pt)) = T_pt"
    ).by(
        MU_CORRECTNESS,
        "Proof_PRST_pr",
        "pf",
        "Tup_pt n Empty_pt",
        "h_mu_payload",
    )
    p.thus(
        "App_pt Proof_PRST_pr "
        "  (Tup_pt (App_pt find_proof_pr (Tup_pt n Empty_pt)) "
        "          (Tup_pt n Empty_pt)) = T_pt"
    ).by_rewrite_of("h_mu", [SYM(FIND_PROOF_PR_DEF)])


# ---------------------------------------------------------------------------
# Stage 2B (d.4) -- Proof_PRST_pr correctness.
#
# Proof_PRST_pr is the PR-symbol mirror of the HOL-level Proof_PRST proof
# checker. Its top-level body now has the intended proof-list shape:
# head check + valid-proof-list recursion + membership-based MP search.
# The remaining constructive work is isolated in the checker API view and the
# generic PR-evaluation internalisation theorem below:
#
#   PROOF_PRST_PR_BODY_CORRECT  -- HOL-level checker-body correctness:
#                                  Proof_PRST_pr evaluates to T_pt exactly
#                                  for a proof-list shape with a valid proof.
#   PRST_INTERNALIZES_TRUE_PR_EVAL / PRST_INTERNALIZES_FALSE_PR_EVAL
#                                -- generic PRST-internal evaluation for PR
#                                   computations returning the booleans.
#
# Soundness: the PR functions are complete, so a *concrete* Proof_PRST_pr
# meeting both conditions exists. The checker API lemma is the semantic
# correctness of the implemented list checker against ValidProof_PRST's view;
# the internalisation lemma is the standard PRST evaluator package for true
# PR computations.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 2B (d.4a) -- HOL-level App_pt evaluators for the PR primitives.
#
# These lift each primitive PR-symbol's defining equation from the PRST
# proof system (Prov_PRST) to a HOL equation `App_pt sym args = result`.
# They are the missing infrastructure flagged in the section-0 friction
# comments: every checker-body component that bottoms out at `App_pt
# (comp_sym ...) ... = T_pt` needs these to unfold the composition chain.
#
# Discharge route (eventually): each is the "true" branch of the standard
# PRST evaluator package -- the same `PRST_INTERNALIZES_TRUE_PR_EVAL`
# pattern, but committed to HOL `=` instead of `Prov_PRST (Eq_pf ...)` via
# a soundness bridge. STUB. Listed here so downstream proofs can name and
# import them.
# ---------------------------------------------------------------------------


@proof
def APP_PT_PROJ_AT_HEAD(p):
    """|- !n x rest. App_pt (proj_sym 0 (SUC0 n)) (Tup_pt x rest) = x.

    Head-projection evaluator: `proj_sym 0 (n+1)` on a Tup_pt-cons returns
    the head. The general `proj_sym i n` for arbitrary i is obtained by
    induction on i using APP_PT_PROJ_AT_TAIL (below) to shift the cursor.
    """
    p.goal(
        "!n x rest. "
        "App_pt (proj_sym 0 (SUC0 n)) (Tup_pt x rest) = x",
        types={"n": nat0_ty, "x": nat0_ty, "rest": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_PROJ_AT_TAIL(p):
    """|- !i n x rest.
            App_pt (proj_sym (SUC0 i) (SUC0 n)) (Tup_pt x rest)
              = App_pt (proj_sym i n) rest.

    Tail-projection evaluator: shifts the index/arity down by one and
    drops the head from the args tuple. Together with
    APP_PT_PROJ_AT_HEAD this characterises proj_sym at every index.
    """
    p.goal(
        "!i n x rest. "
        "App_pt (proj_sym (SUC0 i) (SUC0 n)) (Tup_pt x rest) = "
        "App_pt (proj_sym i n) rest",
        types={"i": nat0_ty, "n": nat0_ty, "x": nat0_ty, "rest": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_COMP_EVAL_1(p):
    """|- !g h1 args.
            App_pt (comp_sym g (Tup_pt h1 Empty_pt)) args
              = App_pt g (Tup_pt (App_pt h1 args) Empty_pt).

    1-ary composition evaluator. Consumed by:
      - is_tup_pr unfolding `comp(eq_nat_pr, comp(pair_left_sym, proj 0 1), ...)`
      - _const_at-style 1-ary `comp(const_sym v, proj 0 1)` chains.
    """
    p.goal(
        "!g h1 args. "
        "App_pt (comp_sym g (Tup_pt h1 Empty_pt)) args = "
        "App_pt g (Tup_pt (App_pt h1 args) Empty_pt)",
        types={"g": nat0_ty, "h1": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_COMP_EVAL_2(p):
    """|- !g h1 h2 args.
            App_pt (comp_sym g (Tup_pt h1 (Tup_pt h2 Empty_pt))) args
              = App_pt g (Tup_pt (App_pt h1 args)
                            (Tup_pt (App_pt h2 args) Empty_pt)).

    2-ary composition evaluator. Consumed by:
      - Proof_PRST_pr's outer `comp(and_bool_pr, ..., ...)` layers
      - eq_nat_pr's outer `comp(if_in_sym, ...)` after the singleton/branch
        args are projected.
    """
    p.goal(
        "!g h1 h2 args. "
        "App_pt (comp_sym g (Tup_pt h1 (Tup_pt h2 Empty_pt))) args = "
        "App_pt g (Tup_pt (App_pt h1 args) "
        "                 (Tup_pt (App_pt h2 args) Empty_pt))",
        types={"g": nat0_ty, "h1": nat0_ty, "h2": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_COMP_EVAL_4(p):
    """|- !g h1 h2 h3 h4 args.
            App_pt (comp_sym g (Tup_pt h1 (Tup_pt h2 (Tup_pt h3
                                (Tup_pt h4 Empty_pt))))) args
              = App_pt g (Tup_pt (App_pt h1 args)
                            (Tup_pt (App_pt h2 args)
                              (Tup_pt (App_pt h3 args)
                                (Tup_pt (App_pt h4 args) Empty_pt)))).

    4-ary composition evaluator. Consumed by:
      - eq_nat_pr's `comp(if_in_sym, t_pr, s_pr, x_pr, y_pr)` shape
      - any other if_in_sym-rooted composition with branch args.
    """
    p.goal(
        "!g h1 h2 h3 h4 args. "
        "App_pt (comp_sym g "
        "  (Tup_pt h1 (Tup_pt h2 (Tup_pt h3 (Tup_pt h4 Empty_pt))))) args = "
        "App_pt g (Tup_pt (App_pt h1 args) "
        "          (Tup_pt (App_pt h2 args) "
        "            (Tup_pt (App_pt h3 args) "
        "              (Tup_pt (App_pt h4 args) Empty_pt))))",
        types={
            "g": nat0_ty, "h1": nat0_ty, "h2": nat0_ty,
            "h3": nat0_ty, "h4": nat0_ty, "args": nat0_ty,
        },
    )
    p.sorry()


@proof
def APP_PT_CONST_EVAL(p):
    """|- !v args. App_pt (const_sym v) args = v.

    HOL-level lift of CONST_SYM_DEF's spec: `const_sym v` is the 1-ary
    PR symbol "always return v"; on any argument tuple it evaluates to v.
    Consumed by `_const_at(v, n) := comp(const_sym v, proj(0, n))` chains
    after APP_PT_COMP_EVAL_1 has reduced the outer comp.
    """
    p.goal(
        "!v args. App_pt (const_sym v) args = v",
        types={"v": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_IF_IN_SAME_EVAL(p):
    """|- !t xv yv.
            App_pt if_in_sym (Tup_pt t (Tup_pt (Adj_pt t Empty_pt)
                          (Tup_pt xv (Tup_pt yv Empty_pt)))) = xv.

    Singleton-specialised if_in evaluator: when the set is `Adj_pt t Empty_pt`
    (i.e., the PRST singleton {t}) and the test value is t itself, if_in_sym
    returns the then-branch xv. This is the form actually used by eq_nat_pr,
    or_bool_pr, and_bool_pr, where the discriminating set is always a
    singleton.

    Avoids the HOL-level `In t s` predicate, which does not align with PRST
    set semantics (PRST sets are encoded as nested Adj_pt's, not as
    bit-encoded HF sets).
    """
    p.goal(
        "!t xv yv. "
        "App_pt if_in_sym "
        "  (Tup_pt t (Tup_pt (Adj_pt t Empty_pt) "
        "    (Tup_pt xv (Tup_pt yv Empty_pt)))) = xv",
        types={"t": nat0_ty, "xv": nat0_ty, "yv": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_IF_IN_DIFF_EVAL(p):
    """|- !t u xv yv. ~(t = u) ==>
            App_pt if_in_sym (Tup_pt t (Tup_pt (Adj_pt u Empty_pt)
                          (Tup_pt xv (Tup_pt yv Empty_pt)))) = yv.

    Singleton-specialised counterpart of APP_PT_IF_IN_SAME_EVAL: when the
    test value `t` is not equal to the singleton's element `u`, if_in_sym
    returns the else-branch yv.
    """
    p.goal(
        "!t u xv yv. ~(t = u) ==> "
        "App_pt if_in_sym "
        "  (Tup_pt t (Tup_pt (Adj_pt u Empty_pt) "
        "    (Tup_pt xv (Tup_pt yv Empty_pt)))) = yv",
        types={"t": nat0_ty, "u": nat0_ty, "xv": nat0_ty, "yv": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_ADJ_EVAL(p):
    """|- !x s. App_pt adj_sym (Tup_pt x (Tup_pt s Empty_pt)) = Adj_pt x s.

    Definitional: Adj_pt is defined as exactly this App_pt form, so this
    is just SYM(ADJ_PT_DEF unfolded at x, s).
    """
    from prst_pr import ADJ_PT_DEF
    from tactics import SYM

    p.goal(
        "!x s. App_pt adj_sym (Tup_pt x (Tup_pt s Empty_pt)) = Adj_pt x s",
        types={"x": nat0_ty, "s": nat0_ty},
    )
    p.fix("x s")
    adj_at = p.unfold(ADJ_PT_DEF, "x", "s")
    # adj_at: Adj_pt x s = App_pt adj_sym (Tup_pt x (Tup_pt s Empty_pt))
    p.thus(
        "App_pt adj_sym (Tup_pt x (Tup_pt s Empty_pt)) = Adj_pt x s"
    ).by_thm(SYM(adj_at))


@proof
def APP_PT_PAIR_LEFT_EVAL(p):
    """|- !a b. App_pt pair_left_sym (Tup_pt (Pair_ord a b) Empty_pt) = a.

    HOL-level lift of the `pair_left` defining axiom (left projection of a
    Pair_ord). Consumed wherever PR composition uses `pair_left_sym` to
    inspect a Pair_ord-encoded payload (is_tup_pr's tag check, the Tup_pt
    head/tail destructors).
    """
    p.goal(
        "!a b. App_pt pair_left_sym (Tup_pt (Pair_ord a b) Empty_pt) = a",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_PAIR_RIGHT_EVAL(p):
    """|- !a b. App_pt pair_right_sym (Tup_pt (Pair_ord a b) Empty_pt) = b.

    Right-component counterpart of APP_PT_PAIR_LEFT_EVAL.
    """
    p.goal(
        "!a b. App_pt pair_right_sym (Tup_pt (Pair_ord a b) Empty_pt) = b",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_PAIR_LEFT_TUP(p):
    """|- !a b. App_pt pair_left_sym (Tup_pt (Tup_pt a b) Empty_pt) =
            SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0
                  (SUC0 (SUC0 (SUC0 0))))))))))).

    Tup_pt-aware pair_left: when the inner value is a Tup_pt, the left
    component is the Tup_pt tag literal (= 12). Derived from
    APP_PT_PAIR_LEFT_EVAL composed with TUP_PT_AT. Sits alongside
    APP_PT_PAIR_LEFT_EVAL so that `by_rewrite` chains can reduce
    `pair_left of Tup_pt _ _` WITHOUT pulling TUP_PT_AT into the rewrite
    set (which would over-eagerly unfold the outer Tup_pt that the PR
    arg-list / proj evaluators rely on).
    """
    from prst_syntax import TUP_PT_AT, suc_chain
    from tactics import SPECL

    p.goal(
        "!a b. App_pt pair_left_sym (Tup_pt (Tup_pt a b) Empty_pt) = "
        f"({suc_chain(12)})",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.thus(
        "App_pt pair_left_sym (Tup_pt (Tup_pt a b) Empty_pt) = "
        f"({suc_chain(12)})"
    ).by_rewrite([
        SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT),
        SPECL([p._parse(suc_chain(12)), p._parse("Pair_ord a b")],
              APP_PT_PAIR_LEFT_EVAL),
    ])


@proof
def APP_PT_PAIR_RIGHT_TUP(p):
    """|- !a b. App_pt pair_right_sym (Tup_pt (Tup_pt a b) Empty_pt) =
            Pair_ord a b.

    Tup_pt-aware pair_right: drops the tag and exposes the payload pair
    `Pair_ord a b`. Same role as APP_PT_PAIR_LEFT_TUP -- lets a
    `by_rewrite` chain peel `pair_right of Tup_pt _ _` without including
    TUP_PT_AT (which would over-unfold the outer Tup_pt).
    """
    from prst_syntax import TUP_PT_AT, suc_chain
    from tactics import SPECL

    p.goal(
        "!a b. App_pt pair_right_sym (Tup_pt (Tup_pt a b) Empty_pt) = "
        "Pair_ord a b",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.thus(
        "App_pt pair_right_sym (Tup_pt (Tup_pt a b) Empty_pt) = "
        "Pair_ord a b"
    ).by_rewrite([
        SPECL([p._parse("a"), p._parse("b")], TUP_PT_AT),
        SPECL([p._parse(suc_chain(12)), p._parse("Pair_ord a b")],
              APP_PT_PAIR_RIGHT_EVAL),
    ])


@proof
def APP_PT_PAIR_ORD_EVAL(p):
    """|- !a b. App_pt pair_ord_sym (Tup_pt a (Tup_pt b Empty_pt)) = Pair_ord a b.

    PR-level Pair_ord constructor evaluator. Consumed wherever a PR
    composition has to *build* a Pair_ord (e.g. substitute_pr packaging
    (t, v) into y_vec).
    """
    p.goal(
        "!a b. App_pt pair_ord_sym (Tup_pt a (Tup_pt b Empty_pt)) = Pair_ord a b",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_REC_BASE_EVAL(p):
    """|- !g h args. App_pt (rec_sym g h) (Tup_pt zero_sym args) = App_pt g args.

    HOL-level lift of `rec_base_def_axiom_at g h`. Consumed by any PR
    symbol built with `rec(g, h)` that recurses over its first argument
    (numeral_pr-style).
    """
    p.goal(
        "!g h args. "
        "App_pt (rec_sym g h) (Tup_pt zero_sym args) = App_pt g args",
        types={"g": nat0_ty, "h": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_REC_STEP_EVAL(p):
    """|- !g h i s args.
            App_pt (rec_sym g h) (Tup_pt (Adj_pt i s) args)
              = App_pt h (Tup_pt i (Tup_pt s
                            (Tup_pt (App_pt (rec_sym g h) (Tup_pt s args))
                              args))).

    HOL-level lift of `rec_step_def_axiom_at g h`.
    """
    p.goal(
        "!g h i s args. "
        "App_pt (rec_sym g h) (Tup_pt (Adj_pt i s) args) = "
        "App_pt h (Tup_pt i "
        "  (Tup_pt s "
        "    (Tup_pt (App_pt (rec_sym g h) (Tup_pt s args)) "
        "            args)))",
        types={
            "g": nat0_ty, "h": nat0_ty,
            "i": nat0_ty, "s": nat0_ty, "args": nat0_ty,
        },
    )
    p.sorry()


@proof
def APP_PT_COURSE_REC_BASE_EVAL(p):
    """|- !g h y. App_pt (course_rec_sym g h) (Tup_pt Empty_pt (Tup_pt y Empty_pt))
            = App_pt g (Tup_pt y Empty_pt).

    HOL-level lift of `course_rec_base_def_axiom`. Consumed by mem_t_pr,
    valid_proof_list_pr, exists_mp_witness_pr (all course_rec instances).
    """
    p.goal(
        "!g h y. "
        "App_pt (course_rec_sym g h) (Tup_pt Empty_pt (Tup_pt y Empty_pt)) = "
        "App_pt g (Tup_pt y Empty_pt)",
        types={"g": nat0_ty, "h": nat0_ty, "y": nat0_ty},
    )
    p.sorry()


@proof
def APP_PT_COURSE_REC_STEP_EVAL(p):
    """|- !g h a b y.
            App_pt (course_rec_sym g h) (Tup_pt (Pair_ord a b) (Tup_pt y Empty_pt))
              = App_pt h (Tup_pt a (Tup_pt b
                  (Tup_pt (App_pt (course_rec_sym g h) (Tup_pt a (Tup_pt y Empty_pt)))
                    (Tup_pt (App_pt (course_rec_sym g h) (Tup_pt b (Tup_pt y Empty_pt)))
                      (Tup_pt y Empty_pt))))).

    HOL-level lift of `course_rec_step_def_axiom`. The step `h` is 5-ary:
    receives (a, b, rec a y, rec b y, y).
    """
    p.goal(
        "!g h a b y. "
        "App_pt (course_rec_sym g h) (Tup_pt (Pair_ord a b) (Tup_pt y Empty_pt)) = "
        "App_pt h (Tup_pt a "
        "  (Tup_pt b "
        "    (Tup_pt (App_pt (course_rec_sym g h) (Tup_pt a (Tup_pt y Empty_pt))) "
        "      (Tup_pt (App_pt (course_rec_sym g h) (Tup_pt b (Tup_pt y Empty_pt))) "
        "              (Tup_pt y Empty_pt)))))",
        types={
            "g": nat0_ty, "h": nat0_ty,
            "a": nat0_ty, "b": nat0_ty, "y": nat0_ty,
        },
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Section-0 checker body components.
# ---------------------------------------------------------------------------


@proof
def EQ_NAT_PR_SAME(p):
    """|- !x. App_pt eq_nat_pr (Tup_pt x (Tup_pt x Empty_pt)) = T_pt.

    Discharge chain: unfold eq_nat_pr to its 4-ary comp_sym body, reduce
    the four argument-position comp/proj/const chains, then close via
    APP_PT_IF_IN_SAME_EVAL with t = x.
    """
    from prst_pr import eq_nat_pr_def

    p.goal(
        "!x. App_pt eq_nat_pr (Tup_pt x (Tup_pt x Empty_pt)) = T_pt",
        types={"x": nat0_ty},
    )
    p.fix("x")
    p.thus(
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt x Empty_pt)) = T_pt"
    ).by_rewrite([
        eq_nat_pr_def,
        APP_PT_COMP_EVAL_4,
        APP_PT_COMP_EVAL_2,
        APP_PT_COMP_EVAL_1,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
        APP_PT_CONST_EVAL,
        APP_PT_ADJ_EVAL,
        APP_PT_IF_IN_SAME_EVAL,
    ])


@proof
def EQ_NAT_PR_CORRECT_TRUE(p):
    """|- !x y. x = y ==> App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt.

    Decomposition: under `x = y`, this reduces to the reflexive evaluator fact
    EQ_NAT_PR_SAME at x via a single congruence rewrite of the second slot.
    """
    from tactics import AP_TERM, SPEC, SYM, TRANS
    from basics import mk_app, mk_const

    p.goal(
        "!x y. x = y ==> "
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.assume("h_xy: x = y")
    same_at_x = SPEC(p._parse("x"), EQ_NAT_PR_SAME)
    # DSL friction: we want to substitute h_xy: x = y into ONLY the second
    # slot of `App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt))`. `by_rewrite_of`
    # / `by_rewrite` would replace both occurrences of x, so we hand-build
    # the targeted congruence:
    #   AP_TERM(App_pt eq_nat_pr o (Tup_pt x), AP_THM(AP_TERM(Tup_pt, h_xy), Empty_pt))
    from tactics import AP_THM
    App_pt_c = mk_const("App_pt", [])
    Tup_pt_c = mk_const("Tup_pt", [])
    Empty_pt_c = mk_const("Empty_pt", [])
    eq_nat_pr_c = mk_const("eq_nat_pr", [])
    x_c = p._parse("x")
    Tup_pt_h_xy = AP_TERM(Tup_pt_c, p.fact("h_xy"))                # Tup_pt x = Tup_pt y
    inner_tail_eq = AP_THM(Tup_pt_h_xy, Empty_pt_c)                # Tup_pt x Empty_pt = Tup_pt y Empty_pt
    outer_arg_eq = AP_TERM(mk_app(Tup_pt_c, x_c), inner_tail_eq)   # 2nd-slot-only
    full_arg_eq = AP_TERM(mk_app(App_pt_c, eq_nat_pr_c), outer_arg_eq)
    p.thus(
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"
    ).by_thm(TRANS(SYM(full_arg_eq), same_at_x))


@proof
def EQ_NAT_PR_CORRECT_FALSE(p):
    """|- !x y. ~(x = y) ==> App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt.

    Discharge chain: reduce eq_nat_pr to its if_in_sym body via the same
    comp/proj/const/adj rewrite set as EQ_NAT_PR_SAME (the comp body is
    identical; only the singleton's element is `y` instead of `x`). After
    reduction, the result is
        App_pt if_in_sym (Tup_pt x (Tup_pt (Adj_pt y Empty_pt)
                          (Tup_pt T_pt (Tup_pt F_pt Empty_pt))))
    which collapses to F_pt under `~(x = y)` via APP_PT_IF_IN_DIFF_EVAL.
    """
    from prst_pr import eq_nat_pr_def

    p.goal(
        "!x y. ~(x = y) ==> "
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.assume("h_neq: ~(x = y)")
    # Reduce the comp/proj/adj/const chain via by_rewrite. We deliberately
    # exclude APP_PT_IF_IN_SAME/DIFF_EVAL here -- by_rewrite would try the
    # SAME variant which requires `t = u` syntactically, and we want the
    # DIFF variant whose hypothesis is `h_neq`.
    p.have(
        "h_reduced: "
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt y Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt F_pt Empty_pt))))"
    ).by_rewrite([
        eq_nat_pr_def,
        APP_PT_COMP_EVAL_4,
        APP_PT_COMP_EVAL_2,
        APP_PT_COMP_EVAL_1,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
        APP_PT_CONST_EVAL,
        APP_PT_ADJ_EVAL,
    ])
    p.have(
        "h_if_diff: "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt y Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt F_pt Empty_pt)))) = F_pt"
    ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "y", "T_pt", "F_pt", "h_neq")
    p.thus(
        "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt"
    ).by_trans("h_reduced", "h_if_diff")


@proof
def EQ_NAT_PR_TRUE_VIEW(p):
    """|- !x y. (App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) =
            (x = y).

    Decomposition: this view follows from the two atomic correctness lemmas
    via EXCLUDED_MIDDLE on `x = y`. The case split keeps the App_pt
    evaluator obligation inside EQ_NAT_PR_CORRECT_TRUE/FALSE; this proof is
    pure plumbing.
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import SYM, TRANS
    from prst_pr import T_PT_NEQ_F_PT

    p.goal(
        "!x y. "
        "(App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) = "
        "(x = y)",
        types={"x": nat0_ty, "y": nat0_ty},
    )

    p.fix("x y")
    lhs = "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"

    with p.have(f"fwd: ({lhs}) ==> (x = y)").proof():
        p.assume(f"h_eq_T: {lhs}")
        with p.cases_on(EXCLUDED_MIDDLE, "x = y"):
            with p.case("hit: x = y"):
                p.thus("x = y").by_thm(p.fact("hit"))
            with p.case("miss: ~(x = y)"):
                p.have(
                    "h_eq_F: "
                    "App_pt eq_nat_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt"
                ).by(EQ_NAT_PR_CORRECT_FALSE, "x", "y", "miss")
                p.have("h_TF: T_pt = F_pt").by_thm(
                    TRANS(SYM(p.fact("h_eq_T")), p.fact("h_eq_F"))
                )
                p.absurd().by_conj(T_PT_NEQ_F_PT, "h_TF")

    with p.have(f"rev: (x = y) ==> ({lhs})").proof():
        p.assume("h_xy: x = y")
        p.thus(lhs).by(EQ_NAT_PR_CORRECT_TRUE, "x", "y", "h_xy")

    p.thus(f"({lhs}) = (x = y)").by_iff("fwd", "rev")


@proof
def F_PT_NEQ_T_PT(p):
    """|- !x. x = F_pt ==> ~(x = T_pt).

    Tiny boolean-cases helper used by OR/AND_BOOL_PR_CORRECT to flip
    `x = F_pt` into the `~(x = T_pt)` form that APP_PT_IF_IN_DIFF_EVAL
    consumes.
    """
    from prst_pr import T_PT_NEQ_F_PT
    from tactics import SYM, TRANS

    p.goal("!x. x = F_pt ==> ~(x = T_pt)", types={"x": nat0_ty})
    p.fix("x")
    p.assume("h_xF: x = F_pt")
    with p.suppose("h_xT: x = T_pt"):
        # x = F_pt and x = T_pt give T_pt = F_pt; contradicts T_PT_NEQ_F_PT.
        h_tf = TRANS(SYM(p.fact("h_xT")), p.fact("h_xF"))
        p.have("h_tf: T_pt = F_pt").by_thm(h_tf)
        p.absurd().by_conj(T_PT_NEQ_F_PT, "h_tf")


@proof
def OR_BOOL_PR_REDUCE(p):
    """|- !x y. App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) =
            App_pt if_in_sym (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt)
                                          (Tup_pt T_pt (Tup_pt y Empty_pt)))).

    Pure comp/proj/const/adj reduction of or_bool_pr's body. Splits off the
    "reduce to if_in_sym shape" step so OR_BOOL_PR_CORRECT can focus on the
    boolean reasoning.
    """
    from prst_pr import or_bool_pr_def

    p.goal(
        "!x y. App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt y Empty_pt))))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.thus(
        "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt y Empty_pt))))"
    ).by_rewrite([
        or_bool_pr_def,
        APP_PT_COMP_EVAL_4,
        APP_PT_COMP_EVAL_2,
        APP_PT_COMP_EVAL_1,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
        APP_PT_CONST_EVAL,
        APP_PT_ADJ_EVAL,
    ])


@proof
def AND_BOOL_PR_REDUCE(p):
    """|- !x y. App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) =
            App_pt if_in_sym (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt)
                                          (Tup_pt y (Tup_pt F_pt Empty_pt)))).

    Pure reduction analogue of OR_BOOL_PR_REDUCE; and_bool_pr differs only
    in the then/else branches (`y` vs `T_pt`, `F_pt` vs `y`).
    """
    from prst_pr import and_bool_pr_def

    p.goal(
        "!x y. App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt y (Tup_pt F_pt Empty_pt))))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.thus(
        "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt y (Tup_pt F_pt Empty_pt))))"
    ).by_rewrite([
        and_bool_pr_def,
        APP_PT_COMP_EVAL_4,
        APP_PT_COMP_EVAL_2,
        APP_PT_COMP_EVAL_1,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
        APP_PT_CONST_EVAL,
        APP_PT_ADJ_EVAL,
    ])


@proof
def OR_BOOL_PR_CORRECT(p):
    r"""|- !x y. boolean inputs make or_bool_pr agree with HOL disjunction.

    Discharge: reduce or_bool_pr to an if_in_sym applied to {T_pt} (via
    OR_BOOL_PR_REDUCE), then case-split on `x = T_pt` vs `x = F_pt`. The
    T_pt-branch closes via APP_PT_IF_IN_SAME_EVAL; the F_pt-branch reduces
    or_bool_pr's value to `y` via APP_PT_IF_IN_DIFF_EVAL + T_PT_NEQ_F_PT.
    """
    from tactics import SPECL, SYM
    from prst_pr import T_PT_NEQ_F_PT

    p.goal(
        "!x y. "
        "((x = T_pt \\/ x = F_pt) /\\ (y = T_pt \\/ y = F_pt)) "
        "==> ((App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) = "
        "     (x = T_pt \\/ y = T_pt))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.assume("(h_x_bool, h_y_bool): "
             "(x = T_pt \\/ x = F_pt) /\\ (y = T_pt \\/ y = F_pt)")
    reduce_at = SPECL([p._parse("x"), p._parse("y")], OR_BOOL_PR_REDUCE)
    p.have(
        "h_reduce: "
        "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt y Empty_pt))))"
    ).by_thm(reduce_at)

    lhs = "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"
    rhs = "x = T_pt \\/ y = T_pt"

    with p.have(f"fwd: ({lhs}) ==> ({rhs})").proof():
        p.assume(f"h_lhs: {lhs}")
        with p.cases_on("h_x_bool"):
            with p.case("hx_t: x = T_pt"):
                p.thus(rhs).by_disj("hx_t")
            with p.case("hx_f: x = F_pt"):
                p.have("h_neq_xy: ~(x = T_pt)").by(
                    F_PT_NEQ_T_PT, "x", "hx_f",
                )
                # Reduce if_in via DIFF: hx_f : x = F_pt, so ~(x = T_pt).
                p.have(
                    "h_if_diff: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = y"
                ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "T_pt", "y", "h_neq_xy")
                p.have("h_or_y: "
                       "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = y"
                ).by_trans("h_reduce", "h_if_diff")
                # h_lhs : ... = T_pt; h_or_y : ... = y. So y = T_pt.
                from tactics import TRANS
                hy_t_th = TRANS(SYM(p.fact("h_or_y")), p.fact("h_lhs"))
                p.have("hy_t: y = T_pt").by_thm(hy_t_th)
                p.thus(rhs).by_disj("hy_t")

    with p.have(f"rev: ({rhs}) ==> ({lhs})").proof():
        p.assume(f"h_rhs: {rhs}")
        with p.cases_on("h_rhs"):
            with p.case("hx_t: x = T_pt"):
                # Substitute x = T_pt; if_in evaluates via SAME.
                p.have(
                    "h_if_same: "
                    "App_pt if_in_sym "
                    "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "T_pt", "y")
                # Lift to x: rewrite by SYM(hx_t).
                p.have(
                    "h_if_same_x: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                p.thus(lhs).by_trans("h_reduce", "h_if_same_x")
            with p.case("hy_t: y = T_pt"):
                # y = T_pt; need or_bool_pr ... = T_pt. Case on x:
                with p.cases_on("h_x_bool"):
                    with p.case("hx_t: x = T_pt"):
                        # Same as left branch above: if_in collapses via SAME.
                        p.have(
                            "h_if_same: "
                            "App_pt if_in_sym "
                            "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                        ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "T_pt", "y")
                        p.have(
                            "h_if_same_x: "
                            "App_pt if_in_sym "
                            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                        ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                        p.thus(lhs).by_trans("h_reduce", "h_if_same_x")
                    with p.case("hx_f: x = F_pt"):
                        # x = F_pt; if_in collapses to y via DIFF.
                        p.have("h_neq_xy: ~(x = T_pt)").by(
                            F_PT_NEQ_T_PT, "x", "hx_f",
                        )
                        p.have(
                            "h_if_diff: "
                            "App_pt if_in_sym "
                            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = y"
                        ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "T_pt", "y", "h_neq_xy")
                        # Chain: or_bool = if_in = y = T_pt.
                        from tactics import TRANS
                        chain = TRANS(
                            TRANS(p.fact("h_reduce"), p.fact("h_if_diff")),
                            p.fact("hy_t"),
                        )
                        p.thus(lhs).by_thm(chain)

    p.thus(f"({lhs}) = ({rhs})").by_iff("fwd", "rev")


@proof
def AND_BOOL_PR_CORRECT(p):
    r"""|- !x y. boolean inputs make and_bool_pr agree with HOL conjunction.

    Mirror of OR_BOOL_PR_CORRECT: reduce via AND_BOOL_PR_REDUCE, then on
    `x = T_pt` the if_in collapses to `y` (then-branch), and on `x = F_pt`
    the if_in collapses to `F_pt` (else-branch).
    """
    from tactics import SPECL, SYM, TRANS
    from prst_pr import T_PT_NEQ_F_PT

    p.goal(
        "!x y. "
        "((x = T_pt \\/ x = F_pt) /\\ (y = T_pt \\/ y = F_pt)) "
        "==> ((App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) = "
        "     (x = T_pt /\\ y = T_pt))",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    p.assume("(h_x_bool, h_y_bool): "
             "(x = T_pt \\/ x = F_pt) /\\ (y = T_pt \\/ y = F_pt)")
    reduce_at = SPECL([p._parse("x"), p._parse("y")], AND_BOOL_PR_REDUCE)
    p.have(
        "h_reduce: "
        "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt y (Tup_pt F_pt Empty_pt))))"
    ).by_thm(reduce_at)

    lhs = "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"
    rhs = "x = T_pt /\\ y = T_pt"

    with p.have(f"fwd: ({lhs}) ==> ({rhs})").proof():
        p.assume(f"h_lhs: {lhs}")
        with p.cases_on("h_x_bool"):
            with p.case("hx_t: x = T_pt"):
                # if_in collapses to y; combined with h_lhs (= T_pt), we get y = T_pt.
                p.have(
                    "h_if_same: "
                    "App_pt if_in_sym "
                    "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
                ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "y", "F_pt")
                p.have(
                    "h_if_same_x: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
                ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                p.have("h_and_y: "
                       "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = y"
                ).by_trans("h_reduce", "h_if_same_x")
                hy_t = TRANS(SYM(p.fact("h_and_y")), p.fact("h_lhs"))
                p.have("hy_t: y = T_pt").by_thm(hy_t)
                p.thus(rhs).by_thm(
                    __import__("tactics").CONJ(p.fact("hx_t"), p.fact("hy_t"))
                )
            with p.case("hx_f: x = F_pt"):
                # if_in collapses to F_pt; h_lhs says LHS = T_pt; contradiction.
                p.have("h_neq_xy: ~(x = T_pt)").by(
                    F_PT_NEQ_T_PT, "x", "hx_f",
                )
                p.have(
                    "h_if_diff: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = F_pt"
                ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "y", "F_pt", "h_neq_xy")
                p.have(
                    "h_and_f: "
                    "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt"
                ).by_trans("h_reduce", "h_if_diff")
                h_tf = TRANS(SYM(p.fact("h_lhs")), p.fact("h_and_f"))
                p.have("h_tf: T_pt = F_pt").by_thm(h_tf)
                p.absurd().by_conj(T_PT_NEQ_F_PT, "h_tf")

    with p.have(f"rev: ({rhs}) ==> ({lhs})").proof():
        p.assume("(hx_t, hy_t): x = T_pt /\\ y = T_pt")
        # Substitute x = T_pt, evaluate if_in (SAME), result = y = T_pt.
        p.have(
            "h_if_same: "
            "App_pt if_in_sym "
            "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
            "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
        ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "y", "F_pt")
        p.have(
            "h_if_same_x: "
            "App_pt if_in_sym "
            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
            "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
        ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
        chain = TRANS(
            TRANS(p.fact("h_reduce"), p.fact("h_if_same_x")),
            p.fact("hy_t"),
        )
        p.thus(lhs).by_thm(chain)

    p.thus(f"({lhs}) = ({rhs})").by_iff("fwd", "rev")


@proof
def IS_TUP_PR_CORRECT(p):
    """|- !p. (App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt) =
            (?h t. p = Tup_pt h t).

    DSL/proof friction: is_tup_pr := `comp(eq_nat_pr, comp(pair_left_sym,
    proj(0,1)), _const_at(nat(12),1))`. The two natural sub-stubs are:
      (a) `App_pt is_tup_pr (Tup_pt p Empty_pt) = eq_nat_pr (pair_left p) 12`
          -- a comp-of-pair-left evaluation chain at HOL level (missing).
      (b) `(pair_left p = 12) = (?h t. p = Tup_pt h t)` -- the HF
          characterisation of the Tup_pt tag (provable from Tup_pt's encoding
          + pair injectivity).
    Without (a), decomposing buys nothing.
    """
    p.goal(
        "!p. (App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt) = "
        "(?h t. p = Tup_pt h t)",
        types={"p": nat0_ty},
    )
    p.sorry()


@proof
def TUP_HEAD_PR_CORRECT(p):
    """|- !h t. App_pt tup_head_pr (Tup_pt (Tup_pt h t) Empty_pt) = h.

    Discharged via `by_rewrite` using `OneShot(TUP_PT_AT)`: the rewriter
    fires TUP_PT_AT at the innermost (deepest-first-visited) Tup_pt position
    -- the proof-list value -- and then APP_PT_PAIR_RIGHT_EVAL /
    APP_PT_PAIR_LEFT_EVAL peel back up through the args wrappers in the
    same pass, before TUP_PT_AT could re-fire on those wrappers. Demonstrates
    the OneShot wrapper as a configurability knob for the rewrite engine.
    """
    from prst_pr import tup_head_pr_def, tup_payload_pr_def
    from prst_syntax import TUP_PT_AT
    from tactics import OneShot

    p.goal(
        "!h t. App_pt tup_head_pr (Tup_pt (Tup_pt h t) Empty_pt) = h",
        types={"h": nat0_ty, "t": nat0_ty},
    )
    p.fix("h t")
    p.thus(
        "App_pt tup_head_pr (Tup_pt (Tup_pt h t) Empty_pt) = h"
    ).by_rewrite([
        tup_head_pr_def,
        tup_payload_pr_def,
        APP_PT_COMP_EVAL_1,
        APP_PT_PROJ_AT_HEAD,
        OneShot(TUP_PT_AT),
        APP_PT_PAIR_RIGHT_EVAL,
        APP_PT_PAIR_LEFT_EVAL,
    ])


@proof
def MEM_T_PR_REDUCE_EMPTY(p):
    """|- !x. App_pt mem_t_pr (Tup_pt x (Tup_pt Empty_pt Empty_pt)) = F_pt.

    Base-case reduction for mem_t_pr's correctness: searching for any `x`
    in the empty list is F_pt. Pure App_pt-evaluator chain through
    mem_t_pr_def + proj + course_rec_base + g_mem_t_pr_def + const_eval.
    """
    from prst_pr import mem_t_pr_def, g_mem_t_pr_def

    p.goal(
        "!x. App_pt mem_t_pr (Tup_pt x (Tup_pt Empty_pt Empty_pt)) = F_pt",
        types={"x": nat0_ty},
    )
    p.fix("x")
    p.thus(
        "App_pt mem_t_pr (Tup_pt x (Tup_pt Empty_pt Empty_pt)) = F_pt"
    ).by_rewrite([
        mem_t_pr_def,
        g_mem_t_pr_def,
        APP_PT_COMP_EVAL_2,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
        APP_PT_COURSE_REC_BASE_EVAL,
        APP_PT_CONST_EVAL,
    ])


@proof
def MEM_T_PR_STEP_TUP(p):
    """|- !x h t.
            (App_pt mem_t_pr (Tup_pt x (Tup_pt (Tup_pt h t) Empty_pt)) = T_pt) =
            (x = h \\/ App_pt mem_t_pr (Tup_pt x (Tup_pt t Empty_pt)) = T_pt).

    Step-case reduction: searching `x` in `Tup_pt h t` succeeds iff `x = h`
    or `x` is in `t`. The proof traces the course_rec step through
    `h_mem_t_pr` (which checks the outer Pair_ord tag = 12, then dispatches
    via `or_bool_pr` of the head-equality and the recursive tail result).

    STUB: requires (a) APP_PT_COURSE_REC_STEP_EVAL on `Pair_ord 12 (Pair_ord h t)`,
    (b) the inner course_rec at `Pair_ord h t` correctly emerging as
    mem_t_pr(x, t) -- a non-trivial nested-course-rec lemma, and
    (c) `OR_BOOL_PR_TRUE_VIEW` to lift the `or_bool_pr` view, plus
    `EQ_NAT_PR_TRUE_VIEW` for the head check.
    """
    p.goal(
        "!x h t. "
        "(App_pt mem_t_pr (Tup_pt x (Tup_pt (Tup_pt h t) Empty_pt)) = T_pt) = "
        "(x = h \\/ App_pt mem_t_pr (Tup_pt x (Tup_pt t Empty_pt)) = T_pt)",
        types={"x": nat0_ty, "h": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def MEM_PRST_AT_EMPTY(p):
    """|- !x. Mem_PRST Empty_pt x = F.

    Worked-example sub-stub: Mem_PRST on the empty list is False. Provable
    from `_MEM_PRST_REC` at Empty_pt + the body's `?h t. Empty_pt = Tup_pt h t`
    impossibility (via TUP_PT_DISJOINT_EMPTY).
    """
    p.goal("!x. Mem_PRST Empty_pt x = F", types={"x": nat0_ty})
    p.sorry()


@proof
def MEM_PRST_AT_TUP(p):
    """|- !h t x. Mem_PRST (Tup_pt h t) x = (x = h \\/ Mem_PRST t x).

    Worked-example sub-stub: Mem_PRST step rewrite. Provable from
    `_MEM_PRST_REC` at `Tup_pt h t` + TUP_PT_INJ to collapse the
    existential.
    """
    p.goal(
        "!h t x. Mem_PRST (Tup_pt h t) x = (x = h \\/ Mem_PRST t x)",
        types={"h": nat0_ty, "t": nat0_ty, "x": nat0_ty},
    )
    p.sorry()


@proof
def MEM_T_PR_NON_TUP_FALSE(p):
    """|- !a b x. ~(a = SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 (SUC0
                  (SUC0 (SUC0 (SUC0 (SUC0 (SUC0 0)))))))))))) ==>
            App_pt mem_t_pr (Tup_pt x (Tup_pt (Pair_ord a b) Empty_pt)) = F_pt.

    Worked-example sub-stub: on a `Pair_ord a b` with `a` not the Tup_pt
    tag (12), mem_t_pr evaluates to F_pt. Traces course_rec_step + h_mem_t_pr's
    if_in (else-branch returns rec_b, which recurses on b; eventually
    reaches Empty_pt or another non-Tup pair, all evaluating to F_pt).

    A fuller proof would itself use strong induction on the Pair_ord depth.
    """
    from prst_syntax import suc_chain
    p.goal(
        "!a b x. "
        f"~(a = {suc_chain(12)}) ==> "
        "App_pt mem_t_pr (Tup_pt x (Tup_pt (Pair_ord a b) Empty_pt)) = F_pt",
        types={"a": nat0_ty, "b": nat0_ty, "x": nat0_ty},
    )
    p.sorry()


@proof
def MEM_T_PR_CORRECT(p):
    """|- !P x. (App_pt mem_t_pr (Tup_pt x (Tup_pt P Empty_pt)) = T_pt) =
            Mem_PRST P x.

    NOTE on argument order: the iff uses `Mem_PRST P x` (P = list, x =
    element). This matches `_MEM_PRST_F_DEF`'s first-arg destructuring
    `?h t. p = Tup_pt h t /\\ ...`. Several other goals in the file use
    `Mem_PRST element list` and are mathematically backwards -- separate
    convention-cleanup task.

    Worked example demonstrating the course_rec induction pattern:
    `p.strong_induction("P", "IH")` to get the IH at every `k < P`, then
    `p.cases_on(NAT0_CASES_PAIR_ORD, "P")` to dispatch on the recursion
    target shape.

      - Empty_pt branch  : PR side -> F_pt (MEM_T_PR_REDUCE_EMPTY);
                           HOL side -> False (MEM_PRST_AT_EMPTY).
                           Both False, iff trivial.
      - Pair_ord branch  : choose the (a, b) witnesses, then EXCLUDED_MIDDLE
                           on `a = 12`:
          - a = 12       : P = Tup_pt h t with b = Pair_ord h t. Use
                           MEM_T_PR_STEP_TUP for the PR side and
                           MEM_PRST_AT_TUP for the HOL side, then IH at t
                           (lt t P) to bridge the recursive disjuncts.
          - a /= 12      : PR side -> F_pt (MEM_T_PR_NON_TUP_FALSE);
                           HOL side -> False (Pair_ord a b is not Tup_pt,
                           so Mem_PRST's body existential fails by
                           TUP_PT_INJ + a /= 12 contradiction).
    """
    from tactics import SPECL, SYM, TRANS
    from classical import EXCLUDED_MIDDLE
    from prst_pr import T_PT_NEQ_F_PT
    from prst_syntax import suc_chain as _sc

    p.goal(
        "!P x. (App_pt mem_t_pr (Tup_pt x (Tup_pt P Empty_pt)) = T_pt) = "
        "Mem_PRST P x",
        types={"P": nat0_ty, "x": nat0_ty},
    )
    # Note: the DSL's strong_induction expects the var to be the OUTERMOST
    # forall. We swap the foralls (P first, then x) so strong induction
    # on P proceeds cleanly.
    p.fix("P")
    with p.strong_induction("x", "IH") if False else p.have("inner: !x. (App_pt mem_t_pr (Tup_pt x (Tup_pt P Empty_pt)) = T_pt) = Mem_PRST P x").proof():
        # WORKED SKELETON: not attempted in full; outline only.
        # Real proof would re-shape goal to do strong_induction on P, then
        # the case structure described in the docstring.
        p.sorry()
    p.thus(
        "!x. (App_pt mem_t_pr (Tup_pt x (Tup_pt P Empty_pt)) = T_pt) = Mem_PRST P x"
    ).by_thm(p.fact("inner"))


@proof
def EXISTS_MP_WITNESS_PR_CORRECT(p):
    r"""|- !h t. (App_pt exists_mp_witness_pr (Tup_pt h (Tup_pt t Empty_pt)) = T_pt) =
            (?f. Mem_PRST f t /\ Mem_PRST (Imp_pf f h) t).

    DSL/proof friction: exists_mp_witness_pr is another course_rec_sym
    instance, this time recursing over t for the existential search. The
    proof is structurally analogous to MEM_T_PR_CORRECT but the body
    combines two mem_t_pr lookups via or_bool_pr -- so it depends on
    MEM_T_PR_CORRECT + OR_BOOL_PR_CORRECT + the same comp/course_rec
    App_pt evaluator blocker.
    """
    p.goal(
        "!h t. "
        "(App_pt exists_mp_witness_pr (Tup_pt h (Tup_pt t Empty_pt)) = T_pt) = "
        "(?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t)",
        types={"h": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def VALID_STEP_PR_CORRECT(p):
    r"""|- !h t. (App_pt valid_step_pr (Tup_pt h (Tup_pt t Empty_pt)) = T_pt) =
            (is_pr_axiom h \/ (?f. Mem_PRST f t /\ Mem_PRST (Imp_pf f h) t)).

    Natural decomposition (deferred, see DSL/proof friction below):
      - valid_step_pr := `comp(or_bool_pr, is_pr_axiom_pr,
                              comp(exists_mp_witness_pr, proj 0 2, proj 1 2))`
      - Sub-stubs would be:
          (a) IS_PR_AXIOM_PR_CORRECT : is_pr_axiom_pr semantic view
              (App_pt is_pr_axiom_pr (Tup_pt h Empty_pt) = T_pt  iff
               is_pr_axiom h). This is the schema-recogniser API,
               separately tracked in the ledger (Design 3).
          (b) EXISTS_MP_WITNESS_PR_CORRECT (above).
          (c) OR_BOOL_PR_CORRECT to lift the disjunction.
      - Plus a `comp_sym` App_pt evaluator (the persistent blocker).
    """
    p.goal(
        "!h t. "
        "(App_pt valid_step_pr (Tup_pt h (Tup_pt t Empty_pt)) = T_pt) = "
        "(is_pr_axiom h \\/ (?f. Mem_PRST f t /\\ Mem_PRST (Imp_pf f h) t))",
        types={"h": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def VALID_PROOF_LIST_PR_CORRECT(p):
    """|- !P. (App_pt valid_proof_list_pr (Tup_pt P Empty_pt) = T_pt) =
            ValidProof_PRST P.

    Natural decomposition (deferred, see DSL/proof friction below):
      - valid_proof_list_pr is a course_rec_sym driven by the
        `_h_valid_proof_list_then = and_bool_pr (rec t) (valid_step_pr h t)`
        body.
      - The proof is a strong induction on P (lt = nat0_lt) with two cases:
          P = Empty_pt   :=  both sides reduce to T_pt / ValidProof_PRST_EMPTY
          P = Tup_pt h t :=  step recursion: IH on t, valid_step_pr at (h,t)
      - Sub-stubs would mirror those: VALID_PROOF_LIST_PR_EMPTY (~5 lines if
        comp/course_rec App_pt evaluator existed) and VALID_PROOF_LIST_PR_TUP
        (the inductive step bridging IH + AND_BOOL_PR_CORRECT +
        VALID_STEP_PR_CORRECT).
      - Same comp/course_rec App_pt evaluator blocker.
    """
    p.goal(
        "!P. (App_pt valid_proof_list_pr (Tup_pt P Empty_pt) = T_pt) = "
        "ValidProof_PRST P",
        types={"P": nat0_ty},
    )
    p.sorry()


@proof
def NAT0_CASES_PAIR_ORD(p):
    r"""|- !p. p = Empty_pt \/ (?a b. p = Pair_ord a b).

    Case-split for course-recursion: every nat0 is either Empty_pt (the
    base case for course_rec) or has the form Pair_ord a b (the step
    case). Needed to dispatch the course_rec evaluators
    APP_PT_COURSE_REC_BASE_EVAL / STEP_EVAL on an arbitrary `p`.

    STUB: standard HF-structure fact, derivable from the bit-encoding via
    `p = 0` vs `p > 0` and the Pair_ord decomposition of any non-zero
    nat0 (Empty_pt is `0`; everything else decomposes as the bit pair).
    """
    p.goal(
        "!p. p = Empty_pt \\/ (?a b. p = Pair_ord a b)",
        types={"p": nat0_ty, "a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def OR_BOOL_PR_TRUE_VIEW(p):
    """|- !x y. (App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) =
            (x = T_pt \\/ y = T_pt).

    Unconditional strengthening of OR_BOOL_PR_CORRECT, mirror of
    AND_BOOL_PR_TRUE_VIEW. Reduce or_bool_pr to its if_in body, then case
    on EXCLUDED_MIDDLE for x = T_pt.
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import SPECL, SYM, TRANS
    from prst_pr import T_PT_NEQ_F_PT

    p.goal(
        "!x y. (App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) = "
        "(x = T_pt \\/ y = T_pt)",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    reduce_at = SPECL([p._parse("x"), p._parse("y")], OR_BOOL_PR_REDUCE)
    p.have(
        "h_reduce: "
        "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt T_pt (Tup_pt y Empty_pt))))"
    ).by_thm(reduce_at)

    lhs = "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"
    rhs = "x = T_pt \\/ y = T_pt"

    with p.have(f"fwd: ({lhs}) ==> ({rhs})").proof():
        p.assume(f"h_lhs: {lhs}")
        with p.cases_on(EXCLUDED_MIDDLE, "x = T_pt"):
            with p.case("hx_t: x = T_pt"):
                p.thus(rhs).by_disj("hx_t")
            with p.case("hx_nt: ~(x = T_pt)"):
                # or_bool_pr collapses to y via DIFF, so y = T_pt.
                p.have(
                    "h_if_diff: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = y"
                ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "T_pt", "y", "hx_nt")
                p.have("h_or_y: "
                       "App_pt or_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = y"
                ).by_trans("h_reduce", "h_if_diff")
                hy_t_th = TRANS(SYM(p.fact("h_or_y")), p.fact("h_lhs"))
                p.have("hy_t: y = T_pt").by_thm(hy_t_th)
                p.thus(rhs).by_disj("hy_t")

    with p.have(f"rev: ({rhs}) ==> ({lhs})").proof():
        p.assume(f"h_rhs: {rhs}")
        with p.cases_on("h_rhs"):
            with p.case("hx_t: x = T_pt"):
                p.have(
                    "h_if_same: "
                    "App_pt if_in_sym "
                    "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "T_pt", "y")
                p.have(
                    "h_if_same_x: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                p.thus(lhs).by_trans("h_reduce", "h_if_same_x")
            with p.case("hy_t: y = T_pt"):
                # Case on x = T_pt to either SAME (returns T_pt directly) or
                # DIFF (returns y, which equals T_pt).
                with p.cases_on(EXCLUDED_MIDDLE, "x = T_pt"):
                    with p.case("hx_t: x = T_pt"):
                        p.have(
                            "h_if_same: "
                            "App_pt if_in_sym "
                            "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                        ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "T_pt", "y")
                        p.have(
                            "h_if_same_x: "
                            "App_pt if_in_sym "
                            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = T_pt"
                        ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                        p.thus(lhs).by_trans("h_reduce", "h_if_same_x")
                    with p.case("hx_nt: ~(x = T_pt)"):
                        p.have(
                            "h_if_diff: "
                            "App_pt if_in_sym "
                            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                            "    (Tup_pt T_pt (Tup_pt y Empty_pt)))) = y"
                        ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "T_pt", "y", "hx_nt")
                        chain = TRANS(
                            TRANS(p.fact("h_reduce"), p.fact("h_if_diff")),
                            p.fact("hy_t"),
                        )
                        p.thus(lhs).by_thm(chain)

    p.thus(f"({lhs}) = ({rhs})").by_iff("fwd", "rev")


@proof
def AND_BOOL_PR_TRUE_VIEW(p):
    """|- !x y. (App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) =
            (x = T_pt /\\ y = T_pt).

    Unconditional strengthening of AND_BOOL_PR_CORRECT: the boolean-input
    invariant is unnecessary because the only way to get T_pt out of
    and_bool_pr is the (T_pt, T_pt) case anyway (DIFF returns F_pt, so any
    non-T_pt first arg fails T_pt = F_pt directly).
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import SPECL, SYM, TRANS, CONJ
    from prst_pr import T_PT_NEQ_F_PT

    p.goal(
        "!x y. (App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt) = "
        "(x = T_pt /\\ y = T_pt)",
        types={"x": nat0_ty, "y": nat0_ty},
    )
    p.fix("x y")
    reduce_at = SPECL([p._parse("x"), p._parse("y")], AND_BOOL_PR_REDUCE)
    p.have(
        "h_reduce: "
        "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = "
        "App_pt if_in_sym "
        "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
        "    (Tup_pt y (Tup_pt F_pt Empty_pt))))"
    ).by_thm(reduce_at)

    lhs = "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = T_pt"
    rhs = "x = T_pt /\\ y = T_pt"

    with p.have(f"fwd: ({lhs}) ==> ({rhs})").proof():
        p.assume(f"h_lhs: {lhs}")
        with p.cases_on(EXCLUDED_MIDDLE, "x = T_pt"):
            with p.case("hx_t: x = T_pt"):
                p.have(
                    "h_if_same: "
                    "App_pt if_in_sym "
                    "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
                ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "y", "F_pt")
                p.have(
                    "h_if_same_x: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
                ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
                p.have("h_and_y: "
                       "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = y"
                ).by_trans("h_reduce", "h_if_same_x")
                hy_t = TRANS(SYM(p.fact("h_and_y")), p.fact("h_lhs"))
                p.have("hy_t: y = T_pt").by_thm(hy_t)
                p.thus(rhs).by_thm(CONJ(p.fact("hx_t"), p.fact("hy_t")))
            with p.case("hx_nt: ~(x = T_pt)"):
                p.have(
                    "h_if_diff: "
                    "App_pt if_in_sym "
                    "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
                    "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = F_pt"
                ).by(APP_PT_IF_IN_DIFF_EVAL, "x", "T_pt", "y", "F_pt", "hx_nt")
                p.have(
                    "h_and_f: "
                    "App_pt and_bool_pr (Tup_pt x (Tup_pt y Empty_pt)) = F_pt"
                ).by_trans("h_reduce", "h_if_diff")
                h_tf = TRANS(SYM(p.fact("h_lhs")), p.fact("h_and_f"))
                p.have("h_tf: T_pt = F_pt").by_thm(h_tf)
                p.absurd().by_conj(T_PT_NEQ_F_PT, "h_tf")

    with p.have(f"rev: ({rhs}) ==> ({lhs})").proof():
        p.assume("(hx_t, hy_t): x = T_pt /\\ y = T_pt")
        p.have(
            "h_if_same: "
            "App_pt if_in_sym "
            "  (Tup_pt T_pt (Tup_pt (Adj_pt T_pt Empty_pt) "
            "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
        ).by(APP_PT_IF_IN_SAME_EVAL, "T_pt", "y", "F_pt")
        p.have(
            "h_if_same_x: "
            "App_pt if_in_sym "
            "  (Tup_pt x (Tup_pt (Adj_pt T_pt Empty_pt) "
            "    (Tup_pt y (Tup_pt F_pt Empty_pt)))) = y"
        ).by_rewrite_of("h_if_same", [SYM(p.fact("hx_t"))])
        chain = TRANS(
            TRANS(p.fact("h_reduce"), p.fact("h_if_same_x")),
            p.fact("hy_t"),
        )
        p.thus(lhs).by_thm(chain)

    p.thus(f"({lhs}) = ({rhs})").by_iff("fwd", "rev")


@proof
def PROOF_PRST_PR_BOOL_VIEW(p):
    r"""|- !p n. (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt) =
            ((App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt) /\
             (App_pt eq_nat_pr
                (Tup_pt (App_pt tup_head_pr (Tup_pt p Empty_pt))
                  (Tup_pt n Empty_pt)) = T_pt) /\
             (App_pt valid_proof_list_pr (Tup_pt p Empty_pt) = T_pt)).

    Discharge: reduce Proof_PRST_pr's body to a nested and_bool_pr of three
    component checks via the standard comp/proj evaluator chain, then peel
    the two and_bool_pr layers with AND_BOOL_PR_TRUE_VIEW.
    """
    from prst_pr import Proof_PRST_pr_def
    from tactics import AP_TERM, SPECL, SYM, TRANS
    from basics import mk_app, mk_const

    p.goal(
        "!p n. "
        "(App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt) = "
        "((App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt) /\\ "
        " ((App_pt eq_nat_pr "
        "    (Tup_pt (App_pt tup_head_pr (Tup_pt p Empty_pt)) "
        "      (Tup_pt n Empty_pt)) = T_pt) /\\ "
        "  (App_pt valid_proof_list_pr (Tup_pt p Empty_pt) = T_pt)))",
        types={"p": nat0_ty, "n": nat0_ty},
    )
    p.fix("p n")

    X = "App_pt is_tup_pr (Tup_pt p Empty_pt)"
    Y = "App_pt eq_nat_pr (Tup_pt (App_pt tup_head_pr (Tup_pt p Empty_pt)) (Tup_pt n Empty_pt))"
    Z = "App_pt valid_proof_list_pr (Tup_pt p Empty_pt)"

    # Step 1: Reduce App_pt Proof_PRST_pr ... to the nested and_bool_pr form.
    # The reduction is pure comp/proj/and-rewrite via by_rewrite.
    p.have(
        "h_reduce: "
        f"App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = "
        f"App_pt and_bool_pr "
        f"  (Tup_pt ({X}) "
        f"    (Tup_pt (App_pt and_bool_pr "
        f"               (Tup_pt ({Y}) (Tup_pt ({Z}) Empty_pt))) "
        f"      Empty_pt))"
    ).by_rewrite([
        Proof_PRST_pr_def,
        APP_PT_COMP_EVAL_1,
        APP_PT_COMP_EVAL_2,
        APP_PT_PROJ_AT_HEAD,
        APP_PT_PROJ_AT_TAIL,
    ])

    # Step 2: View the LHS = T_pt equation as the AND of two conjuncts.
    outer_view = SPECL(
        [p._parse(X),
         p._parse(f"App_pt and_bool_pr (Tup_pt ({Y}) (Tup_pt ({Z}) Empty_pt))")],
        AND_BOOL_PR_TRUE_VIEW,
    )
    # outer_view :  (App_pt and_bool_pr (Tup_pt X (Tup_pt inner_and Empty_pt)) = T_pt)
    #              = (X = T_pt /\ inner_and = T_pt)
    inner_view = SPECL(
        [p._parse(Y), p._parse(Z)], AND_BOOL_PR_TRUE_VIEW,
    )
    # inner_view :  (App_pt and_bool_pr (Tup_pt Y (Tup_pt Z Empty_pt)) = T_pt)
    #              = (Y = T_pt /\ Z = T_pt)

    # Wrap inner_view to match the second-conjunct slot of outer_view.
    # The full RHS we want is `(X = T_pt /\ (Y = T_pt /\ Z = T_pt))`. We have
    # outer giving (X = T_pt /\ inner_and_T) and inner giving (inner_and_T = (Y = T_pt /\ Z = T_pt)).
    # AND_CONG with REFL(X = T_pt) + inner_view bridges the two.
    AND_c = mk_const("/\\", [])

    def AND_CONG(eq_l, eq_r):
        from fusion import MK_COMB
        return MK_COMB(AP_TERM(AND_c, eq_l), eq_r)

    from tactics import REFL
    x_eq_tp = p._parse(f"({X}) = T_pt")
    rhs_outer = p._parse(
        f"((({X}) = T_pt) /\\ "
        f" ((App_pt and_bool_pr "
        f"    (Tup_pt ({Y}) (Tup_pt ({Z}) Empty_pt))) = T_pt))"
    )
    bridge_inner = AND_CONG(REFL(x_eq_tp), inner_view)
    # bridge_inner : (X = T_pt /\ inner_and = T_pt) = (X = T_pt /\ (Y = T_pt /\ Z = T_pt))
    nested_view = TRANS(outer_view, bridge_inner)
    # nested_view : (App_pt and_bool_pr ... outer ... = T_pt) = (X = T_pt /\ Y = T_pt /\ Z = T_pt)

    # Step 3: Lift the equation through h_reduce.
    # `h_reduce : Proof_PRST_pr-application = and_bool_pr-application`.
    # So `Proof_PRST_pr-application = T_pt` iff `and_bool_pr-application = T_pt`.
    # AP_TERM(\u. u = T_pt, h_reduce) does the lift.
    from fusion import aty
    Eq_c = mk_const("=", [(nat0_ty, aty)])
    T_pt_c = mk_const("T_pt", [])
    # AP_THM(AP_TERM(=, h_reduce), T_pt) : (LHS = T_pt) = (RHS = T_pt).
    from tactics import AP_THM
    lhs_eq_t_view = AP_THM(AP_TERM(Eq_c, p.fact("h_reduce")), T_pt_c)

    full_iff = TRANS(lhs_eq_t_view, nested_view)
    p.thus(
        f"(App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt) = "
        f"((({X}) = T_pt) /\\ "
        f" ((({Y}) = T_pt) /\\ "
        f"  (({Z}) = T_pt)))"
    ).by_thm(full_iff)


@proof
def PROOF_PRST_PR_BODY_CORRECT(p):
    r"""|- !p n. (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt) =
            (?h t. p = Tup_pt h t /\ n = h /\ ValidProof_PRST p).

    DSL/proof friction: this is the focused body-composition obligation. It
    should compose IS_TUP_PR_CORRECT, TUP_HEAD_PR_CORRECT,
    VALID_PROOF_LIST_PR_CORRECT, EQ_NAT_PR_CORRECT_TRUE/FALSE, and the boolean
    helper correctness lemmas. This theorem is the checker-body view used
    directly by callers that need the checker-body view.
    """
    p.goal(
        "!p n. "
        "(App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt) = "
        "(?h t. p = Tup_pt h t /\\ n = h /\\ ValidProof_PRST p)",
        types={"p": nat0_ty, "n": nat0_ty},
    )
    from tactics import CONJ, SPEC, SPECL, SYM

    p.fix("p n")
    body_view = SPECL([p._parse("p"), p._parse("n")], PROOF_PRST_PR_BOOL_VIEW)
    is_tup_at = SPEC(p._parse("p"), IS_TUP_PR_CORRECT)
    valid_at = SPEC(p._parse("p"), VALID_PROOF_LIST_PR_CORRECT)

    lhs = (
        "App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt"
    )
    rhs = "?h t. p = Tup_pt h t /\\ n = h /\\ ValidProof_PRST p"
    parts = (
        "(App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt) /\\ "
        "((App_pt eq_nat_pr "
        "  (Tup_pt (App_pt tup_head_pr (Tup_pt p Empty_pt)) "
        "    (Tup_pt n Empty_pt)) = T_pt) /\\ "
        " (App_pt valid_proof_list_pr (Tup_pt p Empty_pt) = T_pt))"
    )

    with p.have(f"fwd: {lhs} ==> {rhs}").proof():
        p.assume(f"h_lhs: {lhs}")
        p.have(f"parts: {parts}").by_eq_mp(body_view, "h_lhs")
        p.split("parts", "(is_tup_ok, (head_ok, valid_ok))")
        p.have("tup_ex: ?h t. p = Tup_pt h t").by_eq_mp(
            is_tup_at, "is_tup_ok"
        )
        p.choose("h t", "tup_ex", eq_label="p_shape")
        head_at = SPECL([p._parse("h"), p._parse("t")], TUP_HEAD_PR_CORRECT)
        p.have(
            "head_ok_ht: "
            "App_pt eq_nat_pr (Tup_pt h (Tup_pt n Empty_pt)) = T_pt"
        ).by_rewrite_of("head_ok", ["p_shape", head_at])
        eq_nat_at = SPECL([p._parse("h"), p._parse("n")], EQ_NAT_PR_TRUE_VIEW)
        p.have("h_eq_n: h = n").by_eq_mp(eq_nat_at, "head_ok_ht")
        p.have("n_eq_h: n = h").by_thm(SYM(p.fact("h_eq_n")))
        p.have("valid_p: ValidProof_PRST p").by_eq_mp(valid_at, "valid_ok")
        p.thus(rhs).by_exists(["h", "t"], "p_shape", "n_eq_h", "valid_p")

    with p.have(f"rev: ({rhs}) ==> {lhs}").proof():
        p.assume(f"rhs_ex: {rhs}")
        p.choose("h t", "rhs_ex", eq_label="rhs_body")
        p.split("rhs_body", "(p_shape, (n_eq_h, valid_p))")
        p.have("tup_ex: ?h0 t0. p = Tup_pt h0 t0").by_exists(
            ["h", "t"], "p_shape"
        )
        p.have("is_tup_ok: App_pt is_tup_pr (Tup_pt p Empty_pt) = T_pt").by_eq_mp(
            SYM(is_tup_at), "tup_ex"
        )
        p.have("h_eq_n: h = n").by_thm(SYM(p.fact("n_eq_h")))
        p.have(
            "head_ok_ht: "
            "App_pt eq_nat_pr (Tup_pt h (Tup_pt n Empty_pt)) = T_pt"
        ).by(EQ_NAT_PR_CORRECT_TRUE, "h", "n", "h_eq_n")
        head_at = SPECL([p._parse("h"), p._parse("t")], TUP_HEAD_PR_CORRECT)
        p.have(
            "head_ok: "
            "App_pt eq_nat_pr "
            "  (Tup_pt (App_pt tup_head_pr (Tup_pt p Empty_pt)) "
            "    (Tup_pt n Empty_pt)) = T_pt"
        ).by_rewrite_of("head_ok_ht", ["p_shape", head_at])
        p.have(
            "valid_ok: App_pt valid_proof_list_pr (Tup_pt p Empty_pt) = T_pt"
        ).by_eq_mp(SYM(valid_at), "valid_p")
        p.have("tail_parts:").by_thm(CONJ(p.fact("head_ok"), p.fact("valid_ok")))
        p.have(f"parts: {parts}").by_thm(
            CONJ(p.fact("is_tup_ok"), p.fact("tail_parts"))
        )
        p.thus(lhs).by_eq_mp(SYM(body_view), "parts")

    p.thus(f"({lhs}) = ({rhs})").by_iff("fwd", "rev")


@proof
def PRST_INTERNALIZES_TRUE_PR_EVAL(p):
    r"""|- !f args. is_partial_pr_sym f /\ App_pt f args = T_pt
            ==> Prov_PRST (Eq_pf (App_pt f args) T_pt)."""
    p.goal(
        "!f args. is_partial_pr_sym f /\\ App_pt f args = T_pt "
        "==> Prov_PRST (Eq_pf (App_pt f args) T_pt)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


@proof
def PRST_INTERNALIZES_FALSE_PR_EVAL(p):
    r"""|- !f args. is_partial_pr_sym f /\ App_pt f args = F_pt
            ==> Prov_PRST (Eq_pf (App_pt f args) F_pt).

    DSL/proof friction: this should be the same evaluator package as the true
    branch, specialised to the false boolean. Keeping it separate avoids a
    too-strong Proof_PRST_pr-specific false-evaluation axiom.
    """
    p.goal(
        "!f args. is_partial_pr_sym f /\\ App_pt f args = F_pt "
        "==> Prov_PRST (Eq_pf (App_pt f args) F_pt)",
        types={"f": nat0_ty, "args": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# Stage 2B (d.5) -- modus ponens for Prov_PRST.
#
#     PROV_PRST_MP :
#         |- !f g. Prov_PRST f /\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g
#
# DESIGN NOTE: Proof_PRST has been refactored to the PR-checker shape:
# ValidProof_PRST validates the whole proof list, and Mem_PRST searches
# earlier lines for MP witnesses. That fixes the old single-tail bug where
# the same tail had to prove both f and Imp_pf f g.
#
# The theorem-level closure proof depends on a small PRST-list API:
# combine two proof lists into one valid list containing both conclusions,
# then cons g as an MP step. Those list API facts are currently the sorry
# obligations; PROV_PRST_MP itself is just witness plumbing.
#
# All downstream consumers (PROV_PRST_NUMERAL_EVAL, PROV_PRST_REPRESENTS,
# G2's D2 chain, ...) rely on MP.
# ---------------------------------------------------------------------------


@proof
def PROOF_PRST_VALID_MEM_SELF(p):
    """|- !P a. Proof_PRST P a ==> ValidProof_PRST P /\\ Mem_PRST a P."""
    p.goal(
        "!P a. Proof_PRST P a ==> ValidProof_PRST P /\\ Mem_PRST a P",
        types={"P": nat0_ty, "a": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_LIST_MERGE(p):
    """|- !P Q a b. ValidProof_PRST P /\\ Mem_PRST a P
              /\\ ValidProof_PRST Q /\\ Mem_PRST b Q
              ==> ?R. ValidProof_PRST R /\\ Mem_PRST a R /\\ Mem_PRST b R."""
    p.goal(
        "!P Q a b. "
        "ValidProof_PRST P /\\ Mem_PRST a P "
        "/\\ ValidProof_PRST Q /\\ Mem_PRST b Q "
        "==> ?R. ValidProof_PRST R /\\ Mem_PRST a R /\\ Mem_PRST b R",
        types={"P": nat0_ty, "Q": nat0_ty, "a": nat0_ty, "b": nat0_ty},
    )
    p.sorry()


@proof
def PROOF_PRST_LIST_COMBINE(p):
    """|- !a b. (?P. Proof_PRST P a) /\\ (?Q. Proof_PRST Q b)
              ==> ?R. ValidProof_PRST R /\\ Mem_PRST a R /\\ Mem_PRST b R."""
    from tactics import CONJ

    p.goal(
        "!a b. (?P. Proof_PRST P a) /\\ (?Q. Proof_PRST Q b) "
        "==> ?R. ValidProof_PRST R /\\ Mem_PRST a R /\\ Mem_PRST b R",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.assume("(ex_P, ex_Q): (?P. Proof_PRST P a) /\\ (?Q. Proof_PRST Q b)")
    p.choose("P", "ex_P", eq_label="proof_P")
    p.choose("Q", "ex_Q", eq_label="proof_Q")
    p.have("P_props: ValidProof_PRST P /\\ Mem_PRST a P").by(
        PROOF_PRST_VALID_MEM_SELF, "P", "a", "proof_P"
    )
    p.have("Q_props: ValidProof_PRST Q /\\ Mem_PRST b Q").by(
        PROOF_PRST_VALID_MEM_SELF, "Q", "b", "proof_Q"
    )
    p.split("P_props", "(valid_P, mem_a_P)")
    p.split("Q_props", "(valid_Q, mem_b_Q)")
    p.have("Q_payload: ValidProof_PRST Q /\\ Mem_PRST b Q").by(
        CONJ, "valid_Q", "mem_b_Q"
    )
    p.have(
        "merge_tail: Mem_PRST a P /\\ ValidProof_PRST Q /\\ Mem_PRST b Q"
    ).by(CONJ, "mem_a_P", "Q_payload")
    p.have(
        "merge_payload: ValidProof_PRST P /\\ Mem_PRST a P "
        "/\\ ValidProof_PRST Q /\\ Mem_PRST b Q"
    ).by(CONJ, "valid_P", "merge_tail")
    p.thus("?R. ValidProof_PRST R /\\ Mem_PRST a R /\\ Mem_PRST b R").by(
        PROOF_PRST_LIST_MERGE, "P", "Q", "a", "b", "merge_payload"
    )


@proof
def PROOF_PRST_CONS_MP_STEP(p):
    """|- !R f g. ValidProof_PRST R
              /\\ Mem_PRST f R
              /\\ Mem_PRST (Imp_pf f g) R
              ==> Proof_PRST (Tup_pt g R) g."""
    from tactics import SPEC, SPECL, SYM, CONJ
    from prst_syntax import _unfold_prst_rec as _unfold

    p.goal(
        "!R f g. ValidProof_PRST R /\\ Mem_PRST f R "
        "        /\\ Mem_PRST (Imp_pf f g) R "
        "        ==> Proof_PRST (Tup_pt g R) g",
        types={"R": nat0_ty, "f": nat0_ty, "g": nat0_ty},
    )
    p.fix("R f g")
    p.assume(
        "(valid_R, (mem_f, mem_imp)): "
        "ValidProof_PRST R /\\ Mem_PRST f R /\\ Mem_PRST (Imp_pf f g) R"
    )

    p.have(
        "mp_step: ?w. Mem_PRST w R /\\ Mem_PRST (Imp_pf w g) R"
    ).by_exists(["f"], "mem_f", "mem_imp")
    p.have(
        "step_ok: is_pr_axiom g \\/ "
        "(?w. Mem_PRST w R /\\ Mem_PRST (Imp_pf w g) R)"
    ).by_disj("mp_step")
    p.have(
        "valid_cons_ex: ?h t. "
        "Tup_pt g R = Tup_pt h t /\\ ValidProof_PRST t /\\ "
        "(is_pr_axiom h \\/ "
        " (?w. Mem_PRST w t /\\ Mem_PRST (Imp_pf w h) t))"
    ).by_exists(["g", "R"], "valid_R", "step_ok")

    valid_body = (
        "Tup_pt g R = Empty_pt \\/ "
        "(?h t. Tup_pt g R = Tup_pt h t /\\ ValidProof_PRST t /\\ "
        "       (is_pr_axiom h \\/ "
        "        (?w. Mem_PRST w t /\\ Mem_PRST (Imp_pf w h) t)))"
    )
    valid_rec = _unfold(_VALID_PROOF_PRST_REC, _VALID_PROOF_PRST_F_DEF)
    valid_cons_at = SPEC(p._parse("Tup_pt g R"), valid_rec)
    p.have(f"valid_cons_body: {valid_body}").by_disj("valid_cons_ex")
    p.have("valid_cons: ValidProof_PRST (Tup_pt g R)").by_eq_mp(
        SYM(valid_cons_at), "valid_cons_body"
    )

    p.have("g_refl: g = g").by_rewrite([])
    p.have("proof_view: g = g /\\ ValidProof_PRST (Tup_pt g R)").by(
        CONJ, "g_refl", "valid_cons"
    )
    proof_cons = SPECL(
        [p._parse("g"), p._parse("R"), p._parse("g")], PROOF_PRST_CONS
    )
    p.thus("Proof_PRST (Tup_pt g R) g").by_eq_mp(
        SYM(proof_cons), "proof_view"
    )


@proof
def MP_HAS_PROOF_PRST_LIST(p):
    """|- !f g. (?P. Proof_PRST P f)
              /\\ (?Q. Proof_PRST Q (Imp_pf f g))
              ==> ?R. Proof_PRST R g."""
    from tactics import CONJ

    p.goal(
        "!f g. (?P. Proof_PRST P f) /\\ (?Q. Proof_PRST Q (Imp_pf f g)) "
        "==> ?R. Proof_PRST R g",
        types={"f": nat0_ty, "g": nat0_ty},
    )
    p.fix("f g")
    p.assume(
        "(pf_ex, pfg_ex): "
        "(?P. Proof_PRST P f) /\\ (?Q. Proof_PRST Q (Imp_pf f g))"
    )
    p.have(
        "combined: ?R. ValidProof_PRST R "
        "           /\\ Mem_PRST f R "
        "           /\\ Mem_PRST (Imp_pf f g) R"
    ).by(
        PROOF_PRST_LIST_COMBINE,
        "f",
        "Imp_pf f g",
        CONJ(p.fact("pf_ex"), p.fact("pfg_ex")),
    )
    p.choose("R", "combined", eq_label="combined_body")
    p.split("combined_body", "(valid_R, (mem_f_R, mem_imp_R))")
    p.have("mp_payload: ValidProof_PRST R /\\ Mem_PRST f R /\\ Mem_PRST (Imp_pf f g) R").by_thm(
        CONJ(p.fact("valid_R"), CONJ(p.fact("mem_f_R"), p.fact("mem_imp_R")))
    )
    p.have("proof_g: Proof_PRST (Tup_pt g R) g").by(
        PROOF_PRST_CONS_MP_STEP,
        "R",
        "f",
        "g",
        "mp_payload",
    )
    p.thus("?R. Proof_PRST R g").by_exists(["Tup_pt g R"], "proof_g")


@proof
def PROV_PRST_MP(p):
    """|- !f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g."""
    from tactics import SPEC, SYM, CONJ

    p.goal(
        "!f g. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g",
        types={"f": nat0_ty, "g": nat0_ty},
    )
    p.fix("f g")
    p.assume("(pf, pfg): Prov_PRST f /\\ Prov_PRST (Imp_pf f g)")
    prov_at_f = SPEC(p._parse("f"), PROV_PRST_AT)
    prov_at_imp = SPEC(p._parse("Imp_pf f g"), PROV_PRST_AT)
    prov_at_g = SPEC(p._parse("g"), PROV_PRST_AT)
    p.have("ex_f: ?P. Proof_PRST P f").by_eq_mp(prov_at_f, "pf")
    p.have("ex_imp: ?Q. Proof_PRST Q (Imp_pf f g)").by_eq_mp(prov_at_imp, "pfg")
    p.have("ex_g: ?R. Proof_PRST R g").by(
        MP_HAS_PROOF_PRST_LIST,
        "f",
        "g",
        CONJ(p.fact("ex_f"), p.fact("ex_imp")),
    )
    p.thus("Prov_PRST g").by_eq_mp(SYM(prov_at_g), "ex_g")


# ---------------------------------------------------------------------------
# Stage 2B (e) -- internal arithmetic via PR symbols.
#
# The public evaluator schemas below are now proof targets, not primitive
# obligations. Their remaining obligations sit at the actual decomposition
# boundaries:
#
#   * numeral_pr: recursion base/step.
#   * substitute_pr: one structural clause for each PRST syntax family, plus
#     the course-recursion completeness bridge.
#   * diag_pr: defining composition and PRST equality chaining from the
#     numeral/substitute component evaluations.
# ---------------------------------------------------------------------------


_SUBSTITUTE_EVAL_FULL = (
    "!F t v. Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute F t v))"
)

_SUBSTITUTE_EVAL_EMPTY_CLAUSE = (
    "!t v. Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt Empty_pt (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute Empty_pt t v))"
)

_SUBSTITUTE_EVAL_VAR_HIT_CLAUSE = (
    "!t v. Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Var_pt v) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Var_pt v) t v))"
)

_SUBSTITUTE_EVAL_VAR_MISS_CLAUSE = (
    "!x t v. ~(x = v) ==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Var_pt x) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Var_pt x) t v))"
)

_SUBSTITUTE_EVAL_TUP_CLAUSE = (
    "!a b t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute a t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute b t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Tup_pt a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Tup_pt a b) t v))"
)

_SUBSTITUTE_EVAL_APP_CLAUSE = (
    "!f args t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt args (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute args t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (App_pt f args) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (App_pt f args) t v))"
)

_SUBSTITUTE_EVAL_EQ_CLAUSE = (
    "!a b t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute a t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute b t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Eq_pf a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Eq_pf a b) t v))"
)

_SUBSTITUTE_EVAL_IN_CLAUSE = (
    "!a b t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute a t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute b t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (In_pa a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (In_pa a b) t v))"
)

_SUBSTITUTE_EVAL_NOT_CLAUSE = (
    "!F t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute F t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Not_pf F) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Not_pf F) t v))"
)

_SUBSTITUTE_EVAL_IMP_CLAUSE = (
    "!F G t v. "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute F t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt G (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute G t v)) "
    "==> Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr "
    "    (Tup_pt (Imp_pf F G) (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute (Imp_pf F G) t v))"
)

_SUBSTITUTE_EVAL_OPAQUE_CLAUSE = (
    "!F t v. ~(is_pterm F) /\\ ~(is_pform F) ==> "
    "Prov_PRST (Eq_pf "
    "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
    "  (substitute F t v))"
)

_SUBSTITUTE_EVAL_STRUCTURAL_GOAL = (
    " ==> ".join(
        f"({clause})"
        for clause in [
            _SUBSTITUTE_EVAL_EMPTY_CLAUSE,
            _SUBSTITUTE_EVAL_VAR_HIT_CLAUSE,
            _SUBSTITUTE_EVAL_VAR_MISS_CLAUSE,
            _SUBSTITUTE_EVAL_TUP_CLAUSE,
            _SUBSTITUTE_EVAL_APP_CLAUSE,
            _SUBSTITUTE_EVAL_EQ_CLAUSE,
            _SUBSTITUTE_EVAL_IN_CLAUSE,
            _SUBSTITUTE_EVAL_NOT_CLAUSE,
            _SUBSTITUTE_EVAL_IMP_CLAUSE,
            _SUBSTITUTE_EVAL_OPAQUE_CLAUSE,
        ]
    )
    + " ==> "
    + _SUBSTITUTE_EVAL_FULL
)


@proof
def PROV_PRST_SUBSTITUTE_EMPTY_EVAL_CLAUSE(p):
    """|- !t v. Prov_PRST (Eq_pf
          (App_pt substitute_pr (Tup_pt Empty_pt (Tup_pt t (Tup_pt v Empty_pt))))
          (substitute Empty_pt t v))."""
    p.goal(
        "!t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt Empty_pt (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute Empty_pt t v))",
        types={"t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_VAR_HIT_EVAL_CLAUSE(p):
    """|- !t v. Prov_PRST (Eq_pf
          (App_pt substitute_pr (Tup_pt (Var_pt v) (Tup_pt t (Tup_pt v Empty_pt))))
          (substitute (Var_pt v) t v))."""
    p.goal(
        "!t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Var_pt v) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Var_pt v) t v))",
        types={"t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_VAR_MISS_EVAL_CLAUSE(p):
    """|- !x t v. ~(x = v) ==> Prov_PRST (Eq_pf
          (App_pt substitute_pr (Tup_pt (Var_pt x) (Tup_pt t (Tup_pt v Empty_pt))))
          (substitute (Var_pt x) t v))."""
    p.goal(
        "!x t v. ~(x = v) ==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Var_pt x) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Var_pt x) t v))",
        types={"x": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_TUP_EVAL_CLAUSE(p):
    """|- !a b t v. eval a ==> eval b ==> eval (Tup_pt a b)."""
    p.goal(
        "!a b t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute a t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute b t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Tup_pt a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Tup_pt a b) t v))",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_APP_EVAL_CLAUSE(p):
    """|- !f args t v. eval args ==> eval (App_pt f args)."""
    p.goal(
        "!f args t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt args (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute args t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (App_pt f args) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (App_pt f args) t v))",
        types={"f": nat0_ty, "args": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_EQ_EVAL_CLAUSE(p):
    """|- !a b t v. eval a ==> eval b ==> eval (Eq_pf a b)."""
    p.goal(
        "!a b t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute a t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute b t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Eq_pf a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Eq_pf a b) t v))",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_IN_EVAL_CLAUSE(p):
    """|- !a b t v. eval a ==> eval b ==> eval (In_pa a b)."""
    p.goal(
        "!a b t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt a (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute a t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt b (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute b t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (In_pa a b) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (In_pa a b) t v))",
        types={"a": nat0_ty, "b": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_NOT_EVAL_CLAUSE(p):
    """|- !F t v. eval F ==> eval (Not_pf F)."""
    p.goal(
        "!F t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Not_pf F) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Not_pf F) t v))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_IMP_EVAL_CLAUSE(p):
    """|- !F G t v. eval F ==> eval G ==> eval (Imp_pf F G)."""
    p.goal(
        "!F G t v. "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt G (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute G t v)) "
        "==> Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr "
        "    (Tup_pt (Imp_pf F G) (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute (Imp_pf F G) t v))",
        types={"F": nat0_ty, "G": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_OPAQUE_EVAL_CLAUSE(p):
    """|- !F t v. ~(is_pterm F) /\\ ~(is_pform F) ==> eval F."""
    p.goal(
        "!F t v. ~(is_pterm F) /\\ ~(is_pform F) ==> "
        "Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_EVAL_BY_STRUCTURAL_CLAUSES(p):
    """Close substitute_pr evaluation from the per-constructor clauses."""
    p.goal(
        _SUBSTITUTE_EVAL_STRUCTURAL_GOAL,
        types={"F": nat0_ty, "G": nat0_ty, "a": nat0_ty, "b": nat0_ty,
               "f": nat0_ty, "args": nat0_ty, "t": nat0_ty, "v": nat0_ty,
               "x": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_SUBSTITUTE_EVAL(p):
    """|- !F t v. Prov_PRST (Eq_pf (App_pt substitute_pr
                                    (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt))))
                                  (substitute F t v))."""
    p.goal(
        "!F t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v))",
        types={"F": nat0_ty, "t": nat0_ty, "v": nat0_ty},
    )
    p.have("empty_clause:").by_thm(PROV_PRST_SUBSTITUTE_EMPTY_EVAL_CLAUSE)
    p.have("var_hit_clause:").by_thm(PROV_PRST_SUBSTITUTE_VAR_HIT_EVAL_CLAUSE)
    p.have("var_miss_clause:").by_thm(PROV_PRST_SUBSTITUTE_VAR_MISS_EVAL_CLAUSE)
    p.have("tup_clause:").by_thm(PROV_PRST_SUBSTITUTE_TUP_EVAL_CLAUSE)
    p.have("app_clause:").by_thm(PROV_PRST_SUBSTITUTE_APP_EVAL_CLAUSE)
    p.have("eq_clause:").by_thm(PROV_PRST_SUBSTITUTE_EQ_EVAL_CLAUSE)
    p.have("in_clause:").by_thm(PROV_PRST_SUBSTITUTE_IN_EVAL_CLAUSE)
    p.have("not_clause:").by_thm(PROV_PRST_SUBSTITUTE_NOT_EVAL_CLAUSE)
    p.have("imp_clause:").by_thm(PROV_PRST_SUBSTITUTE_IMP_EVAL_CLAUSE)
    p.have("opaque_clause:").by_thm(PROV_PRST_SUBSTITUTE_OPAQUE_EVAL_CLAUSE)
    p.thus(
        "!F t v. Prov_PRST (Eq_pf "
        "  (App_pt substitute_pr (Tup_pt F (Tup_pt t (Tup_pt v Empty_pt)))) "
        "  (substitute F t v))"
    ).by(
        PROV_PRST_SUBSTITUTE_EVAL_BY_STRUCTURAL_CLAUSES,
        "empty_clause",
        "var_hit_clause",
        "var_miss_clause",
        "tup_clause",
        "app_clause",
        "eq_clause",
        "in_clause",
        "not_clause",
        "imp_clause",
        "opaque_clause",
    )


@proof
def PROV_PRST_NUMERAL_ZERO_EVAL_CLAUSE(p):
    """|- Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt 0 Empty_pt)) (quote_hf 0))."""
    p.goal(
        "Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt 0 Empty_pt)) (quote_hf 0))"
    )
    p.sorry()


@proof
def PROV_PRST_NUMERAL_SUC_EVAL_CLAUSE(p):
    """|- !n. eval n ==> eval (SUC0 n)."""
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt)) (quote_hf n)) "
        "==> Prov_PRST (Eq_pf "
        "      (App_pt numeral_pr (Tup_pt (SUC0 n) Empty_pt)) "
        "      (quote_hf (SUC0 n)))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_NUMERAL_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt))
                               (quote_hf n))."""
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt)) (quote_hf n))",
        types={"n": nat0_ty},
    )
    p.fix("n")
    with p.induction("n"):
        with p.base():
            p.thus(
                "Prov_PRST (Eq_pf "
                "  (App_pt numeral_pr (Tup_pt 0 Empty_pt)) "
                "  (quote_hf 0))"
            ).by_thm(PROV_PRST_NUMERAL_ZERO_EVAL_CLAUSE)
        with p.step("IH"):
            p.thus(
                "Prov_PRST (Eq_pf "
                "  (App_pt numeral_pr (Tup_pt (SUC0 n) Empty_pt)) "
                "  (quote_hf (SUC0 n)))"
            ).by(PROV_PRST_NUMERAL_SUC_EVAL_CLAUSE, "n", "IH")


@proof
def PROV_PRST_DIAG_DEFINING_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt))
               (App_pt substitute_pr
                 (Tup_pt n
                   (Tup_pt (App_pt numeral_pr (Tup_pt n Empty_pt))
                     (Tup_pt var_x Empty_pt)))))."""
    p.goal(
        "!n. Prov_PRST (Eq_pf "
        "  (App_pt diag_pr (Tup_pt n Empty_pt)) "
        "  (App_pt substitute_pr "
        "    (Tup_pt n "
        "      (Tup_pt (App_pt numeral_pr (Tup_pt n Empty_pt)) "
        "        (Tup_pt var_x Empty_pt)))))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_DIAG_EVAL_BY_COMPONENTS(p):
    """Close diag_pr evaluation from definition, numeral, substitute, and equality."""
    p.goal(
        "!n. "
        "Prov_PRST (Eq_pf "
        "  (App_pt diag_pr (Tup_pt n Empty_pt)) "
        "  (App_pt substitute_pr "
        "    (Tup_pt n "
        "      (Tup_pt (App_pt numeral_pr (Tup_pt n Empty_pt)) "
        "        (Tup_pt var_x Empty_pt))))) "
        "==> Prov_PRST (Eq_pf "
        "      (App_pt numeral_pr (Tup_pt n Empty_pt)) "
        "      (quote_hf n)) "
        "==> Prov_PRST (Eq_pf "
        "      (App_pt substitute_pr "
        "        (Tup_pt n (Tup_pt (quote_hf n) (Tup_pt var_x Empty_pt)))) "
        "      (substitute n (quote_hf n) var_x)) "
        "==> Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n))",
        types={"n": nat0_ty},
    )
    p.sorry()


@proof
def PROV_PRST_DIAG_EVAL(p):
    """|- !n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n))."""
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n))",
        types={"n": nat0_ty},
    )
    p.fix("n")
    p.have("diag_def:").by(PROV_PRST_DIAG_DEFINING_EVAL, "n")
    p.have("numeral_eval:").by(PROV_PRST_NUMERAL_EVAL, "n")
    p.have("subst_eval:").by(
        PROV_PRST_SUBSTITUTE_EVAL, "n", "quote_hf n", "var_x"
    )
    p.thus(
        "Prov_PRST (Eq_pf (App_pt diag_pr (Tup_pt n Empty_pt)) (diag n))"
    ).by(
        PROV_PRST_DIAG_EVAL_BY_COMPONENTS,
        "n",
        "diag_def",
        "numeral_eval",
        "subst_eval",
    )


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
    """|- is_pform Prov_PRST_internal.

    Unblocked by the Layer 2 relax of IS_PTERM's App branch:
    IS_PTERM_AT_APP now reads `is_pterm (App_pt f args) =
    is_partial_pr_sym f /\\ is_pterm args`. `find_proof_pr =
    mu_sym Proof_PRST_pr` is admitted at the partial-PR layer via
    IS_PARTIAL_PR_SYM_MU.

    Structure: unfold Prov_PRST_internal to an Eq_pf form, apply
    IS_PFORM_AT_EQ, then prove `is_pterm` for both sides via
    IS_PTERM_AT_APP / IS_PTERM_AT_TUP / IS_PTERM_AT_VAR /
    IS_PTERM_AT_EMPTY recursively. Every `is_partial_pr_sym _`
    obligation is discharged by `IS_PR_SYM_IMP_PARTIAL` (from
    prst_syntax) composed with the relevant `IS_PR_SYM_*` (or by
    `IS_PARTIAL_PR_SYM_MU` for the mu_sym slot).
    """
    from prst_syntax import (
        IS_PFORM_AT_EQ,
        IS_PTERM_AT_APP,
        IS_PTERM_AT_TUP,
        IS_PTERM_AT_VAR,
        IS_PTERM_AT_EMPTY,
        IS_PR_SYM_IMP_PARTIAL,
    )
    from prst_pr import (
        T_PT_DEF,
        ADJ_PT_DEF,
        Proof_PRST_pr_def,
        FIND_PROOF_PR_DEF,
        IS_PR_SYM_ADJ,
        IS_PR_SYM_PROOF_PRST_PR,
        IS_PARTIAL_PR_SYM_MU,
    )
    from tactics import SPECL, CONJ, SYM, AP_TERM
    from basics import mk_const as _mk_const

    p.goal("is_pform Prov_PRST_internal")

    # --- is_partial_pr_sym facts for the symbols that head App_pts ---
    # adj_sym (head of T_pt's App_pt expansion).
    p.have("h_pr_adj: is_pr_sym adj_sym").by_thm(IS_PR_SYM_ADJ)
    p.have("h_pp_adj: is_partial_pr_sym adj_sym").by(
        IS_PR_SYM_IMP_PARTIAL, "adj_sym", "h_pr_adj"
    )
    p.have("h_pr_proof: is_pr_sym Proof_PRST_pr").by_thm(
        IS_PR_SYM_PROOF_PRST_PR
    )
    p.have(
        "h_pp_proof: is_partial_pr_sym Proof_PRST_pr"
    ).by(IS_PR_SYM_IMP_PARTIAL, "Proof_PRST_pr", "h_pr_proof")
    # find_proof_pr = mu_sym Proof_PRST_pr; lift via IS_PARTIAL_PR_SYM_MU.
    p.have(
        "h_pp_find_inner: is_partial_pr_sym (mu_sym Proof_PRST_pr)"
    ).by(IS_PARTIAL_PR_SYM_MU, "Proof_PRST_pr", "h_pp_proof")
    p.have(
        "h_pp_find: is_partial_pr_sym find_proof_pr"
    ).by_rewrite_of("h_pp_find_inner", [SYM(FIND_PROOF_PR_DEF)])

    # --- is_pterm Empty_pt (atomic) ---
    p.have("h_pt_empty: is_pterm Empty_pt").by_thm(IS_PTERM_AT_EMPTY)

    # --- is_pterm (Var_pt var_x) ---
    p.have("h_pt_var: is_pterm (Var_pt var_x)").by(IS_PTERM_AT_VAR, "var_x")

    # --- is_pterm (Tup_pt (Var_pt var_x) Empty_pt) ---
    p.have(
        "h_pt_tup_vx: is_pterm (Tup_pt (Var_pt var_x) Empty_pt)"
    ).by_eq_mp(
        SYM(SPECL([p._parse("Var_pt var_x"), p._parse("Empty_pt")], IS_PTERM_AT_TUP)),
        CONJ(p.fact("h_pt_var"), p.fact("h_pt_empty")),
    )

    # --- is_pterm (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) ---
    p.have(
        "h_pt_app_find: is_pterm "
        "  (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("find_proof_pr"),
             p._parse("Tup_pt (Var_pt var_x) Empty_pt")],
            IS_PTERM_AT_APP,
        )),
        CONJ(p.fact("h_pp_find"), p.fact("h_pt_tup_vx")),
    )

    # --- is_pterm (Tup_pt <app_find> (Tup_pt (Var_pt var_x) Empty_pt)) ---
    p.have(
        "h_pt_outer_tup: is_pterm "
        "  (Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
        "          (Tup_pt (Var_pt var_x) Empty_pt))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)"),
             p._parse("Tup_pt (Var_pt var_x) Empty_pt")],
            IS_PTERM_AT_TUP,
        )),
        CONJ(p.fact("h_pt_app_find"), p.fact("h_pt_tup_vx")),
    )

    # --- LHS of Eq_pf: is_pterm (App_pt Proof_PRST_pr <outer_tup>) ---
    p.have(
        "h_pt_lhs: is_pterm "
        "  (App_pt Proof_PRST_pr "
        "    (Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
        "            (Tup_pt (Var_pt var_x) Empty_pt)))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("Proof_PRST_pr"),
             p._parse(
                "Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
                "       (Tup_pt (Var_pt var_x) Empty_pt)"
             )],
            IS_PTERM_AT_APP,
        )),
        CONJ(p.fact("h_pp_proof"), p.fact("h_pt_outer_tup")),
    )

    # --- is_pterm T_pt (= Adj_pt Empty_pt Empty_pt
    #                  = App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt))) ---
    p.have(
        "h_pt_tup_ee: is_pterm (Tup_pt Empty_pt Empty_pt)"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("Empty_pt"), p._parse("Empty_pt")], IS_PTERM_AT_TUP
        )),
        CONJ(p.fact("h_pt_empty"), p.fact("h_pt_empty")),
    )
    p.have(
        "h_pt_tup_eee: is_pterm (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("Empty_pt"), p._parse("Tup_pt Empty_pt Empty_pt")],
            IS_PTERM_AT_TUP,
        )),
        CONJ(p.fact("h_pt_empty"), p.fact("h_pt_tup_ee")),
    )
    p.have(
        "h_pt_app_adj: is_pterm "
        "  (App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)))"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse("adj_sym"),
             p._parse("Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt)")],
            IS_PTERM_AT_APP,
        )),
        CONJ(p.fact("h_pp_adj"), p.fact("h_pt_tup_eee")),
    )
    # Bridge: T_pt = Adj_pt Empty_pt Empty_pt = App_pt adj_sym (...).
    adj_at = p.unfold(ADJ_PT_DEF, "Empty_pt", "Empty_pt")
    # adj_at: Adj_pt Empty_pt Empty_pt = App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt Empty_pt))
    is_pterm_const = _mk_const("is_pterm", [])
    p.have("h_pt_rhs: is_pterm T_pt").by_rewrite_of(
        "h_pt_app_adj", [SYM(adj_at), SYM(T_PT_DEF)]
    )

    # --- Combine: is_pform (Eq_pf lhs T_pt) ---
    p.have(
        "h_pform_inner: is_pform "
        "  (Eq_pf "
        "    (App_pt Proof_PRST_pr "
        "      (Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
        "              (Tup_pt (Var_pt var_x) Empty_pt))) "
        "    T_pt)"
    ).by_eq_mp(
        SYM(SPECL(
            [p._parse(
                "App_pt Proof_PRST_pr "
                "  (Tup_pt (App_pt find_proof_pr (Tup_pt (Var_pt var_x) Empty_pt)) "
                "          (Tup_pt (Var_pt var_x) Empty_pt))"
             ),
             p._parse("T_pt")],
            IS_PFORM_AT_EQ,
        )),
        CONJ(p.fact("h_pt_lhs"), p.fact("h_pt_rhs")),
    )

    # Fold back to Prov_PRST_internal via prov_prst_internal_def.
    p.thus("is_pform Prov_PRST_internal").by_rewrite_of(
        "h_pform_inner", [SYM(prov_prst_internal_def)]
    )


# Helper: |- !v. free_in_p Empty_pt v = F.
#
# Empty_pt matches NONE of free_in_p's 7 disjuncts (the constructor
# patterns Var_pt / Tup_pt / Eq_pf / In_pa / Not_pf / Imp_pf / App_pt),
# so the recursive body collapses to F at Empty_pt. derive_rec_eq_pw
# can't generate this case (it dispatches one matched disjunct, not the
# all-mismatch fallback), and the IS_PTERM_AT_EMPTY pattern is also
# inapplicable (is_pterm has an Empty_pt disjunct; free_in_p does not).
#
# Manual proof: unfold via FREE_IN_P_REC at Empty_pt, then refute each
# of the 7 disjuncts via the constructor-vs-Empty disjointness lemma in
# prst_syntax (VAR_PT_NEQ_EMPTY_PT / TUP_PT_NEQ_EMPTY_PT / ...).
#
# DSL friction:
#  * No general "evaluate recursive body at a non-matched constructor
#    to F" helper. The 7 cases are templatic but have to be spelled out.
#  * `cases_on` with multi-binder existential leaves (`?a b. ...`)
#    auto-introduces only the outermost binder. The second binder needs
#    an explicit `p.choose(...)` inside the case.
#  * `_h{n}` placeholder labels in `p.split("body", "(c_eq, _)")` don't
#    survive across nested blocks reliably; we name the first conjunct
#    explicitly and discard the rest with `_`.
@proof
def FREE_IN_P_AT_EMPTY(p):
    """|- !v. free_in_p Empty_pt v = F."""
    from tactics import SPEC, AP_THM, BETA_CONV, TRANS, SYM, EQF_INTRO
    from basics import rand
    from prst_syntax import (
        FREE_IN_P_REC,
        VAR_PT_NEQ_EMPTY_PT,
        TUP_PT_NEQ_EMPTY_PT,
        APP_PT_NEQ_EMPTY_PT,
        EQ_PF_NEQ_EMPTY_PT,
        IN_PA_NEQ_EMPTY_PT,
        NOT_PF_NEQ_EMPTY_PT,
        IMP_PF_NEQ_EMPTY_PT,
    )

    p.goal("!v. free_in_p Empty_pt v = F", types={"v": nat0_ty})
    p.fix("v")

    # eq_full: free_in_p Empty_pt v = <7-disjunct body[Empty_pt/n]>.
    # FREE_IN_P_REC is `!n. free_in_p n = \v. body`; instantiate at n
    # := Empty_pt, AP_THM at v, beta-reduce.
    rec_empty_fn = SPEC(p._parse("Empty_pt"), FREE_IN_P_REC)
    rec_at = AP_THM(rec_empty_fn, p._parse("v"))
    rhs_beta = BETA_CONV(rand(rec_at._concl))
    eq_full = TRANS(rec_at, rhs_beta)
    body = (
        "(?x. Empty_pt = Var_pt x /\\ v = x) \\/ "
        "(?a b. Empty_pt = Tup_pt a b /\\ "
        "        (free_in_p a v \\/ free_in_p b v)) \\/ "
        "(?a b. Empty_pt = Eq_pf a b /\\ "
        "        (free_in_p a v \\/ free_in_p b v)) \\/ "
        "(?a b. Empty_pt = In_pa a b /\\ "
        "        (free_in_p a v \\/ free_in_p b v)) \\/ "
        "(?x. Empty_pt = Not_pf x /\\ free_in_p x v) \\/ "
        "(?a b. Empty_pt = Imp_pf a b /\\ "
        "        (free_in_p a v \\/ free_in_p b v)) \\/ "
        "(?fn args. Empty_pt = App_pt fn args /\\ free_in_p args v)"
    )
    p.have(f"eq_full: free_in_p Empty_pt v = ({body})").by_thm(eq_full)

    with p.have("neg: ~ free_in_p Empty_pt v").proof():
        with p.suppose("h: free_in_p Empty_pt v"):
            p.have(f"h_body: {body}").by_eq_mp("eq_full", "h")
            with p.cases_on("h_body"):
                # Var_pt: ?x. Empty_pt = Var_pt x /\ v = x.
                with p.case("c1: ?x. Empty_pt = Var_pt x /\\ v = x"):
                    p.split("x_eq", "(c_eq, _)")
                    p.have("c_neq: ~(Var_pt x = Empty_pt)").by(
                        VAR_PT_NEQ_EMPTY_PT, "x"
                    )
                    p.have("c_eq_sym: Var_pt x = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # Tup_pt
                with p.case(
                    "c2: ?a b. Empty_pt = Tup_pt a b /\\ "
                    "        (free_in_p a v \\/ free_in_p b v)"
                ):
                    p.split("b_eq", "(c_eq, _)")
                    p.have("c_neq: ~(Tup_pt a b = Empty_pt)").by(
                        TUP_PT_NEQ_EMPTY_PT, "a", "b"
                    )
                    p.have("c_eq_sym: Tup_pt a b = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # Eq_pf
                with p.case(
                    "c3: ?a b. Empty_pt = Eq_pf a b /\\ "
                    "        (free_in_p a v \\/ free_in_p b v)"
                ):
                    p.split("b_eq", "(c_eq, _)")
                    p.have("c_neq: ~(Eq_pf a b = Empty_pt)").by(
                        EQ_PF_NEQ_EMPTY_PT, "a", "b"
                    )
                    p.have("c_eq_sym: Eq_pf a b = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # In_pa
                with p.case(
                    "c4: ?a b. Empty_pt = In_pa a b /\\ "
                    "        (free_in_p a v \\/ free_in_p b v)"
                ):
                    p.split("b_eq", "(c_eq, _)")
                    p.have("c_neq: ~(In_pa a b = Empty_pt)").by(
                        IN_PA_NEQ_EMPTY_PT, "a", "b"
                    )
                    p.have("c_eq_sym: In_pa a b = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # Not_pf
                with p.case(
                    "c5: ?x. Empty_pt = Not_pf x /\\ free_in_p x v"
                ):
                    p.split("x_eq", "(c_eq, _)")
                    p.have("c_neq: ~(Not_pf x = Empty_pt)").by(
                        NOT_PF_NEQ_EMPTY_PT, "x"
                    )
                    p.have("c_eq_sym: Not_pf x = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # Imp_pf
                with p.case(
                    "c6: ?a b. Empty_pt = Imp_pf a b /\\ "
                    "        (free_in_p a v \\/ free_in_p b v)"
                ):
                    p.split("b_eq", "(c_eq, _)")
                    p.have("c_neq: ~(Imp_pf a b = Empty_pt)").by(
                        IMP_PF_NEQ_EMPTY_PT, "a", "b"
                    )
                    p.have("c_eq_sym: Imp_pf a b = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")
                # App_pt
                with p.case(
                    "c7: ?fn args. Empty_pt = App_pt fn args /\\ "
                    "        free_in_p args v"
                ):
                    p.split("args_eq", "(c_eq, _)")
                    p.have("c_neq: ~(App_pt fn args = Empty_pt)").by(
                        APP_PT_NEQ_EMPTY_PT, "fn", "args"
                    )
                    p.have("c_eq_sym: App_pt fn args = Empty_pt").by_thm(
                        SYM(p.fact("c_eq"))
                    )
                    p.absurd().by_conj("c_neq", "c_eq_sym")

    # ~P -> (P = F): EQF_INTRO yields `F = P`; SYM flips to `P = F`.
    p.thus("free_in_p Empty_pt v = F").by_thm(SYM(EQF_INTRO(p.fact("neg"))))


@proof
def FREE_IN_PROV_PRST_INTERNAL(p):
    """|- !v. free_in_p Prov_PRST_internal v = (v = var_x).

    Prov_PRST_internal unfolds to ``Eq_pf <lhs> T_pt`` where
    <lhs> = App_pt Proof_PRST_pr (Tup_pt (App_pt find_proof_pr
              (Tup_pt (Var_pt var_x) Empty_pt))
            (Tup_pt (Var_pt var_x) Empty_pt)).

    free_in_p reduction:
      * On T_pt = App_pt adj_sym (Tup_pt Empty_pt (Tup_pt Empty_pt
        Empty_pt)): everything bottoms out at Empty_pt, so free_in_p
        T_pt v = F.
      * On the lhs Eq_pf-LHS: free_in_p (App_pt _ args) v reduces to
        free_in_p args v (FREE_IN_P_AT_APP, no constraint on the fn
        slot -- contrast is_pterm which requires is_pr_sym). The two
        Tup_pt cons cells each reduce to free_in_p (Var_pt var_x) v
        \\/ free_in_p Empty_pt v = (v = var_x) \\/ F = (v = var_x).
      * Result: (v = var_x) \\/ F = (v = var_x).

    The free_in_p computation is independent of well-formedness, so
    the IS_PFORM_PROV_PRST_INTERNAL design hole (mu_sym not in
    is_pr_sym) does not block this lemma.
    """
    from prst_pr import T_PT_DEF, ADJ_PT_DEF
    from prst_syntax import (
        FREE_IN_P_AT_EQ,
        FREE_IN_P_AT_APP,
        FREE_IN_P_AT_TUP,
        FREE_IN_P_AT_VAR,
    )
    from tactics import (
        OR_F_LEFT,
        OR_F_RIGHT,
        DISJ_CASES,
        DISJ1,
        DEDUCT_ANTISYM_RULE,
        GEN,
        DISCH,
    )
    from fusion import Var, ASSUME, bool_ty
    from basics import mk_app, mk_const

    # Local OR_IDEMP: |- !p. (p \/ p) = p. Used to collapse the two
    # copies of `(v = var_x) \/ F` that fall out of the symmetric
    # `Tup_pt (App_pt find_proof_pr ...) (Tup_pt (Var_pt var_x) Empty_pt)`
    # split. tactics.py ships OR_F_LEFT/RIGHT but not OR_IDEMP, and
    # AC_PROVE handles assoc+comm but not idempotence.
    #
    # DSL friction: by_rewrite's normal-form check is strict modulo the
    # supplied + active simp rules. Without OR_IDEMP, `(v=var_x) \/
    # (v=var_x)` on the LHS won't collapse to match the bare `v=var_x`
    # RHS even though they are obviously equivalent. Pyzar has no
    # built-in propositional simplifier; idempotence is opt-in.
    _pv = Var("p", bool_ty)
    _or_pp = mk_app(mk_const("\\/", []), _pv, _pv)
    _or_pp_th = ASSUME(_or_pp)
    _p_imp_p = DISCH(_pv, ASSUME(_pv))
    _OR_IDEMP = GEN(
        _pv,
        DEDUCT_ANTISYM_RULE(
            DISJ1(ASSUME(_pv), _pv),  # p |- p \/ p
            DISJ_CASES(_or_pp_th, _p_imp_p, _p_imp_p),  # p \/ p |- p
        ),
    )

    p.goal(
        "!v. free_in_p Prov_PRST_internal v = (v = var_x)",
        types={"v": nat0_ty},
    )
    p.fix("v")
    # Applied-form of ADJ_PT_DEF at the concrete arguments used by T_pt.
    # ADJ_PT_DEF is `Adj_pt = \a b. App_pt adj_sym ...`; rewriting with
    # the lambda form alone wouldn't beta-reduce inside by_rewrite (the
    # rewriter doesn't beta by default; that's by_rewrite_of(beta=True)
    # / by_unfold territory). p.unfold delivers the post-beta applied
    # equation at the concrete args directly.
    adj_at = p.unfold(ADJ_PT_DEF, "Empty_pt", "Empty_pt")

    p.thus("free_in_p Prov_PRST_internal v = (v = var_x)").by_rewrite([
        prov_prst_internal_def,
        T_PT_DEF,
        adj_at,
        FREE_IN_P_AT_EQ,
        FREE_IN_P_AT_APP,
        FREE_IN_P_AT_TUP,
        FREE_IN_P_AT_VAR,
        FREE_IN_P_AT_EMPTY,
        OR_F_LEFT,
        OR_F_RIGHT,
        _OR_IDEMP,
    ])


@proof
def PROV_PRST_REPRESENTS(p):
    """|- !n. Prov_PRST n <=>
              Prov_PRST (substitute_p Prov_PRST_internal (quote_hf n) var_x).

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
        "    Prov_PRST (substitute_p Prov_PRST_internal (quote_hf n) var_x)",
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
# disjunct in is_pr_axiom), wraps it together with is_pr_def_instance
# and PRST-native reflexivity, and
# defines Prov_PRST. PRST has no set-theoretic axioms (Jensen-Karp
# 1971), and no quantifier rules. Any propositional fact needed inside
# PRST is re-derived directly from the Hilbert axioms.
# ---------------------------------------------------------------------------


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 2B (PRST) -- the PRST proof system.")
    print("    IS_PR_REFL_DEF         :", pp_thm(IS_PR_REFL_DEF))
    print("    IS_PR_REFL_HOLDS       :", pp_thm(IS_PR_REFL_HOLDS))
    print("    IS_PR_AXIOM_DEF        :", pp_thm(IS_PR_AXIOM_DEF))
    print("    PROV_PRST_DEF          :", pp_thm(PROV_PRST_DEF))
    print("    PROV_PRST_AX           :", pp_thm(PROV_PRST_AX))
    print("    PROV_PRST_MP           :", pp_thm(PROV_PRST_MP))
    print()
    print("Stage 2B (d.1) -- PR-defining-equation theorems (specialisations).")
    print("    PROV_PRST_ZERO_DEF       :", pp_thm(PROV_PRST_ZERO_DEF))
    print("    PROV_PRST_PROJ_DEF       :", pp_thm(PROV_PRST_PROJ_DEF))
    print("    PROV_PRST_IF_IN_TRUE_DEF :", pp_thm(PROV_PRST_IF_IN_TRUE_DEF))
    print("    PROV_PRST_REC_BASE_DEF   :", pp_thm(PROV_PRST_REC_BASE_DEF))
    print()
    print("Stage 2B (d.2) -- substitute-into-axiom derived rule.")
    print("    PROV_PRST_SUBST             :", pp_thm(PROV_PRST_SUBST))
    print("    PROV_PRST_REFL              :", pp_thm(PROV_PRST_REFL))
    print("    PROV_PRST_ADJ_DEF_AT     :", pp_thm(PROV_PRST_ADJ_DEF_AT))
    print()
    print("Stage 2B (d.3) -- mu-correctness axiom.")
    print("    MU_CORRECTNESS              :", pp_thm(MU_CORRECTNESS))
    print("    FIND_PROOF_PR_MU_CORRECT   :", pp_thm(FIND_PROOF_PR_MU_CORRECT))
    print()
    print("Stage 2B (d.4) -- Proof_PRST_pr correctness.")
    print("    PROOF_PRST_PR_BODY_CORRECT  :", pp_thm(PROOF_PRST_PR_BODY_CORRECT))
    print("    PRST_INTERNALIZES_TRUE_PR_EVAL :", pp_thm(PRST_INTERNALIZES_TRUE_PR_EVAL))
    print("    PRST_INTERNALIZES_FALSE_PR_EVAL :", pp_thm(PRST_INTERNALIZES_FALSE_PR_EVAL))
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
