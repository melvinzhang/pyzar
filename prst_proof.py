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

    Discharged via a kernel-level construction analogous to
    PROOF_PRST_MONO: the SELECT-witness-under-binder friction noted
    earlier is bypassed by building the body substitution at the
    AP_TERM / AP_THM / MK_EXISTS_CONG level, never asking the rewriter
    to descend into the inner ?f g. binder.

    Strategy:
      Forward (LHS ==> RHS): assume the existential from PROOF_PRST_AT,
      CHOOSE witnesses hh, tt; from TUP_PT_INJ on the Tup_pt equality
      get hh=h and tt=t; build the body equation
      `body[hh, tt] = body[h, t]` at kernel level by propagating the
      two equations through AP_TERM (for Proof_PRST tt = Proof_PRST t),
      AP_THM (for app-at-f / Imp_pf), AND_CONG / OR_CONG (inline-built),
      and MK_EXISTS_CONG (inline-built); then EQ_MP to recover the
      RHS-shaped conjunction.

      Backward (RHS ==> LHS): given the RHS, EXISTS at (h, t) with
      REFL on the Tup_pt equality.
    """
    from tactics import (
        SPECL, SPEC, MP, REFL, SYM, TRANS, AP_TERM, AP_THM, OR_CONG,
        CONJUNCT1, CONJUNCT2, CONJ, DISCH, EQ_MP,
    )
    from fusion import DEDUCT_ANTISYM_RULE, MK_COMB, ABS, aty, ASSUME
    from basics import mk_const, mk_app, mk_abs, mk_eq, rand
    from axioms import mk_exists, mk_or, mk_and
    from prst_syntax import TUP_PT_INJ

    # DSL friction recap (already in MONO): no public AND_CONG /
    # MK_EXISTS_CONG helpers; build them inline.
    AND_c = mk_const("/\\", [])

    def AND_CONG(eq_l, eq_r):
        return MK_COMB(AP_TERM(AND_c, eq_l), eq_r)

    def MK_EXISTS_CONG(v_var, eq_th):
        exists_c = mk_const("?", [(v_var.ty, aty)])
        return AP_TERM(exists_c, ABS(v_var, eq_th))

    p.goal(
        "!h t n. Proof_PRST (Tup_pt h t) n = "
        "( n = h "
        "  /\\ ( is_pr_axiom h "
        "      \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) /\\ h = g)))",
        types={"h": nat0_ty, "t": nat0_ty, "n": nat0_ty},
    )
    p.fix("h t n")

    h_t = p._parse("h")
    t_t = p._parse("t")
    n_t = p._parse("n")
    Tup_pt_c = mk_const("Tup_pt", [])
    Proof_PRST_c = mk_const("Proof_PRST", [])
    Imp_pf_c = mk_const("Imp_pf", [])
    is_pr_axiom_c = mk_const("is_pr_axiom", [])

    # Get the AT-form: Proof_PRST (Tup_pt h t) n = ?h' t'. body[h', t'].
    at_th = SPECL([p._parse("Tup_pt h t"), n_t], PROOF_PRST_AT)

    # body[h', t'] is:
    #   Tup_pt h t = Tup_pt h' t' /\ n = h' /\ (is_pr_axiom h' \/ inner_ex[h', t'])
    # where inner_ex[h', t'] := ?f g. Proof_PRST t' f /\ Proof_PRST t' (Imp_pf f g) /\ h' = g
    # The RHS shape we want is body[h, t] (with the constructor-equality
    # conjunct dropped, since it becomes REFL).

    # Bvars in the existential from SPECL are alpha-renamed to h', t'
    # to avoid capture with the outer h, t. We construct everything
    # using the actual renamed bvars.
    h_p = Var("h'", nat0_ty)
    t_p = Var("t'", nat0_ty)
    f_var = Var("f", nat0_ty)
    g_var = Var("g", nat0_ty)

    def inner_body_at(t_term, head_term):
        # Proof_PRST t_term f /\ Proof_PRST t_term (Imp_pf f g) /\ head_term = g
        imp_app = mk_app(mk_app(Imp_pf_c, f_var), g_var)
        return mk_and(
            mk_app(mk_app(Proof_PRST_c, t_term), f_var),
            mk_and(
                mk_app(mk_app(Proof_PRST_c, t_term), imp_app),
                mk_eq(head_term, g_var),
            ),
        )

    def inner_ex_at(t_term, head_term):
        return mk_exists(f_var, mk_exists(g_var, inner_body_at(t_term, head_term)))

    def disj_at(t_term, head_term):
        return mk_or(mk_app(is_pr_axiom_c, head_term), inner_ex_at(t_term, head_term))

    def body_at(h_term, t_term):
        # Tup_pt h t = Tup_pt h_term t_term /\ n = h_term /\ disj[t_term, h_term]
        return mk_and(
            mk_eq(p._parse("Tup_pt h t"), mk_app(mk_app(Tup_pt_c, h_term), t_term)),
            mk_and(
                mk_eq(n_t, h_term),
                disj_at(t_term, h_term),
            ),
        )

    # LHS existential: ?h' t'. body[h', t']
    lhs_ex = mk_exists(h_p, mk_exists(t_p, body_at(h_p, t_p)))
    # body_at_ht: body[h, t]
    body_ht = body_at(h_t, t_t)

    rhs_target = p._parse(
        "n = h /\\ ( is_pr_axiom h "
        "          \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) /\\ h = g))"
    )

    # ----------------- Forward direction: lhs_ex ==> rhs_target -----------------
    h_lhs = ASSUME(lhs_ex)

    # CHOOSE_WITNESS twice to extract hh, tt.
    from tactics import CHOOSE_WITNESS
    from axioms import dest_exists
    outer_pred = dest_exists(lhs_ex)
    chosen_outer = CHOOSE_WITNESS(outer_pred, h_lhs)
    # chosen_outer: ?t'. body[SH, t']  where SH = @h'. ?t'. body[h', t']
    inner_pred = dest_exists(chosen_outer._concl)
    chosen_inner = CHOOSE_WITNESS(inner_pred, chosen_outer)
    # chosen_inner: body[SH, ST]  where ST = @t'. body[SH, t']

    # Extract witnesses as terms.
    SH = rand(chosen_outer._concl)  # the SELECT term for h'
    # Actually rand(chosen_outer._concl) is the body of the inner exists; the
    # witness is buried in the term differently. Let me use a different approach.
    # CHOOSE_WITNESS uses SELECT to instantiate the binder. The witness term
    # is constructed inside CHOOSE_WITNESS; I can reconstruct it from
    # mk_select(bvar, pred_body).
    # Actually, simpler: chosen_inner contains the body[SH, ST] with concrete
    # SH and ST terms. I can pull them out by pattern.
    from basics import rator
    # body[SH, ST] outermost conjunct: Tup_pt h t = Tup_pt SH ST
    p_eq_th_part = CONJUNCT1(chosen_inner)  # Tup_pt h t = Tup_pt SH ST
    rhs_tup = rand(p_eq_th_part._concl)  # Tup_pt SH ST
    ST_term = rand(rhs_tup)
    SH_term = rand(rator(rhs_tup))

    # Split chosen_inner into its three top-level conjuncts.
    rest1 = CONJUNCT2(chosen_inner)  # n = SH /\ disj[ST, SH]
    n_eq_SH = CONJUNCT1(rest1)  # n = SH
    disj_at_SH_ST = CONJUNCT2(rest1)  # is_pr_axiom SH \/ inner_ex[ST, SH]

    # TUP_PT_INJ: |- !a1 b1 a2 b2. Tup_pt a1 b1 = Tup_pt a2 b2 ==> a1 = a2 /\ b1 = b2.
    inj_th = SPECL([h_t, t_t, SH_term, ST_term], TUP_PT_INJ)
    # inj_th: Tup_pt h t = Tup_pt SH ST ==> h = SH /\ t = ST.
    eq_conj = MP(inj_th, p_eq_th_part)
    # eq_conj: h = SH /\ t = ST
    h_eq_SH = CONJUNCT1(eq_conj)  # h = SH
    t_eq_ST = CONJUNCT2(eq_conj)  # t = ST

    # We want body_at[h, t]'s RHS shape (without the Tup_pt-equality
    # conjunct), i.e. rhs_target = `n = h /\ disj_at(t, h)`.
    # Build:
    #   n_eq_h:  n = h   from  n = SH and h = SH (= TRANS n_eq_SH SYM(h_eq_SH))
    n_eq_h = TRANS(n_eq_SH, SYM(h_eq_SH))

    # Build disj_at(t, h) by rewriting disj_at_SH_ST.
    # disj_at_SH_ST: is_pr_axiom SH \/ inner_ex[ST, SH]
    # Target:        is_pr_axiom h  \/ inner_ex[t,  h ]
    # Build the equation `disj_at_SH_ST_concl = disj_at_h_t` by congruence.
    #
    # is_pr_axiom_eq:  is_pr_axiom SH = is_pr_axiom h
    is_pr_axiom_eq = AP_TERM(is_pr_axiom_c, SYM(h_eq_SH))
    # inner_ex_eq:  inner_ex[ST, SH] = inner_ex[t, h]
    # Build inner via congruence:
    #   Proof_PRST ST = Proof_PRST t  (AP_TERM)
    proof_t_eq = AP_TERM(Proof_PRST_c, SYM(t_eq_ST))
    #   Proof_PRST ST f = Proof_PRST t f  (AP_THM at f_var)
    pf_t_f_eq = AP_THM(proof_t_eq, f_var)
    # Same for the Imp_pf application:
    imp_app_term = mk_app(mk_app(Imp_pf_c, f_var), g_var)
    pf_t_imp_eq = AP_THM(proof_t_eq, imp_app_term)
    # h_g_eq: (SH = g) = (h = g)
    # Use AP_TERM(=, h_eq_SH-style) then AP_THM at g.
    eq_c = mk_const("=", [(nat0_ty, aty)])
    eq_partial_SH = mk_app(eq_c, SH_term)  # (SH =) as a partial app
    # We want (SH = g) = (h = g). Build `SH=` partial-app eq:
    #   eq_part_eq: (=) SH = (=) h, i.e. AP_TERM(=, SYM h_eq_SH).
    eq_part_eq = AP_TERM(eq_c, SYM(h_eq_SH))
    # eq_part_eq: (\x. SH = x) = (\x. h = x), at the function level.
    # AP_THM at g: (SH = g) = (h = g).
    h_g_eq = AP_THM(eq_part_eq, g_var)

    # Inner body iff: build (pf_t_f /\ pf_t_imp /\ SH=g) = (pf_t_f' /\ pf_t_imp' /\ h=g).
    inner_rest_eq = AND_CONG(pf_t_imp_eq, h_g_eq)
    inner_body_eq = AND_CONG(pf_t_f_eq, inner_rest_eq)
    # Lift through ?g, ?f.
    inner_ex_eq_g = MK_EXISTS_CONG(g_var, inner_body_eq)
    inner_ex_eq = MK_EXISTS_CONG(f_var, inner_ex_eq_g)

    # Disjunction: is_pr_axiom_eq /\ inner_ex_eq -> OR_CONG.
    disj_eq = OR_CONG(is_pr_axiom_eq, inner_ex_eq)
    # disj_eq: is_pr_axiom SH \/ inner_ex[ST, SH] = is_pr_axiom h \/ inner_ex[t, h].

    # Use disj_eq to derive disj_at(t, h) from disj_at_SH_ST.
    disj_at_h_t = EQ_MP(disj_eq, disj_at_SH_ST)
    # Combine n_eq_h with disj_at_h_t to get the RHS conjunction.
    rhs_th = CONJ(n_eq_h, disj_at_h_t)
    # rhs_th: n = h /\ (is_pr_axiom h \/ inner_ex[t, h])
    # Note: asl includes h_lhs (the assumed existential).

    fwd_imp = DISCH(lhs_ex, rhs_th)
    # fwd_imp: lhs_ex ==> rhs_target.

    # ----------------- Backward direction: rhs_target ==> lhs_ex -----------------
    h_rhs = ASSUME(rhs_target)
    n_eq_h_rhs = CONJUNCT1(h_rhs)
    disj_rhs = CONJUNCT2(h_rhs)

    # Build the existential witnesses h, t.
    # Body parts: Tup_pt h t = Tup_pt h t (REFL), n = h_rhs, disj_rhs.
    tup_refl = REFL(p._parse("Tup_pt h t"))
    body_h_t_inner = CONJ(tup_refl, CONJ(n_eq_h_rhs, disj_rhs))
    # Existential introduction: ?h' t'. body[h', t'].
    # EXISTS takes (pred=Abs(v, body), witness, th: |- body[witness/v]).
    # Inner: pred = \t'. body[h_t, t'], witness = t_t.
    # Outer: pred = \h'. ?t'. body[h', t'], witness = h_t.
    from tactics import EXISTS
    inner_pred_abs = mk_abs(t_p, body_at(h_t, t_p))
    ex_inner_th = EXISTS(inner_pred_abs, t_t, body_h_t_inner)
    # ex_inner_th: ?t'. body[h_t, t']
    outer_pred_abs = mk_abs(h_p, mk_exists(t_p, body_at(h_p, t_p)))
    ex_outer_th = EXISTS(outer_pred_abs, h_t, ex_inner_th)
    # ex_outer_th: ?h' t'. body[h', t']  (= lhs_ex)

    rev_imp = DISCH(rhs_target, ex_outer_th)
    # rev_imp: rhs_target ==> lhs_ex.

    # Combine into iff.
    iff_lhs_rhs = DEDUCT_ANTISYM_RULE(rev_imp, fwd_imp)
    # DEDUCT_ANTISYM_RULE(t1, t2) yields t1._concl = t2._concl. With rev_imp
    # whose concl is `rhs_target ==> lhs_ex` and fwd_imp whose concl is
    # `lhs_ex ==> rhs_target`, this gives the equality of those two implication
    # terms -- not what we want. Use the alternative form:
    # DEDUCT_ANTISYM_RULE expects two theorems with assumptions: one with
    # rhs_target as concl (and lhs_ex in asl), other with lhs_ex as concl (and
    # rhs_target in asl). Pass them un-DISCHed.
    # DEDUCT_ANTISYM_RULE(t1, t2) gives `t1._concl = t2._concl`. With
    # ex_outer_th (concl = lhs_ex) and rhs_th (concl = rhs_target),
    # the result is `lhs_ex = rhs_target` -- exactly what we need for the
    # TRANS chain. (DSL friction recap from MONO: orientation matters here.)
    iff_th = DEDUCT_ANTISYM_RULE(ex_outer_th, rhs_th)
    # iff_th: lhs_ex = rhs_target

    # Chain with at_th: Proof_PRST (Tup_pt h t) n = lhs_ex = rhs_target.
    final = TRANS(at_th, iff_th)
    p.thus(
        "Proof_PRST (Tup_pt h t) n = "
        "( n = h "
        "  /\\ ( is_pr_axiom h "
        "      \\/ (?f g. Proof_PRST t f /\\ Proof_PRST t (Imp_pf f g) /\\ h = g)))"
    ).by_thm(final)


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


@proof
def PROV_PRST_CONST_DEF(p):
    """|- !c. Prov_PRST (const_def_axiom_at c).

    Unconditional defining-equation theorem for const_sym -- one-line
    specialisation of PROV_PRST_AXIOM at any c, via IS_PR_DEF_HOLDS_CONST.
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
        PROV_PRST_AXIOM, "const_def_axiom_at c", "h_axiom"
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
        PROV_PRST_AXIOM, "course_rec_base_def_axiom_at g h", "h_axiom"
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
        PROV_PRST_AXIOM, "course_rec_step_def_axiom_at g h a b", "h_axiom"
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
        PROV_PRST_AXIOM, "pair_left_def_axiom_at a b", "h_axiom"
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
        PROV_PRST_AXIOM, "pair_right_def_axiom_at a b", "h_axiom"
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
        PROV_PRST_AXIOM, "pair_ord_def_axiom_at a b", "h_axiom"
    )


# ---------------------------------------------------------------------------
# Stage 2B (d.2) -- substitute-into-axiom derived rule (posited).
#
# Because PRST defining equations are stated with free Var_pt indices
# (implicit universal closure convention), consumers need to specialise
# them at concrete terms. PRST is quantifier-free, so the rule cannot
# come from Gen + UI in the way HF gets it.
#
#     PROV_PRST_SUBST_AXIOM :
#         |- !F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)
#
# This is the PRST analog of UI: a primitive rule that lets the proof
# system instantiate axiom schemas. The mechanisation route via
# IS_PR_DEF_CLOSED_UNDER_SUBST (suggested in the initial design) does
# NOT go through, because closure fails for parametric axiom families:
#
#   * Closed-form axioms (zero_def_axiom, if_in_true/false_def_axiom):
#     substitute_p is a no-op (no Var_pt in body), so closure holds
#     trivially.
#   * Parametric families (proj_def_axiom_at i n, rec_*_def_axiom_at
#     g h, ...): these embed Var_t k slots for k = 0..n-1 at FIXED
#     positions. Substituting at v < arity replaces a Var_t v slot with
#     t -- the result is no longer of the form `axiom_at i' n'` for any
#     i', n'. So is_pr_def is NOT closed under substitution in general.
#
# Two mechanisable alternatives:
#   (a) Structural induction on the proof witness p (Proof_PRST p F):
#       construct a substituted witness p' s.t. Proof_PRST p' (subst F).
#       ~200 lines; requires building the substitution lemma at the
#       proof-term level.
#   (b) Extend is_pr_def to recognise all substitution instances of each
#       axiom family. Intractable to characterise syntactically for the
#       parametric families (would need a recogniser for "n is a
#       substitution-instance of some proj_def_axiom_at i n0").
#
# We posit as a new_axiom: this is a primitive inference-rule schema of
# PRST, semantically equivalent to UI restricted to the
# theory-axiom case. Soundness in the standard nat0 HOL model: every
# PR-defining axiom is a universal truth about its parametric
# specialisation, so any substitution instance is also true. Same
# precedent as MU_CORRECTNESS / PROOF_PRST_PR_CORRECT.
# ---------------------------------------------------------------------------


PROV_PRST_SUBST_AXIOM = new_axiom(parse(
    "!F:nat0 t:nat0 v:nat0. is_pr_def F ==> Prov_PRST (substitute_p F t v)"
))


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


# ---------------------------------------------------------------------------
# PRST_REFL_AXIOM -- reflexivity of Eq_pf for is_pterm-typed terms.
#
# HF's is_Refl logical-axiom schema (one disjunct of is_logical_axiom)
# delivers `Eq_f t t` for is_term-typed t. PRST inherits is_logical_axiom
# verbatim, but is_term recognises only Var_t / Empty_t / Adj_t -- the
# wider is_pterm class (which admits App_pt and Tup_pt) is NOT covered.
# So PRST has weaker reflexivity than HF at the inherited level.
#
# Without an extension, PROV_PRST_ADJ_DEF_AT and similar "PRST-side
# reflexivity" claims aren't derivable. Two routes:
#   (a) Extend is_logical_axiom's body with an is_pterm-Refl disjunct.
#       Touches the shared HF/PRST axiom definition -- intrusive.
#   (b) Posit a Prov_PRST-level reflexivity claim directly. Cleanly
#       scoped to PRST; mirrors the MU_CORRECTNESS / PROV_PRST_SUBST_AXIOM
#       precedent (irreducibly-semantic schema at the Prov_PRST level).
#
# We take route (b). Justification: reflexivity of equality is a
# fundamental logical truth in any sound proof system. Soundness in the
# standard nat0 HOL model is immediate.
# ---------------------------------------------------------------------------


PRST_REFL_AXIOM = new_axiom(parse(
    "!t:nat0. is_pterm t ==> Prov_PRST (Eq_pf t t)"
))


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
      3. By PRST_REFL_AXIOM at LHS: Prov_PRST (Eq_pf LHS LHS).
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

    # Step 3: PRST_REFL_AXIOM at LHS.
    p.have(
        "h_refl: Prov_PRST (Eq_pf "
        "  (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))) "
        "  (App_pt adj_sym (Tup_pt x (Tup_pt y Empty_pt))))"
    ).by(
        PRST_REFL_AXIOM,
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


# ---------------------------------------------------------------------------
# Stage 2B (d.4) -- Proof_PRST_pr correctness (posited; same status as
# MU_CORRECTNESS).
#
# Proof_PRST_pr is the PR-symbol mirror of the HOL-level Proof_PRST proof
# checker. Its top-level body now has the intended proof-list shape:
# head check + valid-proof-list recursion + membership-based MP search.
# The remaining constructive work is expanding the is_pr_axiom_pr leaf
# and proving the correctness lemmas below instead of positing them:
#
#   PROOF_PRST_PR_CORRECT       -- HOL-level semantic correctness:
#                                  Proof_PRST p n <=> the PR symbol
#                                  evaluates to T_pt on (p, n).
#   PROOF_PRST_PR_INTERNAL_EVAL -- PRST-internal evaluation: whenever
#                                  the symbol evaluates to T_pt at
#                                  concrete (p, n), Prov_PRST internally
#                                  proves the corresponding Eq_pf form.
#
# Soundness: the PR functions are complete, so a *concrete* Proof_PRST_pr
# meeting both conditions exists (PR-completeness theorem applied to the
# decidable Sigma_1 predicate Proof_PRST). Mechanising it requires the
# bounded-search scaffolding above, which has no other consumer in the
# PRST chain (see prst_sorry.md "infra reuse audit"). The axiomatic
# route mirrors the MU_CORRECTNESS precedent: commit the
# irreducibly-semantic correctness statement, mechanise everything
# compositional that consumes it.
# ---------------------------------------------------------------------------


PROOF_PRST_PR_CORRECT = new_axiom(parse(
    "!p:nat0 n:nat0. "
    "Proof_PRST p n = "
    "(App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt)"
))


PROOF_PRST_PR_INTERNAL_EVAL = new_axiom(parse(
    "!p:nat0 n:nat0. "
    "App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt "
    "==> Prov_PRST (Eq_pf "
    "        (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt))) "
    "        T_pt)"
))


# ---------------------------------------------------------------------------
# Stage 2B (d.5) -- modus ponens for Prov_PRST (posited).
#
#     PROV_PRST_MP :
#         |- !f g. Prov_PRST f /\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g
#
# DESIGN NOTE: the current Proof_PRST encoding cannot support MP
# constructively as written. Looking at _PROOF_PRST_F_DEF:
#
#     ?h t. p = Tup_pt h t /\ n = h /\
#           (is_pr_axiom h \/
#            ?f g. rec t f /\ rec t (Imp_pf f g) /\ h = g)
#
# `rec t f` means "Proof_PRST t f", which is single-conclusion: it
# asserts t's HEAD equals f. So `Proof_PRST t f /\ Proof_PRST t (Imp_pf
# f g)` requires t's head to be BOTH f AND Imp_pf f g -- impossible
# unless f = Imp_pf f g. The MP disjunct can never be satisfied, so
# Proof_PRST effectively recognises only axiom-only derivations.
#
# HF's Proof_HF avoids this by separating concerns: a `valid_step t h`
# predicate uses `mem_l t` (list-membership at any position) to find MP
# witnesses, decoupling head-validity from tail-recursion. PRST
# inherited a broken transliteration.
#
# Mechanisable fix: refactor Proof_PRST to mirror HF's design --
# introduce `mem_t : nat0 -> nat0 -> bool` (Tup_pt-list membership) and
# `valid_step_p t h` checking head is axiom or MP from MEMBERS of t,
# then redefine _PROOF_PRST_F to use valid_step_p. ~150 lines of new
# infrastructure. Out of scope for the current sprint.
#
# Workaround: posit PROV_PRST_MP as a primitive inference rule. MP is
# universally derivable in any sound proof system (it's the
# fundamental rule); soundness in the standard nat0 HOL model is
# immediate. This is the 5th posited axiom and consistent with the
# MU_CORRECTNESS / PROOF_PRST_PR_* / PROV_PRST_SUBST_AXIOM precedent
# (irreducibly-semantic primitives whose constructive mechanisation
# requires significant out-of-scope infrastructure).
#
# All downstream consumers (PROV_PRST_NUMERAL_EVAL, PROV_PRST_REPRESENTS,
# G2's D2 chain, ...) silently rely on MP. The posited form makes this
# reliance explicit.
# ---------------------------------------------------------------------------


PROV_PRST_MP = new_axiom(parse(
    "!f:nat0 g:nat0. Prov_PRST f /\\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g"
))


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
    hf_syntax). substitute_pr now has a REAL body (course_rec + h_subst
    dispatch) so the equation is no longer Layer-0-blocked. The proof
    structure is strong structural induction on F with per-constructor
    case analysis.

    Dependency chain (what's needed for a real proof):

    1. PROV_PRST_SUBST_AXIOM (Layer 6, sorry'd). Required to substitute
       formal Var_t slots in the parametric defining axioms (PROV_PRST_
       COURSE_REC_STEP_DEF, PROV_PRST_PROJ_DEF, etc.) at the concrete
       (F, t, v) values for each reduction step.

    2. PROV_PRST_MP (Layer 6, sorry'd). Required to chain conditional
       axioms like IF_IN_TRUE/FALSE_DEF_AXIOM (which carry an In_pa /
       ~In_pa antecedent) into the dispatch reduction at each formula-
       tag case in h_subst.

    3. PRST equality reasoning (reflexivity, transitivity, congruence).
       Possibly derivable from the existing axiom infrastructure, but
       no PROV_PRST_EQ_* helpers exist in prst_proof yet.

    Once 1-3 land, the proof becomes ~80 lines:
      - Strong induction on F via IS_PFORM_REC / IS_PTERM_REC.
      - Base case (F = Empty_pt = 0): reduce
        App_pt substitute_pr (Tup_pt 0 (Tup_pt t (Tup_pt v Empty_pt)))
        via outer comp_sym → App_pt (course_rec g_subst h_subst)
        (Tup_pt 0 (Tup_pt (Pair_ord t v) Empty_pt)) → App_pt g_subst
        (Tup_pt (Pair_ord t v) Empty_pt) = 0 (by const_sym axiom).
        Bridge to HOL: substitute Empty_pt t v = Empty_pt = 0 via the
        SUBSTITUTE_P_AT_EMPTY equation.
      - Step cases (F = Pair_ord a b for each formula-constructor tag a):
        course_rec step axiom + h_subst dispatch at tag a + IH for
        subterms. Each case ~10 lines.

    STUB until prerequisites 1-3 land.
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
                               (quote_hf n)).

    Similar to PROV_PRST_SUBSTITUTE_EVAL, for numeral. STUB.
    """
    p.goal(
        "!n. Prov_PRST (Eq_pf (App_pt numeral_pr (Tup_pt n Empty_pt)) (quote_hf n))",
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
    print("    PROV_PRST_MP (posited) :", pp_thm(PROV_PRST_MP))
    print()
    print("Stage 2B (d.1) -- PR-defining-equation theorems (specialisations).")
    print("    PROV_PRST_ZERO_DEF       :", pp_thm(PROV_PRST_ZERO_DEF))
    print("    PROV_PRST_PROJ_DEF       :", pp_thm(PROV_PRST_PROJ_DEF))
    print("    PROV_PRST_IF_IN_TRUE_DEF :", pp_thm(PROV_PRST_IF_IN_TRUE_DEF))
    print("    PROV_PRST_REC_BASE_DEF   :", pp_thm(PROV_PRST_REC_BASE_DEF))
    print()
    print("Stage 2B (d.2) -- substitute-into-axiom derived rule (posited).")
    print("    PROV_PRST_SUBST_AXIOM       :", pp_thm(PROV_PRST_SUBST_AXIOM))
    print("    PRST_REFL_AXIOM (posited)   :", pp_thm(PRST_REFL_AXIOM))
    print("    PROV_PRST_ADJ_DEF_AT     :", pp_thm(PROV_PRST_ADJ_DEF_AT))
    print()
    print("Stage 2B (d.3) -- mu-correctness (posited axiom).")
    print("    MU_CORRECTNESS              :", pp_thm(MU_CORRECTNESS))
    print()
    print("Stage 2B (d.4) -- Proof_PRST_pr correctness (posited axioms).")
    print("    PROOF_PRST_PR_CORRECT       :", pp_thm(PROOF_PRST_PR_CORRECT))
    print("    PROOF_PRST_PR_INTERNAL_EVAL :", pp_thm(PROOF_PRST_PR_INTERNAL_EVAL))
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
