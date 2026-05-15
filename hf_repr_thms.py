# ---------------------------------------------------------------------------
# Stage 3 high-layer -- representability proofs that need the Prov_HF
# logical toolkit from ``hf_logic`` (PROV_HF_UI, PROV_HF_AND_ELIM_*,
# PROV_HF_CONTRAP, PROV_HF_DOUBLE_NEG_*, PROV_HF_TRANS_IMP).
#
# This module sits *above* ``hf_logic`` in the dependency tree. The
# split is dictated by the cycle: ``hf_repr`` declares the Prov_HF
# axiom and MP rule; ``hf_logic`` builds the universal-instantiation
# and propositional toolkit on top of those; the IS_*_REPRESENTS
# proofs need both, so they have to live downstream of hf_logic. Doing
# the split this way (rather than monkey-patching ``hf_repr``) means
# every IS_*_REPRESENTS lives in one place and importers see a single
# canonical name.
#
# Contents:
#   (a) HF1_INST / HF2_INST / HF3_INST -- closed HF1-3 axioms
#       instantiated at concrete HF-syntax terms, via PROV_HF_UI plus
#       the substitute reduction lemmas.
#   (b) QUOTE_HF_INJ -- HOL-level injectivity for the quote_hf map.
#   (c) Measured quote membership / inequality scaffolding.
#   (d) Stage-3 remaining SORRY scaffolding
#       (PROV_HF_REPRESENTS). Substitute representability is now provided
#       by the syntax-recursion package in hf_repr_core.
# ---------------------------------------------------------------------------


from fusion import Comb, Const, Var
from basics import dest_eq, mk_app, mk_const, mk_eq
from nat0 import nat0_ty, ZERO, mk_suc0
from parser import parse_type
from proof import proof, define_with_at
from tactics import (
    SPEC,
    SPECL,
    AP_TERM,
    MP,
    SYM,
    REFL,
    EQ_MP,
    TRANS,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    DISJ1,
    NOT_ELIM,
    CONTR,
    EQF_ELIM,
    EQF_INTRO,
    EQT_INTRO,
    EQT_ELIM,
)

from hf_proof import (
    HF1_axiom,
    HF2_axiom,
    HF3_axiom,
    HF4_axiom,
    HF1_AXIOM_DEF,
    HF2_AXIOM_DEF,
    HF3_AXIOM_DEF,
    HF4_AXIOM_DEF,
    IS_HF_AXIOM_HOLDS,
    is_hf_ind_axiom,
    is_logical_axiom,
    IS_AXIOM_AT,
    var_x,
    var_y,
    var_z,
    VAR_X_DEF,
    VAR_Y_DEF,
    VAR_Z_DEF,
)
from hf_syntax import (
    Empty_t,
    EMPTY_T_DEF,
    SUBSTITUTE_AT_NOT,
    SUBSTITUTE_AT_IN,
    SUBSTITUTE_AT_EMPTY,
    SUBSTITUTE_AT_INSERT,
    SUBSTITUTE_AT_EQ,
    SUBSTITUTE_AT_IMP,
    SUBSTITUTE_AT_VAR_HIT,
    SUBSTITUTE_AT_VAR_MISS,
    SUBSTITUTE_AT_FORALL_MISS,
    IS_FORM_AT_NOT,
    IS_FORM_AT_IN,
    IS_FORM_AT_IMP,
    IS_FORM_AT_EQ,
    IS_FORM_AT_FORALL,
    IS_TERM_AT_VAR,
    SUBSTITUTE_PRESERVES_IS_FORM,
)
from hf_repr_core import (
    PROV_HF_AXIOM,
    IS_TERM_EMPTY,
    IS_TERM_INSERT,
    QUOTE_HF_AT_EMPTY,
    _QUOTE_HF_AT_NZ,
)
from hf_sets import (
    EMPTY_DEF,
    INSERT_AT,
    IN_AT,
    IN_LT,
    NOT_IN_EMPTY,
    IN_INSERT_DIFF,
)
from hf_sets import IN_EXT
from hf_syntax import INSERT_T_INJ, INSERT_T_NEQ_EMPTY
from bits import (
    BIT_ABOVE_FALSE,
    BIT_AT_SET_BIT_DIFF,
    BIT_AT_SET_BIT_OTHER_SELF_FALSE,
    BIT_AT_SET_BIT_SAME,
    BIT_CLEAR_LOW_LOW_BIT,
    BIT_LOW_BIT,
    BIT_SELF_FALSE,
    BITWISE_LT_BY_TOP_DIFF,
    COND_F_NAT0,
    COND_T_NAT0,
    INSERT_LOW_BIT_CLEAR_LOW,
    LOW_BIT_LT,
    CLEAR_LOW_LT,
    SET_BIT_PRESENT_ID,
    SET_BIT_COMMUTE_DIFF,
    SET_BIT_GT_NEW,
)
from classical import EXCLUDED_MIDDLE, NOT_FORALL_TO_EX_NOT
from hf_logic import (
    PROV_HF_UI,
    PROV_HF_SUBST_EQ,
    PROV_HF_HYP_DROP,
    PROV_HF_DT_MP,
    PROV_HF_CONTRAP,
    PROV_HF_DOUBLE_NEG_INTRO,
    PROV_HF_AND_ELIM_LEFT,
    PROV_HF_AND_ELIM_RIGHT,
)
from hf_repr_core import (
    IS_TERM_QUOTE_HF,
    SUBSTITUTE_QUOTE_HF,
    PROV_HF_MP,
    PROV_HF_REFL,
    HF_SUPPORT_PREDICATE_PACKAGE,
    IS_TERM_INTERNAL_REPRESENTS,
    NOT_IS_TERM_INTERNAL_REPRESENTS,
    IS_FORM_INTERNAL_REPRESENTS,
    NOT_IS_FORM_INTERNAL_REPRESENTS,
    FREE_IN_INTERNAL_REPRESENTS,
    NOT_FREE_IN_INTERNAL_REPRESENTS,
    HF_SUPPORT_EQUIV_PACKAGE,
    IS_TERM_INTERNAL_EQUIV,
    IS_FORM_INTERNAL_EQUIV,
    FREE_IN_INTERNAL_EQUIV,
    SUBSTITUTE_INTERNAL_EQUIV,
    SUBSTITUTE_INTERNAL_FUNCTIONAL,
    HF_PACKAGE_SIDE_CONDITION_PACKAGE,
    IS_FORM_IS_AXIOM_INTERNAL,
    FREE_IN_IS_AXIOM_INTERNAL,
    IS_TERM_QPARSE_PAIR_ORD,
    FREE_IN_QPARSE_PAIR_ORD,
    IS_TERM_QPARSE_IMP_F,
    FREE_IN_QPARSE_IMP_F,
    IS_TERM_QPARSE_FORALL_F,
    FREE_IN_QPARSE_FORALL_F,
    HF_PROV_FREE_CONDITION_PACKAGE,
    FREE_IN_PROV_HF_INTERNAL_BODY,
    IS_MP_INTERNAL_DEF,
    IS_GEN_INTERNAL_DEF,
    VALID_STEP_HF_SET_INTERNAL_DEF,
    PROOF_HF_SET_INTERNAL_DEF,
    PROV_HF_INTERNAL_DEF,
    Prov_HF_internal,
    HF_SYNTAX_REC_PACKAGE,
    SUBSTITUTE_REPRESENTS_SYNTACTIC,
    SUBSTITUTE_REPRESENTS_TERM,
    SUBSTITUTE_REPRESENTS_FORM,
    SUBSTITUTE_REPRESENTS,
    TEMPLATE_FILL_EMPTY,
    TEMPLATE_FILL_EQ,
    TEMPLATE_FILL_NOT,
    TEMPLATE_FILL_IMP,
    TEMPLATE_FILL_FORALL,
    TEMPLATE_FILL_HOLE_HIT,
    TEMPLATE_FILL_HOLE_MISS,
    TEMPLATE_FILL_INSERT,
    TEMPLATE_FILL_IN,
    TEMPLATE_FILL_QPARSE_VAR_T,
    TEMPLATE_FILL_REPRESENTS_TERM,
    TEMPLATE_FILL_REPRESENTS,
    TEMPLATE_FILL_PRESERVES_IS_FORM,
)
from nat0_order import NAT0_LT_ASYM, NAT0_LT_NOT_REFL, NAT0_LT_SUC0, NAT0_LT_TOTAL_NEQ, NAT0_LT_TRANS


_t_n0 = Var("t", nat0_ty)
_u_n0 = Var("u", nat0_ty)
_w_n0 = Var("w", nat0_ty)
_s_n0 = Var("s", nat0_ty)


# ---------------------------------------------------------------------------
# Helper: lift |- is_hf_axiom HF_axiom to |- Prov_HF HF_axiom.
# ---------------------------------------------------------------------------
def _prov_of_hf_axiom(axiom_const):
    """|- Prov_HF HF{n}_axiom from |- is_hf_axiom HF{n}_axiom.

    is_axiom = is_hf_axiom \\/ (is_hf_ind_axiom \\/ is_logical_axiom);
    lift through DISJ1 then PROV_HF_AXIOM.
    """
    name = axiom_const.name
    is_hf_th = IS_HF_AXIOM_HOLDS[name]  # |- is_hf_axiom HF{n}_axiom
    is_axiom_at = SPEC(axiom_const, IS_AXIOM_AT)
    ind_part = mk_app(is_hf_ind_axiom, axiom_const)
    log_part = mk_app(is_logical_axiom, axiom_const)
    ind_or_log_part = mk_app(mk_const("\\/", []), ind_part, log_part)
    is_axiom_th = EQ_MP(SYM(is_axiom_at), DISJ1(is_hf_th, ind_or_log_part))
    prov_at = SPEC(axiom_const, PROV_HF_AXIOM)
    return MP(prov_at, is_axiom_th)


# ---------------------------------------------------------------------------
# Helper: |- is_term var_x  (and var_y / var_z analogues).
#
# IS_TERM_AT_VAR: |- !v. is_term (Var_t v) = T.
# Specialize at 0 / SUC0 0 / SUC0 SUC0 0, fold the Var_t-encoding back to
# the named constant, then EQT_ELIM.
# ---------------------------------------------------------------------------
def _is_term_var(var_def, inner_idx):
    is_term_at = SPEC(inner_idx, IS_TERM_AT_VAR)  # |- is_term (Var_t k) = T
    is_term_var_t = EQT_ELIM(is_term_at)          # |- is_term (Var_t k)
    from tactics import REWRITE_RULE
    return REWRITE_RULE([SYM(var_def)], is_term_var_t)  # |- is_term var_x


IS_TERM_VAR_X = _is_term_var(VAR_X_DEF, ZERO)
IS_TERM_VAR_Y = _is_term_var(VAR_Y_DEF, mk_suc0(ZERO))
IS_TERM_VAR_Z = _is_term_var(VAR_Z_DEF, mk_suc0(mk_suc0(ZERO)))


# ---------------------------------------------------------------------------
# HF1_INST -- HF1 axiom instantiated at one concrete HF-term ``t``.
#
# HF1_axiom = Forall_f 0 (Not_f (In_a var_x Empty_t)).
# After PROV_HF_UI(0, Not_f (In_a var_x Empty_t), t), the body collapses
# to Not_f (In_a t Empty_t) via SUBSTITUTE_AT_NOT/IN/EMPTY plus the
# var-HIT lemma (substitute (Var_t 0) t 0 = t).
# ---------------------------------------------------------------------------


@proof
def HF1_INST(p):
    """|- !t. is_term t ==> Prov_HF (Not_f (In_a t Empty_t)).

    HF1.  !x. ~In x Empty, instantiated at ``t``.
    """
    p.goal(
        "!t. is_term t ==> Prov_HF (Not_f (In_a t Empty_t))",
        types={"t": nat0_ty},
    )
    p.fix("t")
    p.assume("ht: is_term t")

    # Step 1: |- Prov_HF HF1_axiom.
    prov_h1_raw = _prov_of_hf_axiom(HF1_axiom)
    # Step 2: rewrite using HF1_AXIOM_DEF.
    p.have(
        "h_prov_forall: Prov_HF (Forall_f 0 (Not_f (In_a var_x Empty_t)))"
    ).by_rewrite_of(prov_h1_raw, [HF1_AXIOM_DEF])

    # Step 3: is_form (Not_f (In_a var_x Empty_t)). DSL friction:
    # ``by_rewrite`` only works on equational goals; for plain
    # propositions we descend manually through IS_FORM_AT_IN /
    # IS_FORM_AT_NOT, lifted with EQ_MP(SYM ...).
    in_at = SPECL([var_x, p._parse("Empty_t")], IS_FORM_AT_IN)
    h_in_form = EQ_MP(
        SYM(in_at), CONJ(IS_TERM_VAR_X, IS_TERM_EMPTY)
    )  # |- is_form (In_a var_x Empty_t)
    not_at = SPEC(p._parse("In_a var_x Empty_t"), IS_FORM_AT_NOT)
    h_is_form_body = EQ_MP(SYM(not_at), h_in_form)
    p.have(
        "h_is_form_body: is_form (Not_f (In_a var_x Empty_t))"
    ).by_thm(h_is_form_body)

    # Step 4: PROV_HF_UI at (x=0, phi=Not_f (In_a var_x Empty_t), t=t).
    p.have(
        "h_after_ui: Prov_HF (substitute (Not_f (In_a var_x Empty_t)) t 0)"
    ).by(
        PROV_HF_UI, "0", "Not_f (In_a var_x Empty_t)", "t",
        CONJ(
            p.fact("h_is_form_body"),
            CONJ(p.fact("ht"), p.fact("h_prov_forall")),
        ),
    )

    # Step 5: collapse the substitute symbolically.
    # substitute (Not_f (In_a var_x Empty_t)) t 0
    # = Not_f (In_a (substitute var_x t 0) (substitute Empty_t t 0))
    # = Not_f (In_a t Empty_t)
    # via SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IN, SUBSTITUTE_AT_EMPTY,
    # VAR_X_DEF, SUBSTITUTE_AT_VAR_HIT specialized at (0, t, 0).
    subst_vx_t = MP(
        SPECL([ZERO, _t_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )  # |- substitute (Var_t 0) t 0 = t
    p.thus("Prov_HF (Not_f (In_a t Empty_t))").by_rewrite_of(
        "h_after_ui",
        [
            SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_IN,
            SUBSTITUTE_AT_EMPTY,
            VAR_X_DEF,
            subst_vx_t,
        ],
    )


# ---------------------------------------------------------------------------
# HF2_INST -- HF2 axiom instantiated at concrete (t, u).
#
# HF2_axiom = Forall_f 0 (Forall_f (SUC0 0) (In_a var_x (Insert_t var_x var_y))).
#
# DSL friction: PROV_HF_UI substitutes blindly, no capture-avoidance --
# the second UI step's outer ``substitute t u (SUC0 0)`` only collapses
# back to ``t`` when ``t`` is closed under ``Var_t (SUC0 0)``. We expose
# this as a precondition ``substitute t u (SUC0 0) = t``; downstream
# quote branch bridges discharge it via SUBSTITUTE_QUOTE_HF on
# ``t = quote_hf x`` (quote_hf images contain no Var_t leaves).
# ---------------------------------------------------------------------------


@proof
def HF2_INST(p):
    """|- !t u. is_term t /\\ is_term u /\\
                substitute t u (SUC0 0) = t
                ==> Prov_HF (In_a t (Insert_t t u)).

    HF2.  !x y. In x (Insert x y), instantiated at (t, u). The
    side condition ``substitute t u (SUC0 0) = t`` reflects the
    capture-blind UI substitution: after the inner UI replaces var_x
    with t, the outer UI substitutes u for index SUC0 0 throughout --
    including any var_y leaves in t. The precondition forces t to be
    untouched (vacuously true for closed Insert_t/Empty_t towers, e.g.
    quote_hf images).
    """
    p.goal(
        "!t u. is_term t /\\ is_term u /\\ "
        "(substitute t u (SUC0 0) = t) "
        "==> Prov_HF (In_a t (Insert_t t u))",
        types={"t": nat0_ty, "u": nat0_ty},
    )
    p.fix("t u")
    p.assume(
        "(ht, hu, h_stable): is_term t /\\ is_term u /\\ "
        "(substitute t u (SUC0 0) = t)"
    )

    prov_h2_raw = _prov_of_hf_axiom(HF2_axiom)
    p.have(
        "h_prov_forall: Prov_HF (Forall_f 0 (Forall_f (SUC0 0) "
        "(In_a var_x (Insert_t var_x var_y))))"
    ).by_rewrite_of(prov_h2_raw, [HF2_AXIOM_DEF])

    # is_form (In_a var_x (Insert_t var_x var_y)).
    in_at = SPECL(
        [var_x, p._parse("Insert_t var_x var_y")], IS_FORM_AT_IN
    )
    is_term_inner = MP(
        SPECL([var_x, var_y], IS_TERM_INSERT),
        CONJ(IS_TERM_VAR_X, IS_TERM_VAR_Y),
    )  # |- is_term (Insert_t var_x var_y)
    h_in_form = EQ_MP(SYM(in_at), CONJ(IS_TERM_VAR_X, is_term_inner))

    # is_form (Forall_f (SUC0 0) (In_a var_x (Insert_t var_x var_y))).
    fa_at_inner = SPECL(
        [
            mk_suc0(ZERO),
            p._parse("In_a var_x (Insert_t var_x var_y)"),
        ],
        IS_FORM_AT_FORALL,
    )  # |- is_form (Forall_f (SUC0 0) phi) = is_form phi
    h_is_form_phi1 = EQ_MP(SYM(fa_at_inner), h_in_form)
    p.have(
        "h_is_form_phi1: is_form (Forall_f (SUC0 0) "
        "(In_a var_x (Insert_t var_x var_y)))"
    ).by_thm(h_is_form_phi1)

    # First UI: substitute (Forall_f (SUC0 0) ...) t 0.
    p.have(
        "h_after_ui1: Prov_HF (substitute "
        "(Forall_f (SUC0 0) (In_a var_x (Insert_t var_x var_y))) "
        "t 0)"
    ).by(
        PROV_HF_UI, "0", "Forall_f (SUC0 0) (In_a var_x (Insert_t var_x var_y))",
        "t",
        CONJ(
            p.fact("h_is_form_phi1"),
            CONJ(p.fact("ht"), p.fact("h_prov_forall")),
        ),
    )

    # Reduce the substitute symbolically.
    # substitute (Forall_f (SUC0 0) phi) t 0:
    # cond ~(0 = SUC0 0), so SUBSTITUTE_AT_FORALL_MISS fires.
    # _SUBST_VX_AT_X-style: we need substitute (Var_t 0) t 0 = t and
    # substitute (Var_t (SUC0 0)) t 0 = Var_t (SUC0 0).
    subst_vx_t = MP(
        SPECL([ZERO, _t_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )  # |- substitute (Var_t 0) t 0 = t
    # ~(0 = SUC0 0): from AXIOM_3_0 via _flip_neq pattern.
    from nat0 import AXIOM_3_0
    neq_s0_0 = SPEC(ZERO, AXIOM_3_0)  # |- ~(SUC0 0 = 0)
    # Flip to ~(0 = SUC0 0).
    from fusion import ASSUME
    from tactics import NOT_INTRO, NOT_ELIM, DISCH
    asm_eq = ASSUME(mk_eq(ZERO, mk_suc0(ZERO)))
    contra = MP(NOT_ELIM(neq_s0_0), SYM(asm_eq))
    neq_0_s0 = NOT_INTRO(DISCH(mk_eq(ZERO, mk_suc0(ZERO)), contra))

    subst_vy_at_0 = MP(
        SPECL([mk_suc0(ZERO), _t_n0, ZERO], SUBSTITUTE_AT_VAR_MISS),
        neq_0_s0,
    )  # |- substitute (Var_t (SUC0 0)) t 0 = Var_t (SUC0 0)

    # SUBSTITUTE_AT_FORALL_MISS is conditional on ~(v = a); discharge
    # it once at our concrete (SUC0 0, body, t, 0) so the rewriter sees
    # an unconditional equation. DSL friction: the simp pass unfolds
    # ``var_x`` / ``var_y`` to ``Var_t 0`` / ``Var_t (SUC0 0)`` before
    # rewrite-matching, so we instantiate ``fa_miss_inst`` with the
    # already-unfolded body.
    body_unfolded = p._parse(
        "In_a (Var_t 0) (Insert_t (Var_t 0) (Var_t (SUC0 0)))"
    )
    fa_miss_inst = MP(
        SPECL(
            [mk_suc0(ZERO), body_unfolded, _t_n0, ZERO],
            SUBSTITUTE_AT_FORALL_MISS,
        ),
        neq_0_s0,
    )
    p.have(
        "h_after_ui1_reduced: Prov_HF (Forall_f (SUC0 0) "
        "(In_a t (Insert_t t (Var_t (SUC0 0)))))"
    ).by_rewrite_of(
        "h_after_ui1",
        [
            VAR_X_DEF, VAR_Y_DEF,
            fa_miss_inst, SUBSTITUTE_AT_IN,
            SUBSTITUTE_AT_INSERT,
            subst_vx_t, subst_vy_at_0,
        ],
    )

    # Second UI: substitute (In_a t (Insert_t t (Var_t (SUC0 0)))) u (SUC0 0).
    h_is_term_vy = EQT_ELIM(SPEC(mk_suc0(ZERO), IS_TERM_AT_VAR))
    h_is_term_insert_tvy = MP(
        SPECL([_t_n0, p._parse("Var_t (SUC0 0)")], IS_TERM_INSERT),
        CONJ(p.fact("ht"), h_is_term_vy),
    )
    in_at2 = SPECL(
        [_t_n0, p._parse("Insert_t t (Var_t (SUC0 0))")], IS_FORM_AT_IN
    )
    h_is_form_phi2 = EQ_MP(
        SYM(in_at2), CONJ(p.fact("ht"), h_is_term_insert_tvy)
    )
    p.have(
        "h_is_form_phi2: is_form (In_a t (Insert_t t (Var_t (SUC0 0))))"
    ).by_thm(h_is_form_phi2)

    p.have(
        "h_after_ui2: Prov_HF (substitute "
        "(In_a t (Insert_t t (Var_t (SUC0 0)))) u (SUC0 0))"
    ).by(
        PROV_HF_UI, "SUC0 0", "In_a t (Insert_t t (Var_t (SUC0 0)))", "u",
        CONJ(
            p.fact("h_is_form_phi2"),
            CONJ(p.fact("hu"), p.fact("h_after_ui1_reduced")),
        ),
    )

    # Reduce: substitute (In_a t (Insert_t t (Var_t (SUC0 0)))) u (SUC0 0)
    # = In_a (substitute t u (SUC0 0))
    #         (Insert_t (substitute t u (SUC0 0)) (substitute (Var_t (SUC0 0)) u (SUC0 0)))
    # = In_a t (Insert_t t u)        [h_stable + Var_t (SUC0 0) HIT]
    subst_vy_u = MP(
        SPECL([mk_suc0(ZERO), _u_n0, mk_suc0(ZERO)], SUBSTITUTE_AT_VAR_HIT),
        REFL(mk_suc0(ZERO)),
    )  # |- substitute (Var_t (SUC0 0)) u (SUC0 0) = u
    p.thus("Prov_HF (In_a t (Insert_t t u))").by_rewrite_of(
        "h_after_ui2",
        [
            SUBSTITUTE_AT_IN, SUBSTITUTE_AT_INSERT,
            subst_vy_u, "h_stable",
        ],
    )


# ---------------------------------------------------------------------------
# HF3_INST -- HF3 axiom instantiated at concrete (a, b, c).
#
# HF3_axiom (three Forall_f layers):
#   Forall_f 0 (Forall_f (SUC0 0) (Forall_f (SUC0 (SUC0 0))
#     (Imp_f (Not_f (Eq_f var_x var_y))
#        (Not_f (Imp_f
#           (Imp_f (In_a var_y (Insert_t var_x var_z)) (In_a var_y var_z))
#           (Not_f (Imp_f (In_a var_y var_z)
#                         (In_a var_y (Insert_t var_x var_z)))))))))
#
# Three UI steps. As with HF2_INST, the capture-blind substitution
# pollutes inner terms; we expose three substitute-stability preconds:
#   * substitute a b (SUC0 0) = a
#   * substitute a c (SUC0 (SUC0 0)) = a
#   * substitute b c (SUC0 (SUC0 0)) = b
# All three are vacuously true for quote_hf images via SUBSTITUTE_QUOTE_HF.
# ---------------------------------------------------------------------------


# A small helper bundling AXIOM_3_0 + flip into the assorted ``~(i = j)``
# inequalities at indices 0, SUC0 0, SUC0 (SUC0 0) -- replicated from
# hf_repr's _build_neq_s0_ss0 / _flip_neq logic, kept private here to
# avoid a circular-style dependency on hf_repr internals.
def _flip_neq_local(neq_th, lhs, rhs):
    from fusion import ASSUME
    from tactics import NOT_INTRO, NOT_ELIM, DISCH
    asm = ASSUME(mk_eq(rhs, lhs))
    a_eq_b = SYM(asm)
    contra = MP(NOT_ELIM(neq_th), a_eq_b)
    return NOT_INTRO(DISCH(mk_eq(rhs, lhs), contra))


from nat0 import AXIOM_3_0, AXIOM_4_0  # noqa: E402

_neq_s0_0 = SPEC(ZERO, AXIOM_3_0)              # |- ~(SUC0 0 = 0)
_neq_ss0_0 = SPEC(mk_suc0(ZERO), AXIOM_3_0)    # |- ~(SUC0 (SUC0 0) = 0)
_neq_0_s0 = _flip_neq_local(_neq_s0_0, mk_suc0(ZERO), ZERO)
_neq_0_ss0 = _flip_neq_local(
    _neq_ss0_0, mk_suc0(mk_suc0(ZERO)), ZERO
)


def _neq_s0_ss0_build():
    from fusion import ASSUME
    from tactics import NOT_INTRO, NOT_ELIM, DISCH
    inj = SPECL([ZERO, mk_suc0(ZERO)], AXIOM_4_0)
    asm = ASSUME(mk_eq(mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))))
    z_eq_s0 = MP(inj, asm)
    contra = MP(NOT_ELIM(_neq_0_s0), z_eq_s0)
    return NOT_INTRO(
        DISCH(mk_eq(mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))), contra)
    )


_neq_s0_ss0 = _neq_s0_ss0_build()
_neq_ss0_s0 = _flip_neq_local(
    _neq_s0_ss0, mk_suc0(ZERO), mk_suc0(mk_suc0(ZERO))
)


_a_n0 = Var("a", nat0_ty)
_b_n0 = Var("b", nat0_ty)
_c_n0 = Var("c", nat0_ty)

_idx0 = ZERO
_idx1 = mk_suc0(ZERO)
_idx2 = mk_suc0(mk_suc0(ZERO))


# Parser-syntax helpers: HF3's body has 9 var-leaf occurrences and
# parens nest 10 layers deep, easy to miscount manually.  We compose
# strings via these helpers so parens stay balanced.
_VS0 = "(Var_t 0)"
_VS1 = "(Var_t (SUC0 0))"
_VS2 = "(Var_t (SUC0 (SUC0 0)))"


def _body3_at(x, y, z):
    """The HF3 body B0 with var_x/y/z replaced by the parser-syntax
    strings ``x``, ``y``, ``z`` (each must be its own parser-bracketed
    term).
    """
    return (
        f"(Imp_f (Not_f (Eq_f {x} {y})) "
        f"(Not_f (Imp_f "
        f"(Imp_f (In_a {y} (Insert_t {x} {z})) (In_a {y} {z})) "
        f"(Not_f (Imp_f (In_a {y} {z}) "
        f"(In_a {y} (Insert_t {x} {z})))))))"
    )


def _subst_var_hit(idx, term):
    """|- substitute (Var_t idx) term idx = term."""
    return MP(SPECL([idx, term, idx], SUBSTITUTE_AT_VAR_HIT), REFL(idx))


def _subst_var_miss(idx_var, term, idx_subst, neq_th):
    """|- substitute (Var_t idx_var) term idx_subst = Var_t idx_var.

    Requires ``neq_th : ~(idx_subst = idx_var)``.
    """
    return MP(
        SPECL([idx_var, term, idx_subst], SUBSTITUTE_AT_VAR_MISS), neq_th
    )


def _subst_forall_miss(fa_idx, body, term, subst_idx, neq_th):
    """|- substitute (Forall_f fa_idx body) term subst_idx
            = Forall_f fa_idx (substitute body term subst_idx).

    Requires ``neq_th : ~(subst_idx = fa_idx)``.
    """
    return MP(
        SPECL(
            [fa_idx, body, term, subst_idx], SUBSTITUTE_AT_FORALL_MISS
        ),
        neq_th,
    )


# B0 = innermost HF3 body (with var_x/y/z folded). _B0_text returns the
# string form for parsing; the parser unfolds var_x/y/z to Var_t 0/1/2
# inside the proof simp pass.
def _B0_text():
    return (
        "Imp_f (Not_f (Eq_f var_x var_y)) "
        "(Not_f (Imp_f "
        "(Imp_f (In_a var_y (Insert_t var_x var_z)) (In_a var_y var_z)) "
        "(Not_f (Imp_f (In_a var_y var_z) "
        "              (In_a var_y (Insert_t var_x var_z))))))"
    )


def _B1_text():
    return "Forall_f (SUC0 (SUC0 0)) (" + _B0_text() + ")"


def _B2_text():
    return "Forall_f (SUC0 0) (" + _B1_text() + ")"


# Unfolded body forms (with Var_t 0/1/2 instead of var_x/y/z) -- needed
# to instantiate FORALL_MISS at the simp-normalised shape.
def _B0_unfolded(p):
    return p._parse(
        "Imp_f (Not_f (Eq_f (Var_t 0) (Var_t (SUC0 0)))) "
        "(Not_f (Imp_f "
        "(Imp_f (In_a (Var_t (SUC0 0)) "
        "             (Insert_t (Var_t 0) (Var_t (SUC0 (SUC0 0))))) "
        "       (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0))))) "
        "(Not_f (Imp_f (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
        "              (In_a (Var_t (SUC0 0)) "
        "                    (Insert_t (Var_t 0) "
        "                              (Var_t (SUC0 (SUC0 0))))))))) "
    )


def _B1_unfolded(p):
    return p._parse(
        "Forall_f (SUC0 (SUC0 0)) ("
        "Imp_f (Not_f (Eq_f (Var_t 0) (Var_t (SUC0 0)))) "
        "(Not_f (Imp_f "
        "(Imp_f (In_a (Var_t (SUC0 0)) "
        "             (Insert_t (Var_t 0) (Var_t (SUC0 (SUC0 0))))) "
        "       (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0))))) "
        "(Not_f (Imp_f (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
        "              (In_a (Var_t (SUC0 0)) "
        "                    (Insert_t (Var_t 0) "
        "                              (Var_t (SUC0 (SUC0 0)))))))))) "
    )


# Body shape after UI1 (var_x replaced with `a`).
def _B0_at_a(p):
    return p._parse(
        "Imp_f (Not_f (Eq_f a (Var_t (SUC0 0)))) "
        "(Not_f (Imp_f "
        "(Imp_f (In_a (Var_t (SUC0 0)) "
        "             (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
        "       (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0))))) "
        "(Not_f (Imp_f (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
        "              (In_a (Var_t (SUC0 0)) "
        "                    (Insert_t a (Var_t (SUC0 (SUC0 0))))))))) "
    )


@proof
def HF3_INST(p):
    """|- !a b c. is_term a /\\ is_term b /\\ is_term c
                /\\ (substitute a b (SUC0 0) = a)
                /\\ (substitute a c (SUC0 (SUC0 0)) = a)
                /\\ (substitute b c (SUC0 (SUC0 0)) = b)
                ==> Prov_HF (Imp_f (Not_f (Eq_f a b))
                              (Not_f (Imp_f
                                 (Imp_f (In_a b (Insert_t a c)) (In_a b c))
                                 (Not_f (Imp_f (In_a b c)
                                              (In_a b (Insert_t a c))))))).

    HF3.  !x y z. ~(x = y) -> (In y (Insert x z) <-> In y z), instantiated
    at (a, b, c). Encoded biconditional spells out as
        Imp_f (Not_f (Eq_f a b))
              (Not_f (Imp_f (Imp_f P Q) (Not_f (Imp_f Q P))))
    where P := In_a b (Insert_t a c) and Q := In_a b c.

    Three PROV_HF_UI steps interleaved with substitute reductions
    (FORALL_MISS at the bound-var inequalities, IMP/NOT/EQ/IN/INSERT
    push-through, VAR_HIT at the substitution-target leaf, VAR_MISS at
    the other two leaves, and the three precond stability rewrites
    h_ab / h_ac / h_bc to keep the previously-substituted slots fixed).
    """
    p.goal(
        "!a b c. (is_term a /\\ is_term b /\\ is_term c) "
        "/\\ (substitute a b (SUC0 0) = a) "
        "/\\ (substitute a c (SUC0 (SUC0 0)) = a) "
        "/\\ (substitute b c (SUC0 (SUC0 0)) = b) "
        "==> Prov_HF (Imp_f (Not_f (Eq_f a b)) "
        "             (Not_f (Imp_f "
        "                (Imp_f (In_a b (Insert_t a c)) (In_a b c)) "
        "                (Not_f (Imp_f (In_a b c) "
        "                              (In_a b (Insert_t a c)))))))",
        types={"a": nat0_ty, "b": nat0_ty, "c": nat0_ty},
    )
    p.fix("a b c")
    p.assume(
        "((ha, hb, hc), h_ab, h_ac, h_bc): "
        "(is_term a /\\ is_term b /\\ is_term c) "
        "/\\ (substitute a b (SUC0 0) = a) "
        "/\\ (substitute a c (SUC0 (SUC0 0)) = a) "
        "/\\ (substitute b c (SUC0 (SUC0 0)) = b)"
    )

    # Step 1: |- Prov_HF HF3_axiom unfolded.
    prov_h3_raw = _prov_of_hf_axiom(HF3_axiom)
    p.have(
        "h_prov_3a: Prov_HF (Forall_f 0 (" + _B2_text() + "))"
    ).by_rewrite_of(prov_h3_raw, [HF3_AXIOM_DEF])

    # Step 2: is_form for each layer (B0, B1, B2) -- with var_x/y/z
    # folded; the rewriter handles the unfold during simp normalisation.
    # is_term (Insert_t var_x var_z).
    is_term_insert_xz = MP(
        SPECL([var_x, var_z], IS_TERM_INSERT),
        CONJ(IS_TERM_VAR_X, IS_TERM_VAR_Z),
    )
    # is_form (Eq_f var_x var_y).
    eq_xy_at = SPECL([var_x, var_y], IS_FORM_AT_EQ)
    is_form_eq_xy = EQ_MP(
        SYM(eq_xy_at), CONJ(IS_TERM_VAR_X, IS_TERM_VAR_Y)
    )
    # is_form (Not_f (Eq_f var_x var_y)).
    not_eq_at = SPEC(p._parse("Eq_f var_x var_y"), IS_FORM_AT_NOT)
    is_form_not_eq_xy = EQ_MP(SYM(not_eq_at), is_form_eq_xy)
    # is_form (In_a var_y (Insert_t var_x var_z)).
    in_y_xz_at = SPECL(
        [var_y, p._parse("Insert_t var_x var_z")], IS_FORM_AT_IN
    )
    is_form_in_y_xz = EQ_MP(
        SYM(in_y_xz_at), CONJ(IS_TERM_VAR_Y, is_term_insert_xz)
    )
    # is_form (In_a var_y var_z).
    in_y_z_at = SPECL([var_y, var_z], IS_FORM_AT_IN)
    is_form_in_y_z = EQ_MP(
        SYM(in_y_z_at), CONJ(IS_TERM_VAR_Y, IS_TERM_VAR_Z)
    )
    # is_form (Imp_f (In_a y (Insert x z)) (In_a y z)).
    imp_pq_at = SPECL(
        [
            p._parse("In_a var_y (Insert_t var_x var_z)"),
            p._parse("In_a var_y var_z"),
        ],
        IS_FORM_AT_IMP,
    )
    is_form_imp_pq = EQ_MP(
        SYM(imp_pq_at), CONJ(is_form_in_y_xz, is_form_in_y_z)
    )
    # is_form (Imp_f (In_a y z) (In_a y (Insert x z))).
    imp_qp_at = SPECL(
        [
            p._parse("In_a var_y var_z"),
            p._parse("In_a var_y (Insert_t var_x var_z)"),
        ],
        IS_FORM_AT_IMP,
    )
    is_form_imp_qp = EQ_MP(
        SYM(imp_qp_at), CONJ(is_form_in_y_z, is_form_in_y_xz)
    )
    # is_form (Not_f (Imp_f Q P)).
    not_imp_qp_at = SPEC(
        p._parse(
            "Imp_f (In_a var_y var_z) (In_a var_y (Insert_t var_x var_z))"
        ),
        IS_FORM_AT_NOT,
    )
    is_form_not_imp_qp = EQ_MP(SYM(not_imp_qp_at), is_form_imp_qp)
    # is_form (Imp_f (Imp_f P Q) (Not_f (Imp_f Q P))).
    imp_outer_at = SPECL(
        [
            p._parse(
                "Imp_f (In_a var_y (Insert_t var_x var_z)) "
                "      (In_a var_y var_z)"
            ),
            p._parse(
                "Not_f (Imp_f (In_a var_y var_z) "
                "             (In_a var_y (Insert_t var_x var_z)))"
            ),
        ],
        IS_FORM_AT_IMP,
    )
    is_form_imp_outer = EQ_MP(
        SYM(imp_outer_at),
        CONJ(is_form_imp_pq, is_form_not_imp_qp),
    )
    # is_form (Not_f (Imp_f ... ...)).
    not_imp_outer_at = SPEC(
        p._parse(
            "Imp_f "
            "(Imp_f (In_a var_y (Insert_t var_x var_z)) "
            "       (In_a var_y var_z)) "
            "(Not_f (Imp_f (In_a var_y var_z) "
            "              (In_a var_y (Insert_t var_x var_z))))"
        ),
        IS_FORM_AT_NOT,
    )
    is_form_not_imp_outer = EQ_MP(
        SYM(not_imp_outer_at), is_form_imp_outer
    )
    # is_form B0.
    imp_top_at = SPECL(
        [
            p._parse("Not_f (Eq_f var_x var_y)"),
            p._parse(
                "Not_f (Imp_f "
                "(Imp_f (In_a var_y (Insert_t var_x var_z)) "
                "       (In_a var_y var_z)) "
                "(Not_f (Imp_f (In_a var_y var_z) "
                "              (In_a var_y (Insert_t var_x var_z)))))"
            ),
        ],
        IS_FORM_AT_IMP,
    )
    is_form_B0 = EQ_MP(
        SYM(imp_top_at),
        CONJ(is_form_not_eq_xy, is_form_not_imp_outer),
    )
    # is_form B1 = is_form (Forall_f (SUC0 SUC0 0) B0).
    fa_B0_at = SPECL(
        [_idx2, p._parse(_B0_text())], IS_FORM_AT_FORALL,
    )
    is_form_B1 = EQ_MP(SYM(fa_B0_at), is_form_B0)
    # is_form B2 = is_form (Forall_f (SUC0 0) B1).
    fa_B1_at = SPECL(
        [_idx1, p._parse(_B1_text())], IS_FORM_AT_FORALL,
    )
    is_form_B2 = EQ_MP(SYM(fa_B1_at), is_form_B1)

    p.have("h_is_form_B2: is_form (" + _B2_text() + ")").by_thm(is_form_B2)

    # Substitute leaf rules at idx 0 (subst target = 0).
    subst_v0_at_0 = _subst_var_hit(_idx0, _a_n0)
    subst_v1_at_0 = _subst_var_miss(_idx1, _a_n0, _idx0, _neq_0_s0)
    subst_v2_at_0 = _subst_var_miss(_idx2, _a_n0, _idx0, _neq_0_ss0)

    # FORALL_MISS at subst_idx = 0 -- conditional on bound idx ≠ 0.
    fa_miss_b1_at_0 = _subst_forall_miss(
        _idx1, _B1_unfolded(p), _a_n0, _idx0, _neq_0_s0
    )
    # The inner Forall_f wraps B0; FORALL_MISS at SUC0 SUC0 0 ≠ 0.
    fa_miss_b0_at_0 = _subst_forall_miss(
        _idx2, _B0_unfolded(p), _a_n0, _idx0, _neq_0_ss0
    )

    # ---- UI 1 (substitute a for var_x = Var_t 0) ----
    body_after_ui1 = _body3_at("a", _VS1, _VS2)
    forall_v2_body_after_ui1 = f"(Forall_f (SUC0 (SUC0 0)) {body_after_ui1})"
    full_after_ui1 = f"(Forall_f (SUC0 0) {forall_v2_body_after_ui1})"

    p.have(
        "h_ui1: Prov_HF (substitute (" + _B2_text() + ") a 0)"
    ).by(
        PROV_HF_UI, "0", _B2_text(), "a",
        CONJ(
            p.fact("h_is_form_B2"),
            CONJ(p.fact("ha"), p.fact("h_prov_3a")),
        ),
    )
    p.have(
        f"h_ui1_red: Prov_HF {full_after_ui1}"
    ).by_rewrite_of(
        "h_ui1",
        [
            VAR_X_DEF, VAR_Y_DEF, VAR_Z_DEF,
            fa_miss_b1_at_0, fa_miss_b0_at_0,
            SUBSTITUTE_AT_IMP, SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_EQ, SUBSTITUTE_AT_IN, SUBSTITUTE_AT_INSERT,
            subst_v0_at_0, subst_v1_at_0, subst_v2_at_0,
        ],
    )

    # ---- UI 2 (substitute b for var_y = Var_t (SUC0 0)) ----
    # Need is_form of the body Forall_f (SUC0 (SUC0 0)) B0[a/var_x].
    # Build it manually from is_term a + leaf is_term facts.
    is_term_v1 = EQT_ELIM(SPEC(_idx1, IS_TERM_AT_VAR))
    is_term_v2 = EQT_ELIM(SPEC(_idx2, IS_TERM_AT_VAR))
    # is_term (Insert_t a (Var_t (SUC0 (SUC0 0)))).
    is_term_insert_av2 = MP(
        SPECL([_a_n0, p._parse("Var_t (SUC0 (SUC0 0))")], IS_TERM_INSERT),
        CONJ(p.fact("ha"), is_term_v2),
    )
    # is_form (Eq_f a (Var_t (SUC0 0))).
    eq_av1_at = SPECL(
        [_a_n0, p._parse("Var_t (SUC0 0)")], IS_FORM_AT_EQ,
    )
    is_form_eq_av1 = EQ_MP(
        SYM(eq_av1_at), CONJ(p.fact("ha"), is_term_v1)
    )
    is_form_not_eq_av1 = EQ_MP(
        SYM(SPEC(p._parse("Eq_f a (Var_t (SUC0 0))"), IS_FORM_AT_NOT)),
        is_form_eq_av1,
    )
    # is_form (In_a (Var_t (SUC0 0)) (Insert_t a (Var_t (SUC0 (SUC0 0))))).
    in_v1_av2_at = SPECL(
        [
            p._parse("Var_t (SUC0 0)"),
            p._parse("Insert_t a (Var_t (SUC0 (SUC0 0)))"),
        ],
        IS_FORM_AT_IN,
    )
    is_form_in_v1_av2 = EQ_MP(
        SYM(in_v1_av2_at), CONJ(is_term_v1, is_term_insert_av2)
    )
    # is_form (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))).
    in_v1_v2_at = SPECL(
        [
            p._parse("Var_t (SUC0 0)"),
            p._parse("Var_t (SUC0 (SUC0 0))"),
        ],
        IS_FORM_AT_IN,
    )
    is_form_in_v1_v2 = EQ_MP(
        SYM(in_v1_v2_at), CONJ(is_term_v1, is_term_v2)
    )
    is_form_imp_pq_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "In_a (Var_t (SUC0 0)) "
                    "(Insert_t a (Var_t (SUC0 (SUC0 0))))"
                ),
                p._parse(
                    "In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_v1_av2, is_form_in_v1_v2),
    )
    is_form_imp_qp_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))"
                ),
                p._parse(
                    "In_a (Var_t (SUC0 0)) "
                    "(Insert_t a (Var_t (SUC0 (SUC0 0))))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_v1_v2, is_form_in_v1_av2),
    )
    is_form_not_imp_qp_a = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f (In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
                "      (In_a (Var_t (SUC0 0)) "
                "            (Insert_t a (Var_t (SUC0 (SUC0 0)))))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_qp_a,
    )
    is_form_imp_outer_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "Imp_f (In_a (Var_t (SUC0 0)) "
                    "             (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                    "      (In_a (Var_t (SUC0 0)) "
                    "             (Var_t (SUC0 (SUC0 0))))"
                ),
                p._parse(
                    "Not_f (Imp_f "
                    "(In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
                    "(In_a (Var_t (SUC0 0)) "
                    "      (Insert_t a (Var_t (SUC0 (SUC0 0))))))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_imp_pq_a, is_form_not_imp_qp_a),
    )
    is_form_not_imp_outer_a = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f "
                "(Imp_f (In_a (Var_t (SUC0 0)) "
                "             (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                "       (In_a (Var_t (SUC0 0)) "
                "             (Var_t (SUC0 (SUC0 0))))) "
                "(Not_f (Imp_f "
                "(In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
                "(In_a (Var_t (SUC0 0)) "
                "      (Insert_t a (Var_t (SUC0 (SUC0 0)))))))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_outer_a,
    )
    is_form_B0_at_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse("Not_f (Eq_f a (Var_t (SUC0 0)))"),
                p._parse(
                    "Not_f (Imp_f "
                    "(Imp_f (In_a (Var_t (SUC0 0)) "
                    "             (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                    "       (In_a (Var_t (SUC0 0)) "
                    "             (Var_t (SUC0 (SUC0 0))))) "
                    "(Not_f (Imp_f "
                    "(In_a (Var_t (SUC0 0)) (Var_t (SUC0 (SUC0 0)))) "
                    "(In_a (Var_t (SUC0 0)) "
                    "      (Insert_t a (Var_t (SUC0 (SUC0 0)))))))) "
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_not_eq_av1, is_form_not_imp_outer_a),
    )
    # is_form (Forall_f (SUC0 SUC0 0) B0[a/var_x]).
    is_form_B1_at_a = EQ_MP(
        SYM(SPECL([_idx2, _B0_at_a(p)], IS_FORM_AT_FORALL)),
        is_form_B0_at_a,
    )
    p.have(
        f"h_is_form_B1_a: is_form {forall_v2_body_after_ui1}"
    ).by_thm(is_form_B1_at_a)

    # FORALL_MISS at subst_idx = SUC0 0 -- conditional on bound idx ≠ SUC0 0.
    fa_miss_b0_at_s0 = _subst_forall_miss(
        _idx2, _B0_at_a(p), _b_n0, _idx1, _neq_s0_ss0
    )
    # Substitute leaf rules at idx SUC0 0.
    subst_v1_at_s0 = _subst_var_hit(_idx1, _b_n0)
    subst_v2_at_s0 = _subst_var_miss(_idx2, _b_n0, _idx1, _neq_s0_ss0)

    body_after_ui2 = _body3_at("a", "b", _VS2)
    forall_v2_body_after_ui2 = f"(Forall_f (SUC0 (SUC0 0)) {body_after_ui2})"

    p.have(
        f"h_ui2: Prov_HF (substitute {forall_v2_body_after_ui1} b (SUC0 0))"
    ).by(
        PROV_HF_UI, "SUC0 0", forall_v2_body_after_ui1, "b",
        CONJ(
            p.fact("h_is_form_B1_a"),
            CONJ(p.fact("hb"), p.fact("h_ui1_red")),
        ),
    )

    p.have(
        f"h_ui2_red: Prov_HF {forall_v2_body_after_ui2}"
    ).by_rewrite_of(
        "h_ui2",
        [
            fa_miss_b0_at_s0,
            SUBSTITUTE_AT_IMP, SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_EQ, SUBSTITUTE_AT_IN, SUBSTITUTE_AT_INSERT,
            subst_v1_at_s0, subst_v2_at_s0,
            "h_ab",
        ],
    )

    # ---- UI 3 (substitute c for var_z = Var_t (SUC0 SUC0 0)) ----
    # is_form of B0[a/var_x, b/var_y].
    # is_term (Insert_t a (Var_t (SUC0 (SUC0 0)))).
    # is_form (Eq_f a b).
    is_form_eq_ab = EQ_MP(
        SYM(SPECL([_a_n0, _b_n0], IS_FORM_AT_EQ)),
        CONJ(p.fact("ha"), p.fact("hb")),
    )
    is_form_not_eq_ab = EQ_MP(
        SYM(SPEC(p._parse("Eq_f a b"), IS_FORM_AT_NOT)),
        is_form_eq_ab,
    )
    # is_form (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))).
    is_form_in_b_av2 = EQ_MP(
        SYM(SPECL(
            [_b_n0, p._parse("Insert_t a (Var_t (SUC0 (SUC0 0)))")],
            IS_FORM_AT_IN,
        )),
        CONJ(p.fact("hb"), is_term_insert_av2),
    )
    # is_form (In_a b (Var_t (SUC0 (SUC0 0)))).
    is_form_in_b_v2 = EQ_MP(
        SYM(SPECL(
            [_b_n0, p._parse("Var_t (SUC0 (SUC0 0))")],
            IS_FORM_AT_IN,
        )),
        CONJ(p.fact("hb"), is_term_v2),
    )
    is_form_imp_pq_ab = EQ_MP(
        SYM(SPECL(
            [
                p._parse("In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))"),
                p._parse("In_a b (Var_t (SUC0 (SUC0 0)))"),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_b_av2, is_form_in_b_v2),
    )
    is_form_imp_qp_ab = EQ_MP(
        SYM(SPECL(
            [
                p._parse("In_a b (Var_t (SUC0 (SUC0 0)))"),
                p._parse("In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))"),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_b_v2, is_form_in_b_av2),
    )
    is_form_not_imp_qp_ab = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f (In_a b (Var_t (SUC0 (SUC0 0)))) "
                "      (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0)))))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_qp_ab,
    )
    is_form_imp_outer_ab = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "Imp_f "
                    "(In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                    "(In_a b (Var_t (SUC0 (SUC0 0))))"
                ),
                p._parse(
                    "Not_f (Imp_f (In_a b (Var_t (SUC0 (SUC0 0)))) "
                    "             (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_imp_pq_ab, is_form_not_imp_qp_ab),
    )
    is_form_not_imp_outer_ab = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f "
                "(Imp_f (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                "       (In_a b (Var_t (SUC0 (SUC0 0))))) "
                "(Not_f (Imp_f (In_a b (Var_t (SUC0 (SUC0 0)))) "
                "              (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0)))))))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_outer_ab,
    )
    is_form_B0_at_ab = EQ_MP(
        SYM(SPECL(
            [
                p._parse("Not_f (Eq_f a b)"),
                p._parse(
                    "Not_f (Imp_f "
                    "(Imp_f (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))) "
                    "       (In_a b (Var_t (SUC0 (SUC0 0))))) "
                    "(Not_f (Imp_f (In_a b (Var_t (SUC0 (SUC0 0)))) "
                    "              (In_a b (Insert_t a (Var_t (SUC0 (SUC0 0))))))))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_not_eq_ab, is_form_not_imp_outer_ab),
    )
    p.have(
        f"h_is_form_B0_ab: is_form {body_after_ui2}"
    ).by_thm(is_form_B0_at_ab)

    # Leaf rules at idx SUC0 SUC0 0.
    subst_v2_at_ss0 = _subst_var_hit(_idx2, _c_n0)

    body_final = _body3_at("a", "b", "c")

    p.have(
        f"h_ui3: Prov_HF (substitute {body_after_ui2} c (SUC0 (SUC0 0)))"
    ).by(
        PROV_HF_UI, "SUC0 (SUC0 0)", body_after_ui2, "c",
        CONJ(
            p.fact("h_is_form_B0_ab"),
            CONJ(p.fact("hc"), p.fact("h_ui2_red")),
        ),
    )

    p.thus(f"Prov_HF {body_final}").by_rewrite_of(
        "h_ui3",
        [
            SUBSTITUTE_AT_IMP, SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_EQ, SUBSTITUTE_AT_IN, SUBSTITUTE_AT_INSERT,
            subst_v2_at_ss0,
            "h_ac", "h_bc",
        ],
    )


# ---------------------------------------------------------------------------
# QUOTE_HF_INJ -- HOL-level injectivity of the quoting map.
# ---------------------------------------------------------------------------


@proof
def QUOTE_HF_INJ(p):
    """|- !s t. quote_hf s = quote_hf t ==> s = t.

    Strong induction on ``s`` with predicate
    ``\\s. !t. quote_hf s = quote_hf t ==> s = t``.  Inside the induction
    body we ``fix t`` and assume the quote_hf-equation, then case-split
    on ``s = 0`` and ``t = 0`` for four branches:

      * (s=0 ∧ t=0)  : direct rewrite.
      * (s=0 ∧ t≠0)  : quote_hf s reduces to Empty_t, quote_hf t reduces
                       to Insert_t _ _; INSERT_T_NEQ_EMPTY closes via
                       contradiction.
      * (s≠0 ∧ t=0)  : symmetric.
      * (s≠0 ∧ t≠0)  : both sides bit-decompose; INSERT_T_INJ peels the
                       outer Insert_t; the IH fires twice (at low_bit s
                       under LOW_BIT_LT and clear_low s under CLEAR_LOW_LT)
                       to lift the quote_hf equalities to bit equalities;
                       INSERT_LOW_BIT_CLEAR_LOW reconstructs s and t.
    """
    p.goal(
        "!s t. quote_hf s = quote_hf t ==> s = t",
        types={"s": nat0_ty, "t": nat0_ty},
    )
    with p.strong_induction("s", "IH"):
        # Goal:  !t. quote_hf s = quote_hf t ==> s = t.
        # IH:    !u. nat0_lt u s ==> !t'. quote_hf u = quote_hf t' ==> u = t'.
        p.fix("t")
        p.assume("h_qeq: quote_hf s = quote_hf t")
        with p.cases_on(EXCLUDED_MIDDLE, "s = 0"):
            with p.case("hsz: s = 0"):
                with p.cases_on(EXCLUDED_MIDDLE, "t = 0"):
                    with p.case("htz: t = 0"):
                        p.thus("s = t").by_rewrite_of("hsz", ["htz"])
                    with p.case("htnz: ~(t = 0)"):
                        # quote_hf s reduces to Empty_t.
                        p.have("h_qs: quote_hf s = Empty_t").by_rewrite(
                            ["hsz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                        )
                        # quote_hf t bit-decomposes into Insert_t.
                        p.have(
                            "h_qt: quote_hf t = "
                            "Insert_t (quote_hf (low_bit t)) "
                            "         (quote_hf (clear_low t))"
                        ).by(_QUOTE_HF_AT_NZ, "t", "htnz")
                        # h_qeq + h_qs + h_qt → Empty_t = Insert_t _ _.
                        p.have(
                            "h_eq_ins: Empty_t = "
                            "Insert_t (quote_hf (low_bit t)) "
                            "         (quote_hf (clear_low t))"
                        ).by_rewrite_of("h_qeq", ["h_qs", "h_qt"])
                        neq_th = SPECL(
                            [
                                p._parse("quote_hf (low_bit t)"),
                                p._parse("quote_hf (clear_low t)"),
                            ],
                            INSERT_T_NEQ_EMPTY,
                        )
                        # neq_th : ~(Insert_t _ _ = Empty_t).
                        contra = MP(
                            NOT_ELIM(neq_th), SYM(p.fact("h_eq_ins"))
                        )
                        p.thus("s = t").by_thm(
                            CONTR(p._parse("s = t"), contra)
                        )
            with p.case("hsnz: ~(s = 0)"):
                with p.cases_on(EXCLUDED_MIDDLE, "t = 0"):
                    with p.case("htz: t = 0"):
                        # Symmetric to the (s=0, t≠0) case: flip h_qeq
                        # and use the same INSERT_T_NEQ_EMPTY reasoning.
                        p.have("h_qt: quote_hf t = Empty_t").by_rewrite(
                            ["htz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                        )
                        p.have(
                            "h_qs: quote_hf s = "
                            "Insert_t (quote_hf (low_bit s)) "
                            "         (quote_hf (clear_low s))"
                        ).by(_QUOTE_HF_AT_NZ, "s", "hsnz")
                        p.have(
                            "h_eq_ins: "
                            "Insert_t (quote_hf (low_bit s)) "
                            "         (quote_hf (clear_low s)) = Empty_t"
                        ).by_rewrite_of("h_qeq", ["h_qt", "h_qs"])
                        neq_th = SPECL(
                            [
                                p._parse("quote_hf (low_bit s)"),
                                p._parse("quote_hf (clear_low s)"),
                            ],
                            INSERT_T_NEQ_EMPTY,
                        )
                        contra = MP(NOT_ELIM(neq_th), p.fact("h_eq_ins"))
                        p.thus("s = t").by_thm(
                            CONTR(p._parse("s = t"), contra)
                        )
                    with p.case("htnz: ~(t = 0)"):
                        # Both bit-decompose; INSERT_T_INJ + IH twice.
                        p.have(
                            "h_qs: quote_hf s = "
                            "Insert_t (quote_hf (low_bit s)) "
                            "         (quote_hf (clear_low s))"
                        ).by(_QUOTE_HF_AT_NZ, "s", "hsnz")
                        p.have(
                            "h_qt: quote_hf t = "
                            "Insert_t (quote_hf (low_bit t)) "
                            "         (quote_hf (clear_low t))"
                        ).by(_QUOTE_HF_AT_NZ, "t", "htnz")
                        p.have(
                            "h_ins_eq: "
                            "Insert_t (quote_hf (low_bit s)) "
                            "         (quote_hf (clear_low s)) "
                            "= Insert_t (quote_hf (low_bit t)) "
                            "           (quote_hf (clear_low t))"
                        ).by_rewrite_of("h_qeq", ["h_qs", "h_qt"])
                        p.have(
                            "h_args_eq: "
                            "(quote_hf (low_bit s) = quote_hf (low_bit t)) "
                            "/\\ (quote_hf (clear_low s) "
                            "    = quote_hf (clear_low t))"
                        ).by(
                            INSERT_T_INJ,
                            "quote_hf (low_bit s)",
                            "quote_hf (clear_low s)",
                            "quote_hf (low_bit t)",
                            "quote_hf (clear_low t)",
                            "h_ins_eq",
                        )
                        h_lb_q = CONJUNCT1(p.fact("h_args_eq"))
                        h_cl_q = CONJUNCT2(p.fact("h_args_eq"))
                        p.have(
                            "h_lb_q: quote_hf (low_bit s) = quote_hf (low_bit t)"
                        ).by_thm(h_lb_q)
                        p.have(
                            "h_cl_q: quote_hf (clear_low s) "
                            "= quote_hf (clear_low t)"
                        ).by_thm(h_cl_q)
                        # IH twice.
                        p.have("h_lb_lt: nat0_lt (low_bit s) s").by(
                            LOW_BIT_LT, "s", "hsnz"
                        )
                        p.have("h_cl_lt: nat0_lt (clear_low s) s").by(
                            CLEAR_LOW_LT, "s", "hsnz"
                        )
                        p.have(
                            "h_lb_eq: low_bit s = low_bit t"
                        ).by(
                            "IH",
                            "low_bit s",
                            "h_lb_lt",
                            "low_bit t",
                            "h_lb_q",
                        )
                        p.have(
                            "h_cl_eq: clear_low s = clear_low t"
                        ).by(
                            "IH",
                            "clear_low s",
                            "h_cl_lt",
                            "clear_low t",
                            "h_cl_q",
                        )
                        # Reconstruct s and t via INSERT_LOW_BIT_CLEAR_LOW.
                        p.have(
                            "h_recon_s: s = set_bit (low_bit s) (clear_low s)"
                        ).by(INSERT_LOW_BIT_CLEAR_LOW, "s", "hsnz")
                        p.have(
                            "h_recon_t: t = set_bit (low_bit t) (clear_low t)"
                        ).by(INSERT_LOW_BIT_CLEAR_LOW, "t", "htnz")
                        p.thus("s = t").by_rewrite_of(
                            "h_recon_s",
                            [
                                "h_lb_eq", "h_cl_eq",
                                SYM(p.fact("h_recon_t")),
                            ],
                        )


# ---------------------------------------------------------------------------
# HF4_INST -- HF4 axiom (extensionality) instantiated at concrete (a, b).
#
# HF4_axiom (two Forall_f layers):
#   Forall_f 0 (Forall_f (SUC0 0)
#     (Imp_f (Forall_f (SUC0 (SUC0 0))
#               (encoded-iff (In_a var_z var_x) (In_a var_z var_y)))
#            (Eq_f var_x var_y))).
#
# Two UI steps + substitute reductions, structurally identical to
# HF2/HF3_INST.  The only extra wrinkle is that the body contains a
# nested encoded biconditional under the ∀z layer, so the `is_form`
# evidence and substitute-normalization steps must name the folded and
# unfolded shapes explicitly.
# ---------------------------------------------------------------------------


def _body4_iff_at(z, x, y):
    """HF4's encoded iff body at parser-syntax terms z, x, y."""
    return (
        f"(Not_f (Imp_f "
        f"(Imp_f (In_a {z} {x}) (In_a {z} {y})) "
        f"(Not_f (Imp_f (In_a {z} {y}) (In_a {z} {x})))))"
    )


def _body4_at(x, y):
    """HF4 body `(!z. In z x <-> In z y) -> x = y` at x, y."""
    return (
        f"(Imp_f (Forall_f (SUC0 (SUC0 0)) "
        f"{_body4_iff_at(_VS2, x, y)}) "
        f"(Eq_f {x} {y}))"
    )


def _B4_0_text():
    return (
        "Not_f (Imp_f "
        "(Imp_f (In_a var_z var_x) (In_a var_z var_y)) "
        "(Not_f (Imp_f (In_a var_z var_y) (In_a var_z var_x))))"
    )


def _B4_1_text():
    return (
        "Imp_f (Forall_f (SUC0 (SUC0 0)) ("
        + _B4_0_text()
        + ")) (Eq_f var_x var_y)"
    )


def _B4_2_text():
    return "Forall_f (SUC0 0) (" + _B4_1_text() + ")"


def _B4_0_unfolded(p):
    return p._parse(_body4_iff_at(_VS2, _VS0, _VS1))


def _B4_1_unfolded(p):
    return p._parse(_body4_at(_VS0, _VS1))


def _B4_0_at_a(p):
    return p._parse(_B4_0_at_a_text())


def _B4_0_at_a_text():
    return (
        "Not_f (Imp_f "
        "(Imp_f (In_a (Var_t (SUC0 (SUC0 0))) a) "
        "       (In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0)))) "
        "(Not_f (Imp_f "
        "       (In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))) "
        "       (In_a (Var_t (SUC0 (SUC0 0))) a))))"
    )


@proof
def HF4_INST(p):
    """|- !a b. is_term a /\\ is_term b
                /\\ (substitute a b (SUC0 0) = a)
                ==> Prov_HF (Imp_f
                       (Forall_f (SUC0 (SUC0 0))
                         (Not_f (Imp_f
                            (Imp_f (In_a (Var_t (SUC0 (SUC0 0))) a)
                                   (In_a (Var_t (SUC0 (SUC0 0))) b))
                            (Not_f (Imp_f
                               (In_a (Var_t (SUC0 (SUC0 0))) b)
                               (In_a (Var_t (SUC0 (SUC0 0))) a))))))
                       (Eq_f a b)).

    HF4 (extensionality) instantiated at (a, b).  This is the same
    mechanical pattern as HF2/HF3_INST: two PROV_HF_UI steps interleaved
    with substitute reductions through the body's ∀z + encoded-iff
    structure.

    DSL note: encoded biconditional is
        Not_f (Imp_f (Imp_f (In z a) (In z b)) (Not_f (Imp_f (In z b) (In z a))))
    -- the parser-level shape used by HF4_AXIOM_DEF.
    """
    p.goal(
        "!a b. is_term a /\\ is_term b "
        "/\\ (substitute a b (SUC0 0) = a) "
        "==> Prov_HF (Imp_f "
        "      (Forall_f (SUC0 (SUC0 0)) "
        "        (Not_f (Imp_f "
        "           (Imp_f (In_a (Var_t (SUC0 (SUC0 0))) a) "
        "                  (In_a (Var_t (SUC0 (SUC0 0))) b)) "
        "           (Not_f (Imp_f "
        "              (In_a (Var_t (SUC0 (SUC0 0))) b) "
        "              (In_a (Var_t (SUC0 (SUC0 0))) a)))))) "
        "      (Eq_f a b))",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.assume(
        "(ha, hb, h_ab): is_term a /\\ is_term b "
        "/\\ (substitute a b (SUC0 0) = a)"
    )

    prov_h4_raw = _prov_of_hf_axiom(HF4_axiom)
    p.have(
        "h_prov_4a: Prov_HF (Forall_f 0 (" + _B4_2_text() + "))"
    ).by_rewrite_of(prov_h4_raw, [HF4_AXIOM_DEF])

    # is_form for the axiom body with var_x/var_y/var_z folded.
    in_z_x_at = SPECL([var_z, var_x], IS_FORM_AT_IN)
    is_form_in_z_x = EQ_MP(
        SYM(in_z_x_at), CONJ(IS_TERM_VAR_Z, IS_TERM_VAR_X)
    )
    in_z_y_at = SPECL([var_z, var_y], IS_FORM_AT_IN)
    is_form_in_z_y = EQ_MP(
        SYM(in_z_y_at), CONJ(IS_TERM_VAR_Z, IS_TERM_VAR_Y)
    )
    is_form_imp_pq = EQ_MP(
        SYM(SPECL(
            [p._parse("In_a var_z var_x"), p._parse("In_a var_z var_y")],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_z_x, is_form_in_z_y),
    )
    is_form_imp_qp = EQ_MP(
        SYM(SPECL(
            [p._parse("In_a var_z var_y"), p._parse("In_a var_z var_x")],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_z_y, is_form_in_z_x),
    )
    is_form_not_imp_qp = EQ_MP(
        SYM(SPEC(
            p._parse("Imp_f (In_a var_z var_y) (In_a var_z var_x)"),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_qp,
    )
    is_form_imp_outer = EQ_MP(
        SYM(SPECL(
            [
                p._parse("Imp_f (In_a var_z var_x) (In_a var_z var_y)"),
                p._parse(
                    "Not_f (Imp_f (In_a var_z var_y) (In_a var_z var_x))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_imp_pq, is_form_not_imp_qp),
    )
    is_form_B4_0 = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f (Imp_f (In_a var_z var_x) (In_a var_z var_y)) "
                "      (Not_f (Imp_f (In_a var_z var_y) "
                "                         (In_a var_z var_x)))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_outer,
    )
    is_form_forall_z = EQ_MP(
        SYM(SPECL([_idx2, p._parse(_B4_0_text())], IS_FORM_AT_FORALL)),
        is_form_B4_0,
    )
    is_form_eq_xy = EQ_MP(
        SYM(SPECL([var_x, var_y], IS_FORM_AT_EQ)),
        CONJ(IS_TERM_VAR_X, IS_TERM_VAR_Y),
    )
    is_form_B4_1 = EQ_MP(
        SYM(SPECL(
            [
                p._parse("Forall_f (SUC0 (SUC0 0)) (" + _B4_0_text() + ")"),
                p._parse("Eq_f var_x var_y"),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_forall_z, is_form_eq_xy),
    )
    is_form_B4_2 = EQ_MP(
        SYM(SPECL([_idx1, p._parse(_B4_1_text())], IS_FORM_AT_FORALL)),
        is_form_B4_1,
    )
    p.have("h_is_form_B4_2: is_form (" + _B4_2_text() + ")").by_thm(
        is_form_B4_2
    )

    # ---- UI 1 (substitute a for var_x = Var_t 0) ----
    subst_v0_at_0 = _subst_var_hit(_idx0, _a_n0)
    subst_v1_at_0 = _subst_var_miss(_idx1, _a_n0, _idx0, _neq_0_s0)
    subst_v2_at_0 = _subst_var_miss(_idx2, _a_n0, _idx0, _neq_0_ss0)
    fa_miss_b4_1_at_0 = _subst_forall_miss(
        _idx1, _B4_1_unfolded(p), _a_n0, _idx0, _neq_0_s0
    )
    fa_miss_b4_0_at_0 = _subst_forall_miss(
        _idx2, _B4_0_unfolded(p), _a_n0, _idx0, _neq_0_ss0
    )
    body_after_ui1 = _body4_at("a", _VS1)
    full_after_ui1 = f"(Forall_f (SUC0 0) {body_after_ui1})"

    p.have(
        "h_ui1: Prov_HF (substitute (" + _B4_2_text() + ") a 0)"
    ).by(
        PROV_HF_UI, "0", _B4_2_text(), "a",
        CONJ(
            p.fact("h_is_form_B4_2"),
            CONJ(p.fact("ha"), p.fact("h_prov_4a")),
        ),
    )
    p.have(f"h_ui1_red: Prov_HF {full_after_ui1}").by_rewrite_of(
        "h_ui1",
        [
            VAR_X_DEF, VAR_Y_DEF, VAR_Z_DEF,
            fa_miss_b4_1_at_0, fa_miss_b4_0_at_0,
            SUBSTITUTE_AT_IMP, SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_EQ, SUBSTITUTE_AT_IN,
            subst_v0_at_0, subst_v1_at_0, subst_v2_at_0,
        ],
    )

    # ---- UI 2 (substitute b for var_y = Var_t (SUC0 0)) ----
    is_term_v1 = EQT_ELIM(SPEC(_idx1, IS_TERM_AT_VAR))
    is_term_v2 = EQT_ELIM(SPEC(_idx2, IS_TERM_AT_VAR))
    is_form_in_v2_a = EQ_MP(
        SYM(SPECL([p._parse("Var_t (SUC0 (SUC0 0))"), _a_n0], IS_FORM_AT_IN)),
        CONJ(is_term_v2, p.fact("ha")),
    )
    is_form_in_v2_v1 = EQ_MP(
        SYM(SPECL(
            [
                p._parse("Var_t (SUC0 (SUC0 0))"),
                p._parse("Var_t (SUC0 0)"),
            ],
            IS_FORM_AT_IN,
        )),
        CONJ(is_term_v2, is_term_v1),
    )
    is_form_imp_pq_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse("In_a (Var_t (SUC0 (SUC0 0))) a"),
                p._parse(
                    "In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_v2_a, is_form_in_v2_v1),
    )
    is_form_imp_qp_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))"
                ),
                p._parse("In_a (Var_t (SUC0 (SUC0 0))) a"),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_in_v2_v1, is_form_in_v2_a),
    )
    is_form_not_imp_qp_a = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f (In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))) "
                "      (In_a (Var_t (SUC0 (SUC0 0))) a)"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_qp_a,
    )
    is_form_imp_outer_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "Imp_f (In_a (Var_t (SUC0 (SUC0 0))) a) "
                    "      (In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0)))"
                ),
                p._parse(
                    "Not_f (Imp_f "
                    "(In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))) "
                    "(In_a (Var_t (SUC0 (SUC0 0))) a))"
                ),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_imp_pq_a, is_form_not_imp_qp_a),
    )
    is_form_B4_0_a = EQ_MP(
        SYM(SPEC(
            p._parse(
                "Imp_f "
                "(Imp_f (In_a (Var_t (SUC0 (SUC0 0))) a) "
                "       (In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0)))) "
                "(Not_f (Imp_f "
                "(In_a (Var_t (SUC0 (SUC0 0))) (Var_t (SUC0 0))) "
                "(In_a (Var_t (SUC0 (SUC0 0))) a)))"
            ),
            IS_FORM_AT_NOT,
        )),
        is_form_imp_outer_a,
    )
    is_form_forall_z_a = EQ_MP(
        SYM(SPECL([_idx2, _B4_0_at_a(p)], IS_FORM_AT_FORALL)),
        is_form_B4_0_a,
    )
    is_form_eq_a_v1 = EQ_MP(
        SYM(SPECL([_a_n0, p._parse("Var_t (SUC0 0)")], IS_FORM_AT_EQ)),
        CONJ(p.fact("ha"), is_term_v1),
    )
    is_form_B4_1_a = EQ_MP(
        SYM(SPECL(
            [
                p._parse(
                    "Forall_f (SUC0 (SUC0 0)) (" + _B4_0_at_a_text() + ")"
                ),
                p._parse("Eq_f a (Var_t (SUC0 0))"),
            ],
            IS_FORM_AT_IMP,
        )),
        CONJ(is_form_forall_z_a, is_form_eq_a_v1),
    )
    p.have(f"h_is_form_B4_1_a: is_form {body_after_ui1}").by_thm(
        is_form_B4_1_a
    )

    fa_miss_b4_0_at_s0 = _subst_forall_miss(
        _idx2, _B4_0_at_a(p), _b_n0, _idx1, _neq_s0_ss0
    )
    subst_v1_at_s0 = _subst_var_hit(_idx1, _b_n0)
    subst_v2_at_s0 = _subst_var_miss(_idx2, _b_n0, _idx1, _neq_s0_ss0)
    body_final = _body4_at("a", "b")

    p.have(
        f"h_ui2: Prov_HF (substitute {body_after_ui1} b (SUC0 0))"
    ).by(
        PROV_HF_UI, "SUC0 0", body_after_ui1, "b",
        CONJ(
            p.fact("h_is_form_B4_1_a"),
            CONJ(p.fact("hb"), p.fact("h_ui1_red")),
        ),
    )
    p.thus(f"Prov_HF {body_final}").by_rewrite_of(
        "h_ui2",
        [
            fa_miss_b4_0_at_s0,
            SUBSTITUTE_AT_IMP, SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_EQ, SUBSTITUTE_AT_IN,
            subst_v1_at_s0, subst_v2_at_s0,
            "h_ab",
        ],
    )


@proof
def PROV_HF_NEQ_FROM_MEM_DIFF(p):
    """|- !w s t. is_term s /\\ is_term t
                  /\\ Prov_HF (In_a (quote_hf w) s)
                  /\\ Prov_HF (Not_f (In_a (quote_hf w) t))
                  ==> Prov_HF (Not_f (Eq_f s t)).

    Object-level extensional discriminator.  If equality of ``s`` and
    ``t`` held, substitution into ``In_a (quote_hf w) (Var_t 0)`` would
    transport membership of ``quote_hf w`` from ``s`` to ``t``;
    contraposition against the supplied nonmembership closes
    ``Not_f (Eq_f s t)``.
    """
    p.goal(
        "!w s t. is_term s /\\ is_term t "
        "/\\ Prov_HF (In_a (quote_hf w) s) "
        "/\\ Prov_HF (Not_f (In_a (quote_hf w) t)) "
        "==> Prov_HF (Not_f (Eq_f s t))",
        types={"w": nat0_ty, "s": nat0_ty, "t": nat0_ty},
    )
    p.fix("w s t")
    p.assume(
        "(hs, ht, h_in_s, h_not_in_t): "
        "is_term s /\\ is_term t "
        "/\\ Prov_HF (In_a (quote_hf w) s) "
        "/\\ Prov_HF (Not_f (In_a (quote_hf w) t))"
    )
    p.have("h_tqw: is_term (quote_hf w)").by(IS_TERM_QUOTE_HF, "w")

    is_term_v0 = EQT_ELIM(SPEC(ZERO, IS_TERM_AT_VAR))
    p.have("h_t_v0: is_term (Var_t 0)").by_thm(is_term_v0)

    is_form_phi = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), p._parse("Var_t 0")], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("h_t_v0")),
    )
    p.have("h_f_phi: is_form (In_a (quote_hf w) (Var_t 0))").by_thm(is_form_phi)
    is_form_in_s = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), _s_n0], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("hs")),
    )
    p.have("h_f_in_s: is_form (In_a (quote_hf w) s)").by_thm(is_form_in_s)
    is_form_in_t = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), _t_n0], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("ht")),
    )
    p.have("h_f_in_t: is_form (In_a (quote_hf w) t)").by_thm(is_form_in_t)
    is_form_eq = EQ_MP(
        SYM(SPECL([_s_n0, _t_n0], IS_FORM_AT_EQ)),
        CONJ(p.fact("hs"), p.fact("ht")),
    )
    p.have("h_f_eq: is_form (Eq_f s t)").by_thm(is_form_eq)

    p.have(
        "h_subst_eq: Prov_HF (Imp_f (Eq_f s t) "
        "  (Imp_f (substitute (In_a (quote_hf w) (Var_t 0)) s 0) "
        "         (substitute (In_a (quote_hf w) (Var_t 0)) t 0)))"
    ).by(
        PROV_HF_SUBST_EQ, "0", "In_a (quote_hf w) (Var_t 0)", "s", "t",
        CONJ(
            p.fact("h_f_phi"),
            CONJ(p.fact("hs"), p.fact("ht")),
        ),
    )

    subst_v0_s = MP(
        SPECL([ZERO, _s_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    subst_v0_t = MP(
        SPECL([ZERO, _t_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    p.have(
        "h_imp_in: Prov_HF (Imp_f (Eq_f s t) "
        "  (Imp_f (In_a (quote_hf w) s) (In_a (quote_hf w) t)))"
    ).by_rewrite_of(
        "h_subst_eq",
        [
            SUBSTITUTE_AT_IN,
            subst_v0_s,
            subst_v0_t,
            SUBSTITUTE_QUOTE_HF,
        ],
    )

    p.have(
        "h_drop_in_s: Prov_HF (Imp_f (Eq_f s t) (In_a (quote_hf w) s))"
    ).by(
        PROV_HF_HYP_DROP,
        "Eq_f s t", "In_a (quote_hf w) s",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(p.fact("h_f_in_s"), p.fact("h_in_s")),
        ),
    )
    p.have(
        "h_eq_to_in_t: Prov_HF (Imp_f (Eq_f s t) (In_a (quote_hf w) t))"
    ).by(
        PROV_HF_DT_MP,
        "Eq_f s t", "In_a (quote_hf w) s", "In_a (quote_hf w) t",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(
                p.fact("h_f_in_s"),
                CONJ(
                    p.fact("h_f_in_t"),
                    CONJ(p.fact("h_drop_in_s"), p.fact("h_imp_in")),
                ),
            ),
        ),
    )
    p.have(
        "h_contrap: Prov_HF (Imp_f (Not_f (In_a (quote_hf w) t)) "
        "                         (Not_f (Eq_f s t)))"
    ).by(
        PROV_HF_CONTRAP,
        "Eq_f s t", "In_a (quote_hf w) t",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(p.fact("h_f_in_t"), p.fact("h_eq_to_in_t")),
        ),
    )
    p.thus("Prov_HF (Not_f (Eq_f s t))").by(
        PROV_HF_MP,
        "Not_f (In_a (quote_hf w) t)",
        "Not_f (Eq_f s t)",
        CONJ(p.fact("h_not_in_t"), p.fact("h_contrap")),
    )


@proof
def PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT(p):
    """|- !w s t. is_term s /\\ is_term t
                  /\\ Prov_HF (Not_f (In_a (quote_hf w) s))
                  /\\ Prov_HF (In_a (quote_hf w) t)
                  ==> Prov_HF (Not_f (Eq_f s t)).

    Reverse-orientation discriminator for the mutual quote_hf proof. If
    equality of ``s`` and ``t`` held, substitution into
    ``Not_f (In_a (quote_hf w) (Var_t 0))`` would transport
    nonmembership from ``s`` to ``t``; contraposition against positive
    membership of ``t`` closes ``Not_f (Eq_f s t)``.
    """
    p.goal(
        "!w s t. is_term s /\\ is_term t "
        "/\\ Prov_HF (Not_f (In_a (quote_hf w) s)) "
        "/\\ Prov_HF (In_a (quote_hf w) t) "
        "==> Prov_HF (Not_f (Eq_f s t))",
        types={"w": nat0_ty, "s": nat0_ty, "t": nat0_ty},
    )
    p.fix("w s t")
    p.assume(
        "(hs, ht, h_not_in_s, h_in_t): "
        "is_term s /\\ is_term t "
        "/\\ Prov_HF (Not_f (In_a (quote_hf w) s)) "
        "/\\ Prov_HF (In_a (quote_hf w) t)"
    )
    p.have("h_tqw: is_term (quote_hf w)").by(IS_TERM_QUOTE_HF, "w")

    is_term_v0 = EQT_ELIM(SPEC(ZERO, IS_TERM_AT_VAR))
    p.have("h_t_v0: is_term (Var_t 0)").by_thm(is_term_v0)

    is_form_in_v0 = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), p._parse("Var_t 0")], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("h_t_v0")),
    )
    is_form_phi = EQ_MP(
        SYM(SPEC(p._parse("In_a (quote_hf w) (Var_t 0)"), IS_FORM_AT_NOT)),
        is_form_in_v0,
    )
    p.have("h_f_phi: is_form (Not_f (In_a (quote_hf w) (Var_t 0)))").by_thm(
        is_form_phi
    )
    is_form_in_s = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), _s_n0], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("hs")),
    )
    is_form_not_in_s = EQ_MP(
        SYM(SPEC(p._parse("In_a (quote_hf w) s"), IS_FORM_AT_NOT)),
        is_form_in_s,
    )
    p.have("h_f_not_in_s: is_form (Not_f (In_a (quote_hf w) s))").by_thm(
        is_form_not_in_s
    )
    is_form_in_t = EQ_MP(
        SYM(SPECL([p._parse("quote_hf w"), _t_n0], IS_FORM_AT_IN)),
        CONJ(p.fact("h_tqw"), p.fact("ht")),
    )
    p.have("h_f_in_t: is_form (In_a (quote_hf w) t)").by_thm(is_form_in_t)
    is_form_not_in_t = EQ_MP(
        SYM(SPEC(p._parse("In_a (quote_hf w) t"), IS_FORM_AT_NOT)),
        is_form_in_t,
    )
    p.have("h_f_not_in_t: is_form (Not_f (In_a (quote_hf w) t))").by_thm(
        is_form_not_in_t
    )
    is_form_eq = EQ_MP(
        SYM(SPECL([_s_n0, _t_n0], IS_FORM_AT_EQ)),
        CONJ(p.fact("hs"), p.fact("ht")),
    )
    p.have("h_f_eq: is_form (Eq_f s t)").by_thm(is_form_eq)

    p.have(
        "h_subst_eq: Prov_HF (Imp_f (Eq_f s t) "
        "  (Imp_f (substitute (Not_f (In_a (quote_hf w) (Var_t 0))) s 0) "
        "         (substitute (Not_f (In_a (quote_hf w) (Var_t 0))) t 0)))"
    ).by(
        PROV_HF_SUBST_EQ, "0", "Not_f (In_a (quote_hf w) (Var_t 0))", "s", "t",
        CONJ(
            p.fact("h_f_phi"),
            CONJ(p.fact("hs"), p.fact("ht")),
        ),
    )

    subst_v0_s = MP(
        SPECL([ZERO, _s_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    subst_v0_t = MP(
        SPECL([ZERO, _t_n0, ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    p.have(
        "h_imp_not_in: Prov_HF (Imp_f (Eq_f s t) "
        "  (Imp_f (Not_f (In_a (quote_hf w) s)) "
        "         (Not_f (In_a (quote_hf w) t))))"
    ).by_rewrite_of(
        "h_subst_eq",
        [
            SUBSTITUTE_AT_NOT,
            SUBSTITUTE_AT_IN,
            subst_v0_s,
            subst_v0_t,
            SUBSTITUTE_QUOTE_HF,
        ],
    )

    p.have(
        "h_drop_not_in_s: Prov_HF (Imp_f (Eq_f s t) "
        "  (Not_f (In_a (quote_hf w) s)))"
    ).by(
        PROV_HF_HYP_DROP,
        "Eq_f s t", "Not_f (In_a (quote_hf w) s)",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(p.fact("h_f_not_in_s"), p.fact("h_not_in_s")),
        ),
    )
    p.have(
        "h_eq_to_not_in_t: Prov_HF (Imp_f (Eq_f s t) "
        "  (Not_f (In_a (quote_hf w) t)))"
    ).by(
        PROV_HF_DT_MP,
        "Eq_f s t",
        "Not_f (In_a (quote_hf w) s)",
        "Not_f (In_a (quote_hf w) t)",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(
                p.fact("h_f_not_in_s"),
                CONJ(
                    p.fact("h_f_not_in_t"),
                    CONJ(p.fact("h_drop_not_in_s"), p.fact("h_imp_not_in")),
                ),
            ),
        ),
    )
    p.have(
        "h_contrap: Prov_HF (Imp_f (Not_f (Not_f (In_a (quote_hf w) t))) "
        "                         (Not_f (Eq_f s t)))"
    ).by(
        PROV_HF_CONTRAP,
        "Eq_f s t", "Not_f (In_a (quote_hf w) t)",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(p.fact("h_f_not_in_t"), p.fact("h_eq_to_not_in_t")),
        ),
    )
    p.have(
        "h_dni_in_t: Prov_HF (Not_f (Not_f (In_a (quote_hf w) t)))"
    ).by(
        PROV_HF_DOUBLE_NEG_INTRO,
        "In_a (quote_hf w) t",
        CONJ(p.fact("h_f_in_t"), p.fact("h_in_t")),
    )
    p.thus("Prov_HF (Not_f (Eq_f s t))").by(
        PROV_HF_MP,
        "Not_f (Not_f (In_a (quote_hf w) t))",
        "Not_f (Eq_f s t)",
        CONJ(p.fact("h_dni_in_t"), p.fact("h_contrap")),
    )


@proof
def BOOL_NEQ_XOR(p):
    """|- !p q. ~(p = q) ==> (p /\\ ~q) \\/ (~p /\\ q)."""

    p.goal("!p:bool. !q:bool. ~(p = q) ==> (p /\\ ~q) \\/ (~p /\\ q)")
    p.fix("p q")
    p.assume("hne: ~(p = q)")
    with p.cases_on(EXCLUDED_MIDDLE, "p"):
        with p.case("hp: p"):
            with p.cases_on(EXCLUDED_MIDDLE, "q"):
                with p.case("hq: q"):
                    p.have("p_eq_T: p = T").by_thm(EQT_INTRO(p.fact("hp")))
                    p.have("q_eq_T: q = T").by_thm(EQT_INTRO(p.fact("hq")))
                    p.have("peq: p = q").by_thm(
                        TRANS(p.fact("p_eq_T"), SYM(p.fact("q_eq_T")))
                    )
                    p.absurd().by_conj("hne", "peq")
                with p.case("hnq: ~q"):
                    p.thus("(p /\\ ~q) \\/ (~p /\\ q)").by_disj(
                        CONJ(p.fact("hp"), p.fact("hnq"))
                    )
        with p.case("hnp: ~p"):
            with p.cases_on(EXCLUDED_MIDDLE, "q"):
                with p.case("hq: q"):
                    p.thus("(p /\\ ~q) \\/ (~p /\\ q)").by_disj(
                        CONJ(p.fact("hnp"), p.fact("hq"))
                    )
                with p.case("hnq: ~q"):
                    p.have("p_eq_F: p = F").by_thm(EQF_INTRO(p.fact("hnp")))
                    p.have("q_eq_F: q = F").by_thm(EQF_INTRO(p.fact("hnq")))
                    p.have("peq: p = q").by_thm(
                        TRANS(p.fact("p_eq_F"), SYM(p.fact("q_eq_F")))
                    )
                    p.absurd().by_conj("hne", "peq")


@proof
def HF_EXT_DIFF(p):
    """|- !s t. ~(s = t) ==>
          ?w. (In w s /\\ ~In w t) \\/ (~In w s /\\ In w t).

    HOL-level extensional discriminator for HF sets. This is the witness
    source for the inequality half of the mutual measured quote proof.
    """

    p.goal(
        "!s t. ~(s = t) ==> "
        "?w. (In w s /\\ ~(In w t)) \\/ (~(In w s) /\\ In w t)"
    )
    p.fix("s t")
    p.assume("hst_ne: ~(s = t)")
    with p.have("h_not_all: ~(!w. In w s = In w t)").proof():
        with p.suppose("hall: !w. In w s = In w t"):
            p.have("hst: s = t").by(IN_EXT, "s", "t", "hall")
            p.absurd().by_conj("hst_ne", "hst")
    diff_pred = p._parse("\\w:nat0. In w s = In w t")
    p.have("h_ex: ?w. ~(In w s = In w t)").by_thm(
        NOT_FORALL_TO_EX_NOT(p.fact("h_not_all"), diff_pred)
    )
    p.choose("w", "h_ex")
    p.have(
        "h_xor: (In w s /\\ ~(In w t)) \\/ (~(In w s) /\\ In w t)"
    ).by(BOOL_NEQ_XOR, "In w s", "In w t", "w_eq")
    p.thus("?w. (In w s /\\ ~(In w t)) \\/ (~(In w s) /\\ In w t)").by_witness(
        "w", "h_xor"
    )


# Mutual quote_hf induction measures found by `hf_induction_targets.py`.
#
# Membership decision recurses on `quote_hf_mem_measure x y = Insert x y`.
# Quote inequality uses the symmetric larger side of the two membership
# measures, matching the experiment's `Q(s,t) = max(Insert s t, Insert t s)`.
# The definition avoids adding a general max operator by selecting with
# `nat0_lt` directly.
QUOTE_HF_MEM_MEASURE_DEF, QUOTE_HF_MEM_MEASURE_AT = define_with_at(
    "quote_hf_mem_measure",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\x:nat0. \\y:nat0. Insert x y",
)

QUOTE_HF_NEQ_MEASURE_DEF, QUOTE_HF_NEQ_MEASURE_AT = define_with_at(
    "quote_hf_neq_measure",
    parse_type("nat0 -> nat0 -> nat0"),
    "\\s:nat0. \\t:nat0. "
    "COND_nat0 (nat0_lt (Insert s t) (Insert t s)) "
    "          (Insert t s) "
    "          (Insert s t)",
)


@proof
def QUOTE_HF_MEM_HEAD_NEQ_RAW_DECREASE(p):
    """Raw Ackermann bit-order obligation for the head-neq recursive call.

    This packages the two possible ``quote_hf_neq_measure`` branches as
    raw membership-measure decreases. Both are top-difference bit-order
    comparisons against ``Insert x y``.
    """

    p.goal(
        "!x y. ~(y = 0) /\\ ~(x = low_bit y) "
        "==> nat0_lt (quote_hf_mem_measure x (low_bit y)) "
        "            (quote_hf_mem_measure x y) "
        " /\\ nat0_lt (quote_hf_mem_measure (low_bit y) x) "
        "            (quote_hf_mem_measure x y)"
    )
    p.fix("x y")
    p.assume("(hy_nz,hx_ne): ~(y = 0) /\\ ~(x = low_bit y)")

    with p.have(
        "h_hi_lb: !i. nat0_lt (low_bit y) i "
        "==> bit i (set_bit x (low_bit y)) ==> bit i (set_bit x y)"
    ).proof():
        p.fix("i")
        p.assume("hlti: nat0_lt (low_bit y) i", "hbit: bit i (set_bit x (low_bit y))")
        with p.cases_on(EXCLUDED_MIDDLE, "i = x"):
            with p.case("hix: i = x"):
                p.have("h_x_T: bit x (set_bit x y) = T").by(
                    BIT_AT_SET_BIT_SAME, "x", "y"
                )
                p.have("h_x: bit x (set_bit x y)").by_thm(
                    EQT_ELIM(p.fact("h_x_T"))
                )
                p.thus("bit i (set_bit x y)").by_rewrite_of(
                    "h_x", [SYM(p.fact("hix"))]
                )
            with p.case("hix_ne: ~(i = x)"):
                with p.have("hxi_ne: ~(x = i)").proof():
                    with p.suppose("hxi: x = i"):
                        p.have("hix2: i = x").by_thm(SYM(p.fact("hxi")))
                        p.absurd().by_conj("hix_ne", "hix2")
                p.have(
                    "hbit_i_lb_eq: bit i (set_bit x (low_bit y)) "
                    "= bit i (low_bit y)"
                ).by(BIT_AT_SET_BIT_DIFF, "x", "i", "low_bit y", "hxi_ne")
                p.have("hbit_i_lb: bit i (low_bit y)").by_eq_mp(
                    "hbit_i_lb_eq", "hbit"
                )
                p.have("h_above_F: bit i (low_bit y) = F").by(
                    BIT_ABOVE_FALSE, "low_bit y", "i", "hlti"
                )
                p.absurd().by_thm(EQ_MP(p.fact("h_above_F"), p.fact("hbit_i_lb")))
    p.have("h_lb_left_F: bit (low_bit y) (set_bit x (low_bit y)) = F").by(
        BIT_AT_SET_BIT_OTHER_SELF_FALSE, "x", "low_bit y", "hx_ne"
    )
    p.have("h_lb_left_not: ~(bit (low_bit y) (set_bit x (low_bit y)))").by_thm(
        EQF_ELIM(p.fact("h_lb_left_F"))
    )
    p.have(
        "h_lb_right_eq: bit (low_bit y) (set_bit x y) = bit (low_bit y) y"
    ).by(BIT_AT_SET_BIT_DIFF, "x", "low_bit y", "y", "hx_ne")
    p.have("h_lb_y_T: bit (low_bit y) y = T").by(
        BIT_LOW_BIT, "y", "hy_nz"
    )
    p.have("h_lb_right_T: bit (low_bit y) (set_bit x y) = T").by_trans(
        "h_lb_right_eq", "h_lb_y_T"
    )
    p.have("h_lb_right: bit (low_bit y) (set_bit x y)").by_thm(
        EQT_ELIM(p.fact("h_lb_right_T"))
    )
    p.have(
        "h_left_raw: nat0_lt (set_bit x (low_bit y)) (set_bit x y)"
    ).by(
        BITWISE_LT_BY_TOP_DIFF,
        "low_bit y",
        "set_bit x (low_bit y)",
        "set_bit x y",
        CONJ(p.fact("h_hi_lb"), CONJ(p.fact("h_lb_left_not"), p.fact("h_lb_right"))),
    )

    with p.have(
        "h_hi_x: !i. nat0_lt x i "
        "==> bit i (set_bit (low_bit y) x) ==> bit i (set_bit x y)"
    ).proof():
        p.fix("i")
        p.assume("hlti: nat0_lt x i", "hbit: bit i (set_bit (low_bit y) x)")
        with p.cases_on(EXCLUDED_MIDDLE, "i = low_bit y"):
            with p.case("hi_lb: i = low_bit y"):
                p.have("h_x_lt_lb: nat0_lt x (low_bit y)").by_rewrite_of(
                    "hlti", ["hi_lb"]
                )
                p.have("h_lb_y_T2: bit (low_bit y) y = T").by(
                    BIT_LOW_BIT, "y", "hy_nz"
                )
                p.have("h_lb_y: bit (low_bit y) y").by_thm(
                    EQT_ELIM(p.fact("h_lb_y_T2"))
                )
                p.have(
                    "h_lb_setx_y_eq: bit (low_bit y) (set_bit x y) "
                    "= bit (low_bit y) y"
                ).by(BIT_AT_SET_BIT_DIFF, "x", "low_bit y", "y", "hx_ne")
                p.have("h_lb_setx_y: bit (low_bit y) (set_bit x y)").by_eq_mp(
                    SYM(p.fact("h_lb_setx_y_eq")), "h_lb_y"
                )
                p.thus("bit i (set_bit x y)").by_rewrite_of(
                    "h_lb_setx_y", ["hi_lb"]
                )
            with p.case("hi_lb_ne: ~(i = low_bit y)"):
                with p.have("h_lb_i_ne: ~(low_bit y = i)").proof():
                    with p.suppose("h_lb_i: low_bit y = i"):
                        p.have("hi_lb2: i = low_bit y").by_thm(SYM(p.fact("h_lb_i")))
                        p.absurd().by_conj("hi_lb_ne", "hi_lb2")
                p.have(
                    "hbit_i_x_eq: bit i (set_bit (low_bit y) x) = bit i x"
                ).by(BIT_AT_SET_BIT_DIFF, "low_bit y", "i", "x", "h_lb_i_ne")
                p.have("hbit_i_x: bit i x").by_eq_mp(
                    "hbit_i_x_eq", "hbit"
                )
                p.have("h_above_F: bit i x = F").by(
                    BIT_ABOVE_FALSE, "x", "i", "hlti"
                )
                p.absurd().by_thm(EQ_MP(p.fact("h_above_F"), p.fact("hbit_i_x")))
    with p.have("h_lb_x_ne: ~(low_bit y = x)").proof():
        with p.suppose("h_lb_x: low_bit y = x"):
            p.have("h_x_lb: x = low_bit y").by_thm(SYM(p.fact("h_lb_x")))
            p.absurd().by_conj("hx_ne", "h_x_lb")
    p.have("h_x_left_F: bit x (set_bit (low_bit y) x) = F").by(
        BIT_AT_SET_BIT_OTHER_SELF_FALSE, "low_bit y", "x", "h_lb_x_ne"
    )
    p.have("h_x_left_not: ~(bit x (set_bit (low_bit y) x))").by_thm(
        EQF_ELIM(p.fact("h_x_left_F"))
    )
    p.have("h_x_right_T: bit x (set_bit x y) = T").by(
        BIT_AT_SET_BIT_SAME, "x", "y"
    )
    p.have("h_x_right: bit x (set_bit x y)").by_thm(
        EQT_ELIM(p.fact("h_x_right_T"))
    )
    p.have(
        "h_right_raw: nat0_lt (set_bit (low_bit y) x) (set_bit x y)"
    ).by(
        BITWISE_LT_BY_TOP_DIFF,
        "x",
        "set_bit (low_bit y) x",
        "set_bit x y",
        CONJ(p.fact("h_hi_x"), CONJ(p.fact("h_x_left_not"), p.fact("h_x_right"))),
    )

    p.have(
        "h_left: nat0_lt (quote_hf_mem_measure x (low_bit y)) "
        "                (quote_hf_mem_measure x y)"
    ).by_rewrite_of("h_left_raw", [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT])
    p.have(
        "h_right: nat0_lt (quote_hf_mem_measure (low_bit y) x) "
        "                 (quote_hf_mem_measure x y)"
    ).by_rewrite_of("h_right_raw", [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT])
    p.thus(
        "nat0_lt (quote_hf_mem_measure x (low_bit y)) "
        "        (quote_hf_mem_measure x y) "
        "/\\ nat0_lt (quote_hf_mem_measure (low_bit y) x) "
        "        (quote_hf_mem_measure x y)"
    ).by_thm(CONJ(p.fact("h_left"), p.fact("h_right")))


@proof
def QUOTE_HF_MEM_MEASURE_CLEAR_LOW_DECREASE(p):
    """|- !x y. ~(y = 0) /\\ ~(x = low_bit y)
          ==> nat0_lt (quote_hf_mem_measure x (clear_low y))
                      (quote_hf_mem_measure x y).

    This is the measured replacement for the negative-membership tail call:
    once the current low bit of ``y`` is known not to be ``x``, inserting
    ``x`` into ``clear_low y`` is still strictly below inserting ``x`` into
    ``y``.  The proof avoids list encodings; it uses the missing low bit as
    the strict-growth witness for ``set_bit``.
    """

    p.goal(
        "!x y. ~(y = 0) /\\ ~(x = low_bit y) "
        "==> nat0_lt (quote_hf_mem_measure x (clear_low y)) "
        "            (quote_hf_mem_measure x y)"
    )
    p.fix("x y")
    p.assume("(hy_nz,hx_ne): ~(y = 0) /\\ ~(x = low_bit y)")
    p.have("h_low_cl_F: bit (low_bit y) (clear_low y) = F").by(
        BIT_CLEAR_LOW_LOW_BIT, "y", "hy_nz"
    )
    p.have(
        "h_low_setx_cl: bit (low_bit y) (set_bit x (clear_low y)) "
        "= bit (low_bit y) (clear_low y)"
    ).by(BIT_AT_SET_BIT_DIFF, "x", "low_bit y", "clear_low y", "hx_ne")
    p.have("h_low_setx_cl_F: bit (low_bit y) (set_bit x (clear_low y)) = F").by_trans(
        "h_low_setx_cl", "h_low_cl_F"
    )
    p.have("h_low_not: ~(bit (low_bit y) (set_bit x (clear_low y)))").by_thm(
        EQF_ELIM(p.fact("h_low_setx_cl_F"))
    )
    p.have(
        "h_lt_raw: nat0_lt (set_bit x (clear_low y)) "
        "                   (set_bit (low_bit y) (set_bit x (clear_low y)))"
    ).by(SET_BIT_GT_NEW, "low_bit y", "set_bit x (clear_low y)", "h_low_not")
    p.have("h_y_recon: y = set_bit (low_bit y) (clear_low y)").by(
        INSERT_LOW_BIT_CLEAR_LOW, "y", "hy_nz"
    )
    p.have(
        "h_comm: set_bit x (set_bit (low_bit y) (clear_low y)) "
        "= set_bit (low_bit y) (set_bit x (clear_low y))"
    ).by(SET_BIT_COMMUTE_DIFF, "x", "low_bit y", "clear_low y", "hx_ne")
    p.have(
        "h_setx_y: set_bit x y = set_bit (low_bit y) (set_bit x (clear_low y))"
    ).by_rewrite_of("h_comm", [SYM(p.fact("h_y_recon"))])
    p.thus(
        "nat0_lt (quote_hf_mem_measure x (clear_low y)) "
        "        (quote_hf_mem_measure x y)"
    ).by_rewrite_of("h_lt_raw", [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT, "h_setx_y"])


@proof
def QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE(p):
    """|- !x y. ~(y = 0) /\\ ~(x = low_bit y)
          ==> nat0_lt (quote_hf_neq_measure x (low_bit y))
                      (quote_hf_mem_measure x y).

    This is the recursive-call bound for the membership miss branch.  To
    use HF3 on ``x`` versus the current head ``low_bit y``, membership
    decision needs quoted inequality for that pair; this lemma says that
    inequality call is below the current membership measure.

    The remaining arithmetic proof is bit-order bookkeeping for
    ``max(Insert x (low_bit y), Insert (low_bit y) x) < Insert x y`` under
    ``y != 0`` and ``x != low_bit y``.
    """

    p.goal(
        "!x y. ~(y = 0) /\\ ~(x = low_bit y) "
        "==> nat0_lt (quote_hf_neq_measure x (low_bit y)) "
        "            (quote_hf_mem_measure x y)"
    )
    p.fix("x y")
    p.assume("(hy_nz,hx_ne): ~(y = 0) /\\ ~(x = low_bit y)")
    p.have(
        "h_raw: nat0_lt (quote_hf_mem_measure x (low_bit y)) "
        "                  (quote_hf_mem_measure x y) "
        "/\\ nat0_lt (quote_hf_mem_measure (low_bit y) x) "
        "                  (quote_hf_mem_measure x y)"
    ).by(
        QUOTE_HF_MEM_HEAD_NEQ_RAW_DECREASE,
        "x",
        "y",
        CONJ(p.fact("hy_nz"), p.fact("hx_ne")),
    )
    p.split("h_raw", "(h_x_lb,h_lb_x)")
    branch = "nat0_lt (Insert x (low_bit y)) (Insert (low_bit y) x)"
    with p.cases_on(EXCLUDED_MIDDLE, branch):
        with p.case(
            "h_branch: nat0_lt (Insert x (low_bit y)) (Insert (low_bit y) x)"
        ):
            p.have(
                "h_branch_eq: nat0_lt (Insert x (low_bit y)) "
                "(Insert (low_bit y) x) = T"
            ).by_thm(EQT_INTRO(p.fact("h_branch")))
            p.have(
                "h_lb_x_insert: nat0_lt (Insert (low_bit y) x) "
                "                         (quote_hf_mem_measure x y)"
            ).by_rewrite_of("h_lb_x", [QUOTE_HF_MEM_MEASURE_AT])
            p.thus(
                "nat0_lt (quote_hf_neq_measure x (low_bit y)) "
                "        (quote_hf_mem_measure x y)"
            ).by_rewrite_of(
                "h_lb_x_insert",
                [QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_T_NAT0],
            )
        with p.case(
            "h_branch: ~(nat0_lt (Insert x (low_bit y)) "
            "(Insert (low_bit y) x))"
        ):
            p.have(
                "h_branch_eq: nat0_lt (Insert x (low_bit y)) "
                "(Insert (low_bit y) x) = F"
            ).by_thm(EQF_INTRO(p.fact("h_branch")))
            p.have(
                "h_x_lb_insert: nat0_lt (Insert x (low_bit y)) "
                "                         (quote_hf_mem_measure x y)"
            ).by_rewrite_of("h_x_lb", [QUOTE_HF_MEM_MEASURE_AT])
            p.thus(
                "nat0_lt (quote_hf_neq_measure x (low_bit y)) "
                "        (quote_hf_mem_measure x y)"
            ).by_rewrite_of(
                "h_x_lb_insert",
                [QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_F_NAT0],
            )


@proof
def QUOTE_HF_NEQ_MEASURE_LT_FROM_BOTH(p):
    """|- !s t n. nat0_lt (quote_hf_mem_measure s t) n
              /\\ nat0_lt (quote_hf_mem_measure t s) n
          ==> nat0_lt (quote_hf_neq_measure s t) n.

    ``quote_hf_neq_measure`` is a two-way maximum encoded by ``COND_nat0``.
    This lemma packages the branch split so later strong-induction decreases
    only need to prove the two raw membership bounds.
    """

    p.goal(
        "!s t n. nat0_lt (quote_hf_mem_measure s t) n "
        "/\\ nat0_lt (quote_hf_mem_measure t s) n "
        "==> nat0_lt (quote_hf_neq_measure s t) n"
    )
    p.fix("s t n")
    p.assume(
        "(hst,hts): nat0_lt (quote_hf_mem_measure s t) n "
        "/\\ nat0_lt (quote_hf_mem_measure t s) n"
    )
    with p.cases_on(EXCLUDED_MIDDLE, "nat0_lt (Insert s t) (Insert t s)"):
        with p.case("h_branch: nat0_lt (Insert s t) (Insert t s)"):
            p.have("h_branch_eq: nat0_lt (Insert s t) (Insert t s) = T").by_thm(
                EQT_INTRO(p.fact("h_branch"))
            )
            p.have("hts_insert: nat0_lt (Insert t s) n").by_rewrite_of(
                "hts", [QUOTE_HF_MEM_MEASURE_AT]
            )
            p.thus("nat0_lt (quote_hf_neq_measure s t) n").by_rewrite_of(
                "hts_insert",
                [QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_T_NAT0],
            )
        with p.case("h_branch: ~(nat0_lt (Insert s t) (Insert t s))"):
            p.have("h_branch_eq: nat0_lt (Insert s t) (Insert t s) = F").by_thm(
                EQF_INTRO(p.fact("h_branch"))
            )
            p.have("hst_insert: nat0_lt (Insert s t) n").by_rewrite_of(
                "hst", [QUOTE_HF_MEM_MEASURE_AT]
            )
            p.thus("nat0_lt (quote_hf_neq_measure s t) n").by_rewrite_of(
                "hst_insert",
                [QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_F_NAT0],
            )


@proof
def QUOTE_HF_NEQ_MEASURE_LT_FROM_FOUR_MEM_BOUNDS(p):
    """|- !a b s t.
          (nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure s t)
           /\\ nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure t s))
          /\\
          (nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure s t)
           /\\ nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure t s))
          ==> nat0_lt (quote_hf_neq_measure a b) (quote_hf_neq_measure s t).

    This is the ``max`` bookkeeping helper for neq decreases.  Concrete
    recursive calls only need to prove four membership-measure inequalities;
    this lemma handles both ``COND_nat0`` selectors.
    """

    p.goal(
        "!a b s t. "
        "(nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure s t) "
        " /\\ nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure t s)) "
        "/\\ "
        "(nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure s t) "
        " /\\ nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure t s)) "
        "==> nat0_lt (quote_hf_neq_measure a b) (quote_hf_neq_measure s t)"
    )
    p.fix("a b s t")
    p.assume(
        "((hab_st,hab_ts),(hba_st,hba_ts)): "
        "(nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure s t) "
        " /\\ nat0_lt (quote_hf_mem_measure a b) (quote_hf_mem_measure t s)) "
        "/\\ "
        "(nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure s t) "
        " /\\ nat0_lt (quote_hf_mem_measure b a) (quote_hf_mem_measure t s))"
    )
    with p.cases_on(EXCLUDED_MIDDLE, "nat0_lt (Insert s t) (Insert t s)"):
        with p.case("h_branch: nat0_lt (Insert s t) (Insert t s)"):
            p.have("h_branch_eq: nat0_lt (Insert s t) (Insert t s) = T").by_thm(
                EQT_INTRO(p.fact("h_branch"))
            )
            p.have(
                "h_ab_q: nat0_lt (quote_hf_mem_measure a b) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "hab_ts",
                [QUOTE_HF_MEM_MEASURE_AT, QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_T_NAT0],
            )
            p.have(
                "h_ba_q: nat0_lt (quote_hf_mem_measure b a) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "hba_ts",
                [QUOTE_HF_MEM_MEASURE_AT, QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_T_NAT0],
            )
            p.have(
                "h_both_q: nat0_lt (quote_hf_mem_measure a b) "
                "                    (quote_hf_neq_measure s t) "
                "/\\ nat0_lt (quote_hf_mem_measure b a) "
                "          (quote_hf_neq_measure s t)"
            ).by_thm(CONJ(p.fact("h_ab_q"), p.fact("h_ba_q")))
            p.thus("nat0_lt (quote_hf_neq_measure a b) (quote_hf_neq_measure s t)").by(
                QUOTE_HF_NEQ_MEASURE_LT_FROM_BOTH,
                "a",
                "b",
                "quote_hf_neq_measure s t",
                "h_both_q",
            )
        with p.case("h_branch: ~(nat0_lt (Insert s t) (Insert t s))"):
            p.have("h_branch_eq: nat0_lt (Insert s t) (Insert t s) = F").by_thm(
                EQF_INTRO(p.fact("h_branch"))
            )
            p.have(
                "h_ab_q: nat0_lt (quote_hf_mem_measure a b) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "hab_st",
                [QUOTE_HF_MEM_MEASURE_AT, QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_F_NAT0],
            )
            p.have(
                "h_ba_q: nat0_lt (quote_hf_mem_measure b a) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "hba_st",
                [QUOTE_HF_MEM_MEASURE_AT, QUOTE_HF_NEQ_MEASURE_AT, "h_branch_eq", COND_F_NAT0],
            )
            p.have(
                "h_both_q: nat0_lt (quote_hf_mem_measure a b) "
                "                    (quote_hf_neq_measure s t) "
                "/\\ nat0_lt (quote_hf_mem_measure b a) "
                "          (quote_hf_neq_measure s t)"
            ).by_thm(CONJ(p.fact("h_ab_q"), p.fact("h_ba_q")))
            p.thus("nat0_lt (quote_hf_neq_measure a b) (quote_hf_neq_measure s t)").by(
                QUOTE_HF_NEQ_MEASURE_LT_FROM_BOTH,
                "a",
                "b",
                "quote_hf_neq_measure s t",
                "h_both_q",
            )


@proof
def QUOTE_HF_NEQ_MEASURE_SYM(p):
    """|- !s t. quote_hf_neq_measure s t = quote_hf_neq_measure t s."""

    p.goal("!s t. quote_hf_neq_measure s t = quote_hf_neq_measure t s")
    p.fix("s t")
    with p.cases_on(EXCLUDED_MIDDLE, "nat0_lt (Insert s t) (Insert t s)"):
        with p.case("hst: nat0_lt (Insert s t) (Insert t s)"):
            p.have("hst_eq: nat0_lt (Insert s t) (Insert t s) = T").by_thm(
                EQT_INTRO(p.fact("hst"))
            )
            p.have("hts_not: ~(nat0_lt (Insert t s) (Insert s t))").by(
                NAT0_LT_ASYM, "Insert s t", "Insert t s", "hst"
            )
            p.have("hts_eq: nat0_lt (Insert t s) (Insert s t) = F").by_thm(
                EQF_INTRO(p.fact("hts_not"))
            )
            p.thus("quote_hf_neq_measure s t = quote_hf_neq_measure t s").by_rewrite(
                [QUOTE_HF_NEQ_MEASURE_AT, "hst_eq", "hts_eq", COND_T_NAT0, COND_F_NAT0]
            )
        with p.case("hst_not: ~(nat0_lt (Insert s t) (Insert t s))"):
            p.have("hst_eq: nat0_lt (Insert s t) (Insert t s) = F").by_thm(
                EQF_INTRO(p.fact("hst_not"))
            )
            with p.cases_on(EXCLUDED_MIDDLE, "nat0_lt (Insert t s) (Insert s t)"):
                with p.case("hts: nat0_lt (Insert t s) (Insert s t)"):
                    p.have("hts_eq: nat0_lt (Insert t s) (Insert s t) = T").by_thm(
                        EQT_INTRO(p.fact("hts"))
                    )
                    p.thus(
                        "quote_hf_neq_measure s t = quote_hf_neq_measure t s"
                    ).by_rewrite(
                        [
                            QUOTE_HF_NEQ_MEASURE_AT,
                            "hst_eq",
                            "hts_eq",
                            COND_T_NAT0,
                            COND_F_NAT0,
                        ]
                    )
                with p.case("hts_not: ~(nat0_lt (Insert t s) (Insert s t))"):
                    p.have("hts_eq: nat0_lt (Insert t s) (Insert s t) = F").by_thm(
                        EQF_INTRO(p.fact("hts_not"))
                    )
                    with p.have("h_eq: Insert s t = Insert t s").proof():
                        with p.cases_on(EXCLUDED_MIDDLE, "Insert s t = Insert t s"):
                            with p.case("heq: Insert s t = Insert t s"):
                                p.thus("Insert s t = Insert t s").by_thm(
                                    p.fact("heq")
                                )
                            with p.case("hne: ~(Insert s t = Insert t s)"):
                                p.have(
                                    "h_total: nat0_lt (Insert s t) (Insert t s) "
                                    "\\/ nat0_lt (Insert t s) (Insert s t)"
                                ).by(
                                    NAT0_LT_TOTAL_NEQ,
                                    "Insert s t",
                                    "Insert t s",
                                    "hne",
                                )
                                with p.cases_on("h_total"):
                                    with p.case("hbad: nat0_lt (Insert s t) (Insert t s)"):
                                        p.absurd().by_conj("hst_not", "hbad")
                                    with p.case("hbad: nat0_lt (Insert t s) (Insert s t)"):
                                        p.absurd().by_conj("hts_not", "hbad")
                    p.thus(
                        "quote_hf_neq_measure s t = quote_hf_neq_measure t s"
                    ).by_rewrite(
                        [
                            QUOTE_HF_NEQ_MEASURE_AT,
                            "hst_eq",
                            "hts_eq",
                            "h_eq",
                            COND_F_NAT0,
                        ]
                    )


@proof
def NAT0_LT_SELF_INSERT_SELF(p):
    """|- !a b. nat0_lt a (Insert a b)."""

    p.goal("!a b. nat0_lt a (Insert a b)")
    p.fix("a b")
    with p.have(
        "h_hi: !i. nat0_lt a i ==> bit i a ==> bit i (set_bit a b)"
    ).proof():
        p.fix("i")
        p.assume("hai: nat0_lt a i", "hbit: bit i a")
        p.have("h_i_a_F: bit i a = F").by(BIT_ABOVE_FALSE, "a", "i", "hai")
        p.absurd().by_thm(EQ_MP(p.fact("h_i_a_F"), p.fact("hbit")))
    p.have("h_a_a_F: bit a a = F").by(BIT_SELF_FALSE, "a")
    p.have("h_not_a_a: ~(bit a a)").by_thm(EQF_ELIM(p.fact("h_a_a_F")))
    p.have("h_a_rhs_T: bit a (set_bit a b) = T").by(
        BIT_AT_SET_BIT_SAME, "a", "b"
    )
    p.have("h_a_rhs: bit a (set_bit a b)").by_thm(
        EQT_ELIM(p.fact("h_a_rhs_T"))
    )
    p.have("h_raw: nat0_lt a (set_bit a b)").by(
        BITWISE_LT_BY_TOP_DIFF,
        "a",
        "a",
        "set_bit a b",
        CONJ(p.fact("h_hi"), CONJ(p.fact("h_not_a_a"), p.fact("h_a_rhs"))),
    )
    p.thus("nat0_lt a (Insert a b)").by_rewrite_of("h_raw", [INSERT_AT])


@proof
def QUOTE_HF_EXT_DIFF_LEFT_ABSENT_TRUE_BRANCH(p):
    """|- !w s t. In w s /\\ ~In w t
                  /\\ nat0_lt (Insert s t) (Insert t s)
          ==> nat0_lt (quote_hf_mem_measure w t) (Insert t s).

    In the true selector branch Q(s,t)=Insert t s.  The absent recursive
    membership call M(w,t) is below that side by top-difference at bit t.
    """

    p.goal(
        "!w s t. In w s /\\ ~(In w t) "
        "/\\ nat0_lt (Insert s t) (Insert t s) "
        "==> nat0_lt (quote_hf_mem_measure w t) (Insert t s)"
    )
    p.fix("w s t")
    p.assume(
        "(hws, hnwt, hbranch): In w s /\\ ~(In w t) "
        "/\\ nat0_lt (Insert s t) (Insert t s)"
    )
    p.have("hws_bit: bit w s").by_rewrite_of("hws", [IN_AT])
    with p.have("h_not_bit_t_s: ~(bit t s)").proof():
        with p.suppose("hts_bit: bit t s"):
            p.have("h_set_ts_s: set_bit t s = s").by(
                SET_BIT_PRESENT_ID, "t", "s", "hts_bit"
            )
            p.have("h_insert_ts_s: Insert t s = s").by_rewrite_of(
                "h_set_ts_s", [INSERT_AT]
            )
            p.have("h_s_lt_insert_st: nat0_lt s (Insert s t)").by(
                NAT0_LT_SELF_INSERT_SELF, "s", "t"
            )
            p.have("h_insert_st_lt_s: nat0_lt (Insert s t) s").by_rewrite_of(
                "hbranch", ["h_insert_ts_s"]
            )
            p.have("h_s_lt_s: nat0_lt s s").by(
                NAT0_LT_TRANS, "s", "Insert s t", "s",
                "h_s_lt_insert_st", "h_insert_st_lt_s",
            )
            p.have("h_not_s_lt_s: ~(nat0_lt s s)").by(NAT0_LT_NOT_REFL, "s")
            p.absurd().by_conj("h_not_s_lt_s", "h_s_lt_s")
    with p.have("h_w_ne_t: ~(w = t)").proof():
        with p.suppose("hwt: w = t"):
            p.have("hts_bit: bit t s").by_rewrite_of("hws_bit", ["hwt"])
            p.absurd().by_conj("h_not_bit_t_s", "hts_bit")
    with p.have("h_t_ne_w: ~(t = w)").proof():
        with p.suppose("htw: t = w"):
            p.have("hwt: w = t").by_thm(SYM(p.fact("htw")))
            p.absurd().by_conj("h_w_ne_t", "hwt")
    with p.have(
        "h_hi: !i. nat0_lt t i ==> bit i (set_bit w t) "
        "==> bit i (set_bit t s)"
    ).proof():
        p.fix("i")
        p.assume("hti: nat0_lt t i", "hbit: bit i (set_bit w t)")
        with p.cases_on(EXCLUDED_MIDDLE, "i = w"):
            with p.case("hiw: i = w"):
                p.have("h_w_rhs_eq: bit w (set_bit t s) = bit w s").by(
                    BIT_AT_SET_BIT_DIFF, "t", "w", "s", "h_t_ne_w"
                )
                p.have("h_w_rhs: bit w (set_bit t s)").by_eq_mp(
                    SYM(p.fact("h_w_rhs_eq")), "hws_bit"
                )
                p.thus("bit i (set_bit t s)").by_rewrite_of(
                    "h_w_rhs", [SYM(p.fact("hiw"))]
                )
            with p.case("hiw_ne: ~(i = w)"):
                with p.have("h_w_i_ne: ~(w = i)").proof():
                    with p.suppose("hwi: w = i"):
                        p.have("hiw2: i = w").by_thm(SYM(p.fact("hwi")))
                        p.absurd().by_conj("hiw_ne", "hiw2")
                p.have("hbit_i_t_eq: bit i (set_bit w t) = bit i t").by(
                    BIT_AT_SET_BIT_DIFF, "w", "i", "t", "h_w_i_ne"
                )
                p.have("hbit_i_t: bit i t").by_eq_mp("hbit_i_t_eq", "hbit")
                p.have("h_i_t_F: bit i t = F").by(
                    BIT_ABOVE_FALSE, "t", "i", "hti"
                )
                p.absurd().by_thm(EQ_MP(p.fact("h_i_t_F"), p.fact("hbit_i_t")))
    p.have("h_t_left_eq: bit t (set_bit w t) = bit t t").by(
        BIT_AT_SET_BIT_DIFF, "w", "t", "t", "h_w_ne_t"
    )
    p.have("h_t_t_F: bit t t = F").by(BIT_SELF_FALSE, "t")
    p.have("h_t_left_F: bit t (set_bit w t) = F").by_trans(
        "h_t_left_eq", "h_t_t_F"
    )
    p.have("h_t_left_not: ~(bit t (set_bit w t))").by_thm(
        EQF_ELIM(p.fact("h_t_left_F"))
    )
    p.have("h_t_right_T: bit t (set_bit t s) = T").by(
        BIT_AT_SET_BIT_SAME, "t", "s"
    )
    p.have("h_t_right: bit t (set_bit t s)").by_thm(
        EQT_ELIM(p.fact("h_t_right_T"))
    )
    p.have("h_raw: nat0_lt (set_bit w t) (set_bit t s)").by(
        BITWISE_LT_BY_TOP_DIFF,
        "t",
        "set_bit w t",
        "set_bit t s",
        CONJ(p.fact("h_hi"), CONJ(p.fact("h_t_left_not"), p.fact("h_t_right"))),
    )
    p.thus("nat0_lt (quote_hf_mem_measure w t) (Insert t s)").by_rewrite_of(
        "h_raw", [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT]
    )


@proof
def QUOTE_HF_EXT_DIFF_LEFT_ABSENT_FALSE_BRANCH(p):
    """|- !w s t. In w s /\\ ~In w t
                  /\\ ~nat0_lt (Insert s t) (Insert t s)
          ==> nat0_lt (quote_hf_mem_measure w t) (Insert s t).

    In the false selector branch Q(s,t)=Insert s t.  The absent recursive
    membership call M(w,t) is below that side by top-difference at bit s.
    """

    p.goal(
        "!w s t. In w s /\\ ~(In w t) "
        "/\\ ~(nat0_lt (Insert s t) (Insert t s)) "
        "==> nat0_lt (quote_hf_mem_measure w t) (Insert s t)"
    )
    p.fix("w s t")
    p.assume(
        "(hws, hnwt, hbranch): In w s /\\ ~(In w t) "
        "/\\ ~(nat0_lt (Insert s t) (Insert t s))"
    )
    p.have("h_w_lt_s: nat0_lt w s").by(IN_LT, "s", "w", "hws")
    with p.have("h_w_ne_s: ~(w = s)").proof():
        with p.suppose("hws_eq: w = s"):
            p.have("h_s_lt_s: nat0_lt s s").by_rewrite_of(
                "h_w_lt_s", ["hws_eq"]
            )
            p.have("h_not_s_lt_s: ~(nat0_lt s s)").by(NAT0_LT_NOT_REFL, "s")
            p.absurd().by_conj("h_not_s_lt_s", "h_s_lt_s")
    with p.have("h_s_ne_w: ~(s = w)").proof():
        with p.suppose("hsw: s = w"):
            p.have("hws_eq: w = s").by_thm(SYM(p.fact("hsw")))
            p.absurd().by_conj("h_w_ne_s", "hws_eq")
    with p.have("h_not_bit_s_t: ~(bit s t)").proof():
        with p.suppose("hst_bit: bit s t"):
            p.have("h_set_st_t: set_bit s t = t").by(
                SET_BIT_PRESENT_ID, "s", "t", "hst_bit"
            )
            p.have("h_insert_st_t: Insert s t = t").by_rewrite_of(
                "h_set_st_t", [INSERT_AT]
            )
            p.have("h_t_lt_insert_ts: nat0_lt t (Insert t s)").by(
                NAT0_LT_SELF_INSERT_SELF, "t", "s"
            )
            p.have("h_branch_true: nat0_lt (Insert s t) (Insert t s)").by_rewrite_of(
                "h_t_lt_insert_ts", ["h_insert_st_t"]
            )
            p.absurd().by_conj("hbranch", "h_branch_true")
    p.have("h_s_t_F: bit s t = F").by_thm(EQF_INTRO(p.fact("h_not_bit_s_t")))
    with p.have(
        "h_hi: !i. nat0_lt s i ==> bit i (set_bit w t) "
        "==> bit i (set_bit s t)"
    ).proof():
        p.fix("i")
        p.assume("hsi: nat0_lt s i", "hbit: bit i (set_bit w t)")
        with p.cases_on(EXCLUDED_MIDDLE, "i = w"):
            with p.case("hiw: i = w"):
                p.have("h_s_lt_w: nat0_lt s w").by_rewrite_of("hsi", ["hiw"])
                p.have("h_w_lt_w: nat0_lt w w").by(
                    NAT0_LT_TRANS, "w", "s", "w", "h_w_lt_s", "h_s_lt_w"
                )
                p.have("h_not_w_lt_w: ~(nat0_lt w w)").by(NAT0_LT_NOT_REFL, "w")
                p.absurd().by_conj("h_not_w_lt_w", "h_w_lt_w")
            with p.case("hiw_ne: ~(i = w)"):
                with p.have("h_w_i_ne: ~(w = i)").proof():
                    with p.suppose("hwi: w = i"):
                        p.have("hiw2: i = w").by_thm(SYM(p.fact("hwi")))
                        p.absurd().by_conj("hiw_ne", "hiw2")
                with p.have("h_s_i_ne: ~(s = i)").proof():
                    with p.suppose("hsi_eq: s = i"):
                        p.have("h_s_lt_s: nat0_lt s s").by_rewrite_of(
                            "hsi", [SYM(p.fact("hsi_eq"))]
                        )
                        p.have("h_not_s_lt_s: ~(nat0_lt s s)").by(
                            NAT0_LT_NOT_REFL, "s"
                        )
                        p.absurd().by_conj("h_not_s_lt_s", "h_s_lt_s")
                p.have("hbit_i_t_eq: bit i (set_bit w t) = bit i t").by(
                    BIT_AT_SET_BIT_DIFF, "w", "i", "t", "h_w_i_ne"
                )
                p.have("hbit_i_t: bit i t").by_eq_mp("hbit_i_t_eq", "hbit")
                p.have("hbit_i_rhs_eq: bit i (set_bit s t) = bit i t").by(
                    BIT_AT_SET_BIT_DIFF, "s", "i", "t", "h_s_i_ne"
                )
                p.thus("bit i (set_bit s t)").by_eq_mp(
                    SYM(p.fact("hbit_i_rhs_eq")), "hbit_i_t"
                )
    p.have("h_s_left_eq: bit s (set_bit w t) = bit s t").by(
        BIT_AT_SET_BIT_DIFF, "w", "s", "t", "h_w_ne_s"
    )
    p.have("h_s_left_F: bit s (set_bit w t) = F").by_trans(
        "h_s_left_eq", "h_s_t_F"
    )
    p.have("h_s_left_not: ~(bit s (set_bit w t))").by_thm(
        EQF_ELIM(p.fact("h_s_left_F"))
    )
    p.have("h_s_right_T: bit s (set_bit s t) = T").by(
        BIT_AT_SET_BIT_SAME, "s", "t"
    )
    p.have("h_s_right: bit s (set_bit s t)").by_thm(
        EQT_ELIM(p.fact("h_s_right_T"))
    )
    p.have("h_raw: nat0_lt (set_bit w t) (set_bit s t)").by(
        BITWISE_LT_BY_TOP_DIFF,
        "s",
        "set_bit w t",
        "set_bit s t",
        CONJ(p.fact("h_hi"), CONJ(p.fact("h_s_left_not"), p.fact("h_s_right"))),
    )
    p.thus("nat0_lt (quote_hf_mem_measure w t) (Insert s t)").by_rewrite_of(
        "h_raw", [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT]
    )


@proof
def QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES(p):
    """|- !w s t. In w s /\\ ~In w t ==>
          nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t)
       /\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t).

    Decrease package for the extensional witness branch where ``w`` is
    present on the left and absent on the right.

    Proof plan:
      * ``M(w,s) = s`` by ``SET_BIT_PRESENT_ID``.
      * ``s < Q(s,t)`` by a top-difference split on whether ``s`` is
        already a bit of ``t``.
      * ``M(w,t) < Q(s,t)`` by top-difference at ``s`` when ``s`` is
        absent from ``t``; otherwise at ``t`` against ``Insert t s``.
    """

    p.goal(
        "!w s t. In w s /\\ ~(In w t) ==> "
        "nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t) "
        "/\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t)"
    )
    p.fix("w s t")
    p.assume("(hws, hnwt): In w s /\\ ~(In w t)")
    p.have("hws_bit: bit w s").by_rewrite_of("hws", [IN_AT])
    p.have("h_set_ws_s: set_bit w s = s").by(
        SET_BIT_PRESENT_ID, "w", "s", "hws_bit"
    )
    p.have("h_mws_s: quote_hf_mem_measure w s = s").by_rewrite(
        [QUOTE_HF_MEM_MEASURE_AT, INSERT_AT, "h_set_ws_s"]
    )
    p.have("h_s_lt_st: nat0_lt s (Insert s t)").by(
        NAT0_LT_SELF_INSERT_SELF, "s", "t"
    )
    with p.cases_on(EXCLUDED_MIDDLE, "nat0_lt (Insert s t) (Insert t s)"):
        with p.case("hbranch: nat0_lt (Insert s t) (Insert t s)"):
            p.have("hbranch_eq: nat0_lt (Insert s t) (Insert t s) = T").by_thm(
                EQT_INTRO(p.fact("hbranch"))
            )
            p.have("h_s_lt_ts: nat0_lt s (Insert t s)").by(
                NAT0_LT_TRANS, "s", "Insert s t", "Insert t s",
                "h_s_lt_st", "hbranch",
            )
            p.have(
                "h_ws_q: nat0_lt (quote_hf_mem_measure w s) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "h_s_lt_ts",
                [QUOTE_HF_NEQ_MEASURE_AT, "hbranch_eq", COND_T_NAT0, "h_mws_s"],
            )
            p.have(
                "h_wt_ts: nat0_lt (quote_hf_mem_measure w t) (Insert t s)"
            ).by(
                QUOTE_HF_EXT_DIFF_LEFT_ABSENT_TRUE_BRANCH,
                "w",
                "s",
                "t",
                CONJ(p.fact("hws"), CONJ(p.fact("hnwt"), p.fact("hbranch"))),
            )
            p.have(
                "h_wt_q: nat0_lt (quote_hf_mem_measure w t) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "h_wt_ts",
                [QUOTE_HF_NEQ_MEASURE_AT, "hbranch_eq", COND_T_NAT0],
            )
            p.thus(
                "nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t) "
                "/\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t)"
            ).by_thm(CONJ(p.fact("h_ws_q"), p.fact("h_wt_q")))
        with p.case("hbranch: ~(nat0_lt (Insert s t) (Insert t s))"):
            p.have("hbranch_eq: nat0_lt (Insert s t) (Insert t s) = F").by_thm(
                EQF_INTRO(p.fact("hbranch"))
            )
            p.have(
                "h_ws_q: nat0_lt (quote_hf_mem_measure w s) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "h_s_lt_st",
                [QUOTE_HF_NEQ_MEASURE_AT, "hbranch_eq", COND_F_NAT0, "h_mws_s"],
            )
            p.have(
                "h_wt_st: nat0_lt (quote_hf_mem_measure w t) (Insert s t)"
            ).by(
                QUOTE_HF_EXT_DIFF_LEFT_ABSENT_FALSE_BRANCH,
                "w",
                "s",
                "t",
                CONJ(p.fact("hws"), CONJ(p.fact("hnwt"), p.fact("hbranch"))),
            )
            p.have(
                "h_wt_q: nat0_lt (quote_hf_mem_measure w t) "
                "                  (quote_hf_neq_measure s t)"
            ).by_rewrite_of(
                "h_wt_st",
                [QUOTE_HF_NEQ_MEASURE_AT, "hbranch_eq", COND_F_NAT0],
            )
            p.thus(
                "nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t) "
                "/\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t)"
            ).by_thm(CONJ(p.fact("h_ws_q"), p.fact("h_wt_q")))


@proof
def QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES(p):
    """|- !w s t. ~In w s /\\ In w t ==>
          nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t)
       /\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t).

    Symmetric decrease package for the extensional witness branch where
    ``w`` is absent on the left and present on the right.
    """

    p.goal(
        "!w s t. ~(In w s) /\\ In w t ==> "
        "nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t) "
        "/\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t)"
    )
    p.fix("w s t")
    p.assume("(hnws, hwt): ~(In w s) /\\ In w t")
    p.have(
        "h_left_swapped: nat0_lt (quote_hf_mem_measure w t) "
        "                         (quote_hf_neq_measure t s) "
        "/\\ nat0_lt (quote_hf_mem_measure w s) "
        "          (quote_hf_neq_measure t s)"
    ).by(
        QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES,
        "w",
        "t",
        "s",
        CONJ(p.fact("hwt"), p.fact("hnws")),
    )
    p.split("h_left_swapped", "(h_wt_qts,h_ws_qts)")
    # DSL friction: using the fully quantified symmetry theorem as a
    # rewrite rule loops, so specialize it to this s/t pair before rewriting.
    q_sym_ts = SPECL([p._parse("t"), p._parse("s")], QUOTE_HF_NEQ_MEASURE_SYM)
    p.have(
        "h_ws_q: nat0_lt (quote_hf_mem_measure w s) "
        "                  (quote_hf_neq_measure s t)"
    ).by_rewrite_of("h_ws_qts", [q_sym_ts])
    p.have(
        "h_wt_q: nat0_lt (quote_hf_mem_measure w t) "
        "                  (quote_hf_neq_measure s t)"
    ).by_rewrite_of("h_wt_qts", [q_sym_ts])
    p.thus(
        "nat0_lt (quote_hf_mem_measure w s) (quote_hf_neq_measure s t) "
        "/\\ nat0_lt (quote_hf_mem_measure w t) (quote_hf_neq_measure s t)"
    ).by_thm(CONJ(p.fact("h_ws_q"), p.fact("h_wt_q")))


@proof
def QUOTE_HF_MUTUAL_MEASURED(p):
    """Measured mutual-induction target for the quote_hf replacement.

    |- !n.
       (!x y. nat0_lt (quote_hf_mem_measure x y) n ==>
          membership decision for quote_hf x in quote_hf y)
       /\\
       (!s t. ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) n ==>
          quoted inequality).

    This is the non-circular measured route.  The proof calls the strong
    IH at the current measure, then uses strictly smaller membership /
    inequality calls underneath it.  The remaining ``sorry`` leaves are
    object-level branch bridges, not global quote-decision shortcuts.
    """
    p.goal(
        "!n. "
        "(!x y. nat0_lt (quote_hf_mem_measure x y) n ==> "
        "  ((In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
        "   /\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))))) "
        "/\\ "
        "(!s t. ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) n ==> "
        "  Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))))"
    )
    with p.strong_induction("n", "IH"):
        with p.have(
            "h_mem: !x y. nat0_lt (quote_hf_mem_measure x y) n ==> "
            "  ((In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
            "   /\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))))"
        ).proof():
            p.fix("x y")
            p.assume("hlt: nat0_lt (quote_hf_mem_measure x y) n")
            p.have(
                "h_IH_cur: "
                "(!a b. nat0_lt (quote_hf_mem_measure a b) "
                "                  (quote_hf_mem_measure x y) ==> "
                "  ((In a b ==> Prov_HF (In_a (quote_hf a) (quote_hf b))) "
                "   /\\ (~(In a b) ==> Prov_HF (Not_f (In_a (quote_hf a) "
                "                                      (quote_hf b)))))) "
                "/\\ "
                "(!a b. ~(a = b) /\\ nat0_lt (quote_hf_neq_measure a b) "
                "                  (quote_hf_mem_measure x y) ==> "
                "  Prov_HF (Not_f (Eq_f (quote_hf a) (quote_hf b))))"
            ).by("IH", "quote_hf_mem_measure x y", "hlt")
            p.split("h_IH_cur", "(h_mem_smaller,h_neq_smaller)")

            with p.cases_on(EXCLUDED_MIDDLE, "y = 0"):
                with p.case("hy_zero: y = 0"):
                    p.have("h_qy_empty: quote_hf y = Empty_t").by_rewrite(
                        ["hy_zero", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                    )
                    p.have("h_qx_term: is_term (quote_hf x)").by(
                        IS_TERM_QUOTE_HF, "x"
                    )
                    p.have(
                        "h_hf1: Prov_HF (Not_f (In_a (quote_hf x) Empty_t))"
                    ).by(HF1_INST, "quote_hf x", "h_qx_term")
                    p.have(
                        "h_neg_pf: Prov_HF "
                        "(Not_f (In_a (quote_hf x) (quote_hf y)))"
                    ).by_rewrite_of("h_hf1", [SYM(p.fact("h_qy_empty"))])
                    with p.have(
                        "h_pos: In x y ==> "
                        "Prov_HF (In_a (quote_hf x) (quote_hf y))"
                    ).proof():
                        p.assume("hxy: In x y")
                        p.have("h_in_empty: In x Empty").by_rewrite_of(
                            "hxy", ["hy_zero", SYM(EMPTY_DEF)]
                        )
                        p.have("h_not_empty: ~In x Empty").by(NOT_IN_EMPTY, "x")
                        p.absurd().by_conj("h_not_empty", "h_in_empty")
                    with p.have(
                        "h_neg: ~In x y ==> "
                        "Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))"
                    ).proof():
                        p.assume("_: ~In x y")
                        p.thus(
                            "Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))"
                        ).by_thm(p.fact("h_neg_pf"))
                    p.thus(
                        "(In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
                        "/\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) "
                        "                                      (quote_hf y))))"
                    ).by_thm(CONJ(p.fact("h_pos"), p.fact("h_neg")))
                with p.case("hy_nz: ~(y = 0)"):
                    with p.cases_on(EXCLUDED_MIDDLE, "x = low_bit y"):
                        with p.case("hx_head: x = low_bit y"):
                            p.have(
                                "h_qy_raw: quote_hf y = "
                                "Insert_t (quote_hf (low_bit y)) "
                                "         (quote_hf (clear_low y))"
                            ).by(_QUOTE_HF_AT_NZ, "y", "hy_nz")
                            p.have(
                                "h_qy_split: quote_hf y = "
                                "Insert_t (quote_hf x) (quote_hf (clear_low y))"
                            ).by_rewrite_of("h_qy_raw", [SYM(p.fact("hx_head"))])
                            p.have("h_qx_term: is_term (quote_hf x)").by(
                                IS_TERM_QUOTE_HF, "x"
                            )
                            p.have(
                                "h_qcl_term: is_term (quote_hf (clear_low y))"
                            ).by(IS_TERM_QUOTE_HF, "clear_low y")
                            p.have(
                                "h_qx_stable: substitute (quote_hf x) "
                                "(quote_hf (clear_low y)) (SUC0 0) = quote_hf x"
                            ).by(SUBSTITUTE_QUOTE_HF, "x", "quote_hf (clear_low y)", "SUC0 0")
                            p.have(
                                "h_hf2: Prov_HF "
                                "(In_a (quote_hf x) "
                                "      (Insert_t (quote_hf x) (quote_hf (clear_low y))))"
                            ).by(
                                HF2_INST,
                                "quote_hf x",
                                "quote_hf (clear_low y)",
                                CONJ(
                                    p.fact("h_qx_term"),
                                    CONJ(p.fact("h_qcl_term"), p.fact("h_qx_stable")),
                                ),
                            )
                            p.have(
                                "h_pos_pf: Prov_HF "
                                "(In_a (quote_hf x) (quote_hf y))"
                            ).by_rewrite_of("h_hf2", [SYM(p.fact("h_qy_split"))])
                            with p.have(
                                "h_pos: In x y ==> "
                                "Prov_HF (In_a (quote_hf x) (quote_hf y))"
                            ).proof():
                                p.assume("_: In x y")
                                p.thus(
                                    "Prov_HF (In_a (quote_hf x) (quote_hf y))"
                                ).by_thm(p.fact("h_pos_pf"))
                            p.have("h_low_bit: bit (low_bit y) y = T").by(
                                BIT_LOW_BIT, "y", "hy_nz"
                            )
                            p.have("h_in_head_T: In x y = T").by_rewrite(
                                [IN_AT, "hx_head", "h_low_bit"]
                            )
                            p.have("h_in_head: In x y").by_thm(
                                EQT_ELIM(p.fact("h_in_head_T"))
                            )
                            with p.have(
                                "h_neg: ~In x y ==> "
                                "Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))"
                            ).proof():
                                p.assume("hnxy: ~In x y")
                                p.absurd().by_conj("hnxy", "h_in_head")
                            p.thus(
                                "(In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
                                "/\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) "
                                "                                      (quote_hf y))))"
                            ).by_thm(CONJ(p.fact("h_pos"), p.fact("h_neg")))
                        with p.case("hx_ne_head: ~(x = low_bit y)"):
                            p.have(
                                "h_tail_decr: nat0_lt "
                                "(quote_hf_mem_measure x (clear_low y)) "
                                "(quote_hf_mem_measure x y)"
                            ).by(
                                QUOTE_HF_MEM_MEASURE_CLEAR_LOW_DECREASE,
                                "x",
                                "y",
                                CONJ(p.fact("hy_nz"), p.fact("hx_ne_head")),
                            )
                            p.have(
                                "h_tail_dec: "
                                "(In x (clear_low y) ==> "
                                " Prov_HF (In_a (quote_hf x) "
                                "                 (quote_hf (clear_low y)))) "
                                "/\\ (~(In x (clear_low y)) ==> "
                                " Prov_HF (Not_f (In_a (quote_hf x) "
                                "                         (quote_hf (clear_low y)))))"
                            ).by("h_mem_smaller", "x", "clear_low y", "h_tail_decr")
                            p.have(
                                "h_head_neq_decr: nat0_lt "
                                "(quote_hf_neq_measure x (low_bit y)) "
                                "(quote_hf_mem_measure x y)"
                            ).by(
                                QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE,
                                "x",
                                "y",
                                CONJ(p.fact("hy_nz"), p.fact("hx_ne_head")),
                            )
                            p.have(
                                "h_head_neq: Prov_HF "
                                "(Not_f (Eq_f (quote_hf x) "
                                "               (quote_hf (low_bit y))))"
                            ).by(
                                "h_neq_smaller",
                                "x",
                                "low_bit y",
                                CONJ(p.fact("hx_ne_head"), p.fact("h_head_neq_decr")),
                            )
                            # Missing branch bridge: use h_tail_dec and
                            # h_head_neq with HF3_INST plus the quote_hf
                            # decomposition of y to transfer membership
                            # decision from clear_low y to y.
                            p.split("h_tail_dec", "(h_tail_pos,h_tail_neg)")
                            p.have(
                                "h_qy_split: quote_hf y = "
                                "Insert_t (quote_hf (low_bit y)) "
                                "         (quote_hf (clear_low y))"
                            ).by(_QUOTE_HF_AT_NZ, "y", "hy_nz")
                            p.have("h_qx_term: is_term (quote_hf x)").by(
                                IS_TERM_QUOTE_HF, "x"
                            )
                            p.have(
                                "h_qlb_term: is_term (quote_hf (low_bit y))"
                            ).by(IS_TERM_QUOTE_HF, "low_bit y")
                            p.have(
                                "h_qcl_term: is_term (quote_hf (clear_low y))"
                            ).by(IS_TERM_QUOTE_HF, "clear_low y")
                            p.have(
                                "h_qlb_stable_x: substitute (quote_hf (low_bit y)) "
                                "(quote_hf x) (SUC0 0) = quote_hf (low_bit y)"
                            ).by(
                                SUBSTITUTE_QUOTE_HF,
                                "low_bit y",
                                "quote_hf x",
                                "SUC0 0",
                            )
                            p.have(
                                "h_qlb_stable_cl: substitute (quote_hf (low_bit y)) "
                                "(quote_hf (clear_low y)) (SUC0 (SUC0 0)) = "
                                "quote_hf (low_bit y)"
                            ).by(
                                SUBSTITUTE_QUOTE_HF,
                                "low_bit y",
                                "quote_hf (clear_low y)",
                                "SUC0 (SUC0 0)",
                            )
                            p.have(
                                "h_qx_stable_cl: substitute (quote_hf x) "
                                "(quote_hf (clear_low y)) (SUC0 (SUC0 0)) = "
                                "quote_hf x"
                            ).by(
                                SUBSTITUTE_QUOTE_HF,
                                "x",
                                "quote_hf (clear_low y)",
                                "SUC0 (SUC0 0)",
                            )
                            p.have(
                                "h_hf3: Prov_HF (Imp_f "
                                "(Not_f (Eq_f (quote_hf (low_bit y)) (quote_hf x))) "
                                "(Not_f (Imp_f "
                                "  (Imp_f (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y)))) "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y)))) "
                                "  (Not_f (Imp_f "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "         (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y)))))))))"
                            ).by(
                                HF3_INST,
                                "quote_hf (low_bit y)",
                                "quote_hf x",
                                "quote_hf (clear_low y)",
                                CONJ(
                                    CONJ(
                                        p.fact("h_qlb_term"),
                                        CONJ(p.fact("h_qx_term"), p.fact("h_qcl_term")),
                                    ),
                                    CONJ(
                                        p.fact("h_qlb_stable_x"),
                                        CONJ(
                                            p.fact("h_qlb_stable_cl"),
                                            p.fact("h_qx_stable_cl"),
                                        ),
                                    ),
                                ),
                            )
                            qhf_neq_sym_x_lb = SPECL(
                                [p._parse("x"), p._parse("low_bit y")],
                                QUOTE_HF_NEQ_MEASURE_SYM,
                            )
                            p.have(
                                "h_head_neq_decr_sym: nat0_lt "
                                "(quote_hf_neq_measure (low_bit y) x) "
                                "(quote_hf_mem_measure x y)"
                            ).by_rewrite_of("h_head_neq_decr", [qhf_neq_sym_x_lb])
                            with p.have("hx_ne_head_sym: ~(low_bit y = x)").proof():
                                with p.suppose("hlx: low_bit y = x"):
                                    p.have("hxl: x = low_bit y").by_thm(
                                        SYM(p.fact("hlx"))
                                    )
                                    p.absurd().by_conj("hx_ne_head", "hxl")
                            p.have(
                                "h_head_neq_sym: Prov_HF "
                                "(Not_f (Eq_f (quote_hf (low_bit y)) (quote_hf x)))"
                            ).by(
                                "h_neq_smaller",
                                "low_bit y",
                                "x",
                                CONJ(p.fact("hx_ne_head_sym"), p.fact("h_head_neq_decr_sym")),
                            )
                            p.have(
                                "h_iff_pf: Prov_HF (Not_f (Imp_f "
                                "  (Imp_f (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y)))) "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y)))) "
                                "  (Not_f (Imp_f "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "         (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y))))))))"
                            ).by(
                                PROV_HF_MP,
                                "Not_f (Eq_f (quote_hf (low_bit y)) (quote_hf x))",
                                "Not_f (Imp_f "
                                "  (Imp_f (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y)))) "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y)))) "
                                "  (Not_f (Imp_f "
                                "         (In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "         (In_a (quote_hf x) "
                                "                 (Insert_t (quote_hf (low_bit y)) "
                                "                           (quote_hf (clear_low y)))))))",
                                CONJ(p.fact("h_head_neq_sym"), p.fact("h_hf3")),
                            )
                            # DSL friction: formula-shape facts for encoded
                            # conjunction projections still have to be built
                            # manually; there is no local "is_form by syntax"
                            # tactic for an arbitrary closed HF formula.
                            is_form_tail = EQ_MP(
                                SYM(SPECL(
                                    [
                                        p._parse("quote_hf x"),
                                        p._parse("quote_hf (clear_low y)"),
                                    ],
                                    IS_FORM_AT_IN,
                                )),
                                CONJ(p.fact("h_qx_term"), p.fact("h_qcl_term")),
                            )
                            is_term_insert = MP(
                                SPECL(
                                    [
                                        p._parse("quote_hf (low_bit y)"),
                                        p._parse("quote_hf (clear_low y)"),
                                    ],
                                    IS_TERM_INSERT,
                                ),
                                CONJ(p.fact("h_qlb_term"), p.fact("h_qcl_term")),
                            )
                            is_form_head = EQ_MP(
                                SYM(SPECL(
                                    [
                                        p._parse("quote_hf x"),
                                        p._parse(
                                            "Insert_t (quote_hf (low_bit y)) "
                                            "         (quote_hf (clear_low y))"
                                        ),
                                    ],
                                    IS_FORM_AT_IN,
                                )),
                                CONJ(p.fact("h_qx_term"), is_term_insert),
                            )
                            p.have(
                                "h_form_head: is_form "
                                "(In_a (quote_hf x) "
                                "      (Insert_t (quote_hf (low_bit y)) "
                                "                (quote_hf (clear_low y))))"
                            ).by_thm(is_form_head)
                            p.have(
                                "h_form_tail: is_form "
                                "(In_a (quote_hf x) (quote_hf (clear_low y)))"
                            ).by_thm(is_form_tail)
                            p.have(
                                "h_head_to_tail: Prov_HF (Imp_f "
                                "(In_a (quote_hf x) "
                                "      (Insert_t (quote_hf (low_bit y)) "
                                "                (quote_hf (clear_low y)))) "
                                "(In_a (quote_hf x) (quote_hf (clear_low y))))"
                            ).by(
                                PROV_HF_AND_ELIM_LEFT,
                                "Imp_f (In_a (quote_hf x) "
                                "              (Insert_t (quote_hf (low_bit y)) "
                                "                        (quote_hf (clear_low y)))) "
                                "      (In_a (quote_hf x) (quote_hf (clear_low y)))",
                                "Imp_f (In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "      (In_a (quote_hf x) "
                                "              (Insert_t (quote_hf (low_bit y)) "
                                "                        (quote_hf (clear_low y))))",
                                CONJ(
                                    EQ_MP(
                                        SYM(SPECL(
                                            [
                                                p._parse(
                                                    "In_a (quote_hf x) "
                                                    "     (Insert_t (quote_hf (low_bit y)) "
                                                    "               (quote_hf (clear_low y)))"
                                                ),
                                                p._parse(
                                                    "In_a (quote_hf x) "
                                                    "     (quote_hf (clear_low y))"
                                                ),
                                            ],
                                            IS_FORM_AT_IMP,
                                        )),
                                        CONJ(p.fact("h_form_head"), p.fact("h_form_tail")),
                                    ),
                                    CONJ(
                                        EQ_MP(
                                            SYM(SPECL(
                                                [
                                                    p._parse(
                                                        "In_a (quote_hf x) "
                                                        "     (quote_hf (clear_low y))"
                                                    ),
                                                    p._parse(
                                                        "In_a (quote_hf x) "
                                                        "     (Insert_t (quote_hf (low_bit y)) "
                                                        "               (quote_hf (clear_low y)))"
                                                    ),
                                                ],
                                                IS_FORM_AT_IMP,
                                            )),
                                            CONJ(p.fact("h_form_tail"), p.fact("h_form_head")),
                                        ),
                                        p.fact("h_iff_pf"),
                                    ),
                                ),
                            )
                            p.have(
                                "h_tail_to_head: Prov_HF (Imp_f "
                                "(In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "(In_a (quote_hf x) "
                                "      (Insert_t (quote_hf (low_bit y)) "
                                "                (quote_hf (clear_low y)))))"
                            ).by(
                                PROV_HF_AND_ELIM_RIGHT,
                                "Imp_f (In_a (quote_hf x) "
                                "              (Insert_t (quote_hf (low_bit y)) "
                                "                        (quote_hf (clear_low y)))) "
                                "      (In_a (quote_hf x) (quote_hf (clear_low y)))",
                                "Imp_f (In_a (quote_hf x) (quote_hf (clear_low y))) "
                                "      (In_a (quote_hf x) "
                                "              (Insert_t (quote_hf (low_bit y)) "
                                "                        (quote_hf (clear_low y))))",
                                CONJ(
                                    EQ_MP(
                                        SYM(SPECL(
                                            [
                                                p._parse(
                                                    "In_a (quote_hf x) "
                                                    "     (Insert_t (quote_hf (low_bit y)) "
                                                    "               (quote_hf (clear_low y)))"
                                                ),
                                                p._parse(
                                                    "In_a (quote_hf x) "
                                                    "     (quote_hf (clear_low y))"
                                                ),
                                            ],
                                            IS_FORM_AT_IMP,
                                        )),
                                        CONJ(p.fact("h_form_head"), p.fact("h_form_tail")),
                                    ),
                                    CONJ(
                                        EQ_MP(
                                            SYM(SPECL(
                                                [
                                                    p._parse(
                                                        "In_a (quote_hf x) "
                                                        "     (quote_hf (clear_low y))"
                                                    ),
                                                    p._parse(
                                                        "In_a (quote_hf x) "
                                                        "     (Insert_t (quote_hf (low_bit y)) "
                                                        "               (quote_hf (clear_low y)))"
                                                    ),
                                                ],
                                                IS_FORM_AT_IMP,
                                            )),
                                            CONJ(p.fact("h_form_tail"), p.fact("h_form_head")),
                                        ),
                                        p.fact("h_iff_pf"),
                                    ),
                                ),
                            )
                            p.have(
                                "h_contrap_head_tail: Prov_HF (Imp_f "
                                "(Not_f (In_a (quote_hf x) (quote_hf (clear_low y)))) "
                                "(Not_f (In_a (quote_hf x) "
                                "      (Insert_t (quote_hf (low_bit y)) "
                                "                (quote_hf (clear_low y))))))"
                            ).by(
                                PROV_HF_CONTRAP,
                                "In_a (quote_hf x) "
                                "     (Insert_t (quote_hf (low_bit y)) "
                                "               (quote_hf (clear_low y)))",
                                "In_a (quote_hf x) (quote_hf (clear_low y))",
                                CONJ(
                                    p.fact("h_form_head"),
                                    CONJ(p.fact("h_form_tail"), p.fact("h_head_to_tail")),
                                ),
                            )
                            p.have(
                                "h_y_recon_sb: y = "
                                "set_bit (low_bit y) (clear_low y)"
                            ).by(INSERT_LOW_BIT_CLEAR_LOW, "y", "hy_nz")
                            p.have(
                                "h_insert_sb: Insert (low_bit y) (clear_low y) = "
                                "set_bit (low_bit y) (clear_low y)"
                            ).by(INSERT_AT, "low_bit y", "clear_low y")
                            p.have(
                                "h_y_recon: y = Insert (low_bit y) (clear_low y)"
                            ).by_trans("h_y_recon_sb", SYM(p.fact("h_insert_sb")))
                            p.have(
                                "h_in_tail_eq_raw: In x (Insert (low_bit y) "
                                "(clear_low y)) = In x (clear_low y)"
                            ).by(
                                IN_INSERT_DIFF,
                                "low_bit y",
                                "x",
                                "clear_low y",
                                "hx_ne_head_sym",
                            )
                            p.have(
                                "h_in_tail_eq: In x y = In x (clear_low y)"
                            ).by_rewrite_of(
                                "h_in_tail_eq_raw", [SYM(p.fact("h_y_recon"))]
                            )
                            with p.have(
                                "h_pos: In x y ==> "
                                "Prov_HF (In_a (quote_hf x) (quote_hf y))"
                            ).proof():
                                p.assume("hxy: In x y")
                                p.have("h_tail: In x (clear_low y)").by_eq_mp(
                                    "h_in_tail_eq", "hxy"
                                )
                                p.have(
                                    "h_tail_pf: Prov_HF "
                                    "(In_a (quote_hf x) (quote_hf (clear_low y)))"
                                ).by("h_tail_pos", "h_tail")
                                p.have(
                                    "h_head_pf: Prov_HF "
                                    "(In_a (quote_hf x) "
                                    "      (Insert_t (quote_hf (low_bit y)) "
                                    "                (quote_hf (clear_low y))))"
                                ).by(
                                    PROV_HF_MP,
                                    "In_a (quote_hf x) (quote_hf (clear_low y))",
                                    "In_a (quote_hf x) "
                                    "     (Insert_t (quote_hf (low_bit y)) "
                                    "               (quote_hf (clear_low y)))",
                                    CONJ(p.fact("h_tail_pf"), p.fact("h_tail_to_head")),
                                )
                                p.thus(
                                    "Prov_HF (In_a (quote_hf x) (quote_hf y))"
                                ).by_rewrite_of("h_head_pf", [SYM(p.fact("h_qy_split"))])
                            with p.have(
                                "h_neg: ~In x y ==> "
                                "Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))"
                            ).proof():
                                p.assume("hnxy: ~In x y")
                                with p.have("hn_tail: ~In x (clear_low y)").proof():
                                    with p.suppose("h_tail: In x (clear_low y)"):
                                        p.have("hxy: In x y").by_eq_mp(
                                            SYM(p.fact("h_in_tail_eq")), "h_tail"
                                        )
                                        p.absurd().by_conj("hnxy", "hxy")
                                p.have(
                                    "h_tail_neg_pf: Prov_HF "
                                    "(Not_f (In_a (quote_hf x) (quote_hf (clear_low y))))"
                                ).by("h_tail_neg", "hn_tail")
                                p.have(
                                    "h_head_neg_pf: Prov_HF "
                                    "(Not_f (In_a (quote_hf x) "
                                    "      (Insert_t (quote_hf (low_bit y)) "
                                    "                (quote_hf (clear_low y)))))"
                                ).by(
                                    PROV_HF_MP,
                                    "Not_f (In_a (quote_hf x) (quote_hf (clear_low y)))",
                                    "Not_f (In_a (quote_hf x) "
                                    "     (Insert_t (quote_hf (low_bit y)) "
                                    "               (quote_hf (clear_low y))))",
                                    CONJ(
                                        p.fact("h_tail_neg_pf"),
                                        p.fact("h_contrap_head_tail"),
                                    ),
                                )
                                p.thus(
                                    "Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))"
                                ).by_rewrite_of(
                                    "h_head_neg_pf", [SYM(p.fact("h_qy_split"))]
                                )
                            p.thus(
                                "(In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
                                "/\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) "
                                "                                      (quote_hf y))))"
                            ).by_thm(CONJ(p.fact("h_pos"), p.fact("h_neg")))

        with p.have(
            "h_neq: !s t. ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) n ==> "
            "  Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
        ).proof():
            p.fix("s t")
            p.assume(
                "(hst_ne, hlt): ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) n"
            )
            p.have(
                "h_IH_cur: "
                "(!a b. nat0_lt (quote_hf_mem_measure a b) "
                "                  (quote_hf_neq_measure s t) ==> "
                "  ((In a b ==> Prov_HF (In_a (quote_hf a) (quote_hf b))) "
                "   /\\ (~(In a b) ==> Prov_HF (Not_f (In_a (quote_hf a) "
                "                                      (quote_hf b)))))) "
                "/\\ "
                "(!a b. ~(a = b) /\\ nat0_lt (quote_hf_neq_measure a b) "
                "                  (quote_hf_neq_measure s t) ==> "
                "  Prov_HF (Not_f (Eq_f (quote_hf a) (quote_hf b))))"
            ).by("IH", "quote_hf_neq_measure s t", "hlt")
            p.split("h_IH_cur", "(h_mem_smaller,_)")
            p.have(
                "h_ext: ?w. (In w s /\\ ~(In w t)) "
                "\\/ (~(In w s) /\\ In w t)"
            ).by(HF_EXT_DIFF, "s", "t", "hst_ne")
            p.choose("w", "h_ext")
            with p.thus(
                "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
            ).by_cases("w_eq"):
                with p.case("h_left: In w s /\\ ~(In w t)"):
                    p.have(
                        "h_decrs: nat0_lt (quote_hf_mem_measure w s) "
                        "                    (quote_hf_neq_measure s t) "
                        "/\\ nat0_lt (quote_hf_mem_measure w t) "
                        "          (quote_hf_neq_measure s t)"
                    ).by(QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES, "w", "s", "t", "h_left")
                    p.split("h_left", "(h_in_s,h_not_in_t)")
                    p.split("h_decrs", "(h_ws_decr,h_wt_decr)")
                    p.have(
                        "h_dec_s: (In w s ==> Prov_HF "
                        "(In_a (quote_hf w) (quote_hf s))) "
                        "/\\ (~(In w s) ==> Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf s))))"
                    ).by("h_mem_smaller", "w", "s", "h_ws_decr")
                    p.have(
                        "h_dec_t: (In w t ==> Prov_HF "
                        "(In_a (quote_hf w) (quote_hf t))) "
                        "/\\ (~(In w t) ==> Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf t))))"
                    ).by("h_mem_smaller", "w", "t", "h_wt_decr")
                    p.split("h_dec_s", "(h_s_pos, _)")
                    p.split("h_dec_t", "(_, h_t_neg)")
                    p.have("h_pf_in_s: Prov_HF (In_a (quote_hf w) (quote_hf s))").by(
                        "h_s_pos", "h_in_s"
                    )
                    p.have(
                        "h_pf_not_in_t: Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf t)))"
                    ).by("h_t_neg", "h_not_in_t")
                    p.have("h_qs_term: is_term (quote_hf s)").by(IS_TERM_QUOTE_HF, "s")
                    p.have("h_qt_term: is_term (quote_hf t)").by(IS_TERM_QUOTE_HF, "t")
                    p.thus("Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))").by(
                        PROV_HF_NEQ_FROM_MEM_DIFF,
                        "w",
                        "quote_hf s",
                        "quote_hf t",
                        CONJ(
                            p.fact("h_qs_term"),
                            CONJ(
                                p.fact("h_qt_term"),
                                CONJ(p.fact("h_pf_in_s"), p.fact("h_pf_not_in_t")),
                            ),
                        ),
                    )
                with p.case("h_right: ~(In w s) /\\ In w t"):
                    p.have(
                        "h_decrs: nat0_lt (quote_hf_mem_measure w s) "
                        "                    (quote_hf_neq_measure s t) "
                        "/\\ nat0_lt (quote_hf_mem_measure w t) "
                        "          (quote_hf_neq_measure s t)"
                    ).by(QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES, "w", "s", "t", "h_right")
                    p.split("h_right", "(h_not_in_s,h_in_t)")
                    p.split("h_decrs", "(h_ws_decr,h_wt_decr)")
                    p.have(
                        "h_dec_s: (In w s ==> Prov_HF "
                        "(In_a (quote_hf w) (quote_hf s))) "
                        "/\\ (~(In w s) ==> Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf s))))"
                    ).by("h_mem_smaller", "w", "s", "h_ws_decr")
                    p.have(
                        "h_dec_t: (In w t ==> Prov_HF "
                        "(In_a (quote_hf w) (quote_hf t))) "
                        "/\\ (~(In w t) ==> Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf t))))"
                    ).by("h_mem_smaller", "w", "t", "h_wt_decr")
                    p.split("h_dec_s", "(_, h_s_neg)")
                    p.split("h_dec_t", "(h_t_pos, _)")
                    p.have(
                        "h_pf_not_in_s: Prov_HF "
                        "(Not_f (In_a (quote_hf w) (quote_hf s)))"
                    ).by("h_s_neg", "h_not_in_s")
                    p.have("h_pf_in_t: Prov_HF (In_a (quote_hf w) (quote_hf t))").by(
                        "h_t_pos", "h_in_t"
                    )
                    p.have("h_qs_term: is_term (quote_hf s)").by(IS_TERM_QUOTE_HF, "s")
                    p.have("h_qt_term: is_term (quote_hf t)").by(IS_TERM_QUOTE_HF, "t")
                    p.thus("Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))").by(
                        PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT,
                        "w",
                        "quote_hf s",
                        "quote_hf t",
                        CONJ(
                            p.fact("h_qs_term"),
                            CONJ(
                                p.fact("h_qt_term"),
                                CONJ(p.fact("h_pf_not_in_s"), p.fact("h_pf_in_t")),
                            ),
                        ),
                    )

        p.thus(
            "(!x y. nat0_lt (quote_hf_mem_measure x y) n ==> "
            "  ((In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
            "   /\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))))) "
            "/\\ "
            "(!s t. ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) n ==> "
            "  Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))))"
        ).by_thm(CONJ(p.fact("h_mem"), p.fact("h_neq")))


@proof
def QUOTE_HF_MEM_DECISION(p):
    """|- !x y.
          (In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y)))
          /\\
          (~In x y ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y)))).

    Pivot interface for the quote layer.  The HF-IND and old
    ``IS_IN_REPRESENTS`` routes are gone; this is the unbounded
    projection of ``QUOTE_HF_MUTUAL_MEASURED`` at
    ``SUC0 (quote_hf_mem_measure x y)``.
    """

    p.goal(
        "!x y. (In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
        "/\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y))))"
    )
    p.fix("x y")
    p.have(
        "h_bound: nat0_lt (quote_hf_mem_measure x y) "
        "                  (SUC0 (quote_hf_mem_measure x y))"
    ).by(NAT0_LT_SUC0, "quote_hf_mem_measure x y")
    p.have(
        "h_mutual: "
        "(!a b. nat0_lt (quote_hf_mem_measure a b) "
        "                  (SUC0 (quote_hf_mem_measure x y)) ==> "
        "  ((In a b ==> Prov_HF (In_a (quote_hf a) (quote_hf b))) "
        "   /\\ (~(In a b) ==> Prov_HF (Not_f (In_a (quote_hf a) "
        "                                      (quote_hf b)))))) "
        "/\\ "
        "(!s t. ~(s = t) /\\ nat0_lt (quote_hf_neq_measure s t) "
        "                  (SUC0 (quote_hf_mem_measure x y)) ==> "
        "  Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))))"
    ).by(QUOTE_HF_MUTUAL_MEASURED, "SUC0 (quote_hf_mem_measure x y)")
    p.split("h_mutual", "(h_mem,_)")
    p.thus(
        "(In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
        "/\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y))))"
    ).by("h_mem", "x", "y", "h_bound")


@proof
def QUOTE_HF_PROV_NEQ(p):
    """|- !s t. ~(s = t)
          ==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))).

    Global quoted inequality, recovered as an unbounded projection of
    ``QUOTE_HF_MUTUAL_MEASURED`` rather than as the induction target.
    The extensional witness search remains internal to the measured
    theorem; downstream callers only need ``s != t``.
    """

    p.goal(
        "!s t. ~(s = t) "
        "==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
    )
    p.fix("s t")
    p.assume("hst_ne: ~(s = t)")
    p.have(
        "h_bound: nat0_lt (quote_hf_neq_measure s t) "
        "                  (SUC0 (quote_hf_neq_measure s t))"
    ).by(NAT0_LT_SUC0, "quote_hf_neq_measure s t")
    p.have(
        "h_mutual: "
        "(!x y. nat0_lt (quote_hf_mem_measure x y) "
        "                  (SUC0 (quote_hf_neq_measure s t)) ==> "
        "  ((In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y))) "
        "   /\\ (~(In x y) ==> Prov_HF (Not_f (In_a (quote_hf x) "
        "                                      (quote_hf y)))))) "
        "/\\ "
        "(!a b. ~(a = b) /\\ nat0_lt (quote_hf_neq_measure a b) "
        "                  (SUC0 (quote_hf_neq_measure s t)) ==> "
        "  Prov_HF (Not_f (Eq_f (quote_hf a) (quote_hf b))))"
    ).by(QUOTE_HF_MUTUAL_MEASURED, "SUC0 (quote_hf_neq_measure s t)")
    p.split("h_mutual", "(_,h_neq)")
    p.thus("Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))").by(
        "h_neq", "s", "t", CONJ(p.fact("hst_ne"), p.fact("h_bound"))
    )


# ---------------------------------------------------------------------------
# HF-native qparse base case.
#
# Direct qparse-vs-quote constructor bridge axioms are intentionally not part
# of the main G1 path.  Quoted-data templates should be handled by a separate
# data/template substitution layer, leaving object-language ``substitute`` to
# keep its standard variable-substitution semantics.  The empty bridge remains
# here because it is a closed proof and is useful as a smoke test for
# HF-native literal quoting.
# ---------------------------------------------------------------------------


@proof
def QUOTE_HF_QPARSE_EMPTY(p):
    """|- Prov_HF (Eq_f (quote_hf Empty_t) Empty_t)."""
    p.goal("Prov_HF (Eq_f (quote_hf Empty_t) Empty_t)")
    p.have("h_empty: Empty_t = Empty").by_rewrite(
        [EMPTY_T_DEF, SYM(EMPTY_DEF)]
    )
    p.have("h_quote_to_empty: quote_hf Empty_t = quote_hf Empty").by_cong(
        "quote_hf", "h_empty"
    )
    p.have("h_quote: quote_hf Empty_t = Empty_t").by_thm(
        TRANS(p.fact("h_quote_to_empty"), QUOTE_HF_AT_EMPTY)
    )
    p.have("h_term: is_term Empty_t").by_thm(IS_TERM_EMPTY)
    p.have("h_refl: Prov_HF (Eq_f Empty_t Empty_t)").by(
        PROV_HF_REFL, "Empty_t", "h_term"
    )
    p.thus("Prov_HF (Eq_f (quote_hf Empty_t) Empty_t)").by_rewrite_of(
        "h_refl", ["h_quote"]
    )


# ---------------------------------------------------------------------------
# Stage 3C -- substitute representability.
#
# The old operational checker route has been removed from the high-layer path.
# ``hf_repr_core`` now exports the readability-first syntax-recursion package:
#
#   HF_SYNTAX_REC_PACKAGE
#   SUBSTITUTE_REPRESENTS_SYNTACTIC
#   SUBSTITUTE_REPRESENTS_TERM
#   SUBSTITUTE_REPRESENTS_FORM
#   TEMPLATE_FILL_REPRESENTS_TERM
#   TEMPLATE_FILL_QPARSE_VAR_T
#
# For backwards compatibility in formula-level consumers,
# ``SUBSTITUTE_REPRESENTS`` is an alias of ``SUBSTITUTE_REPRESENTS_FORM``.
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Stage 3D (a) -- representability of provability.
#
# Headline theorem (``PROV_HF_REPRESENTS``):
#   |- !n. Prov_HF n <=>
#          Prov_HF (substitute Prov_HF_internal (numeral n) var_x).
#
# ``Prov_HF_internal`` is a HF-formula with ``var_x`` as its sole free
# variable, expressing "Prov_HF holds at var_x". The body now lives in
# ``hf_repr_core.py`` as the dependency-set
# ``?_internal P. Proof_HF_set_internal(P, var_x)`` construction; this
# section supplies the remaining representability and side-condition
# proofs over that body.
#
# Side conditions posted with the headline (consumed by the diagonal
# lemma, which needs ``phi(x)`` to be a well-formed HF-formula whose
# only free variable is ``var_x``):
#   * ``IS_FORM_PROV_HF_INTERNAL``  : |- is_form Prov_HF_internal.
#   * ``FREE_IN_PROV_HF_INTERNAL``  : |- !v. free_in Prov_HF_internal v
#                                          <=> v = var_x.
#
# Discharge plan -- via HF1-HF5 (no Goedel-beta sequence coding).
# The internal proof predicate uses HF-native proof objects, not
# ``cons_l`` lists. The shape is a dependency-set finite HF set of
# proof-step records:
#
#     P contains records (dependency-set, formula)
#     a record with dependency set k is valid if it is an axiom, or
#     follows by MP/Gen from records in P whose ranks are members of k
#     Prov_HF_internal(x) := ?P. Proof_HF_set_internal(P, x)
#
# The dependency guard is important. A naive unordered "closed set of
# formulas" would allow cyclic justifications, because every formula in
# the set could be used to justify every other formula at the same time.
# Dependency-set records preserve the Hilbert proof-sequence
# well-foundedness while keeping citations as ordinary HF membership.
#
# The previous list-based ``Proof_HF`` scaffolding has been removed from
# ``hf_repr_core.py``; both ``Prov_HF`` and ``Prov_HF_internal`` follow
# the set-native route.
#
# Forward direction (HOL ``Prov_HF n`` ==> HF proves the substituted
# form): Sigma_1 completeness for HF. Extract a ``Proof_HF_set`` witness
# via PROV_HF_AT, exhibit its HF encoding as a HF-numeral, verify each
# conjunct term-by-term (each a closed Sigma_0 fact HF decides at
# numerals).
#
# Backward direction (HF proves ==> HOL): Sigma_1 soundness, which
# lives in Stage 6 via the HF model construction (HF |= HF1-HF5 is
# one HOL theorem citation per axiom).
#
# IS_FORM is discharged below by a structural walk over the defining
# body. FREE_IN should use the matching recursion walk over the same
# dependency-set formula.
# ---------------------------------------------------------------------------


def _head_args(tm):
    args = []
    while isinstance(tm, Comb):
        args.append(tm.arg)
        tm = tm.fun
    args.reverse()
    if isinstance(tm, Const):
        return tm.name, args
    return None, args


_IS_FORM_CONST = mk_const("is_form", [])
_IS_TERM_ZERO = EQ_MP(AP_TERM(mk_const("is_term", []), EMPTY_T_DEF), IS_TERM_EMPTY)
_IS_FORM_DEF_THEOREMS = {
    "is_mp_internal": IS_MP_INTERNAL_DEF,
    "is_gen_internal": IS_GEN_INTERNAL_DEF,
    "valid_step_hf_set_internal": VALID_STEP_HF_SET_INTERNAL_DEF,
    "Proof_HF_set_internal": PROOF_HF_SET_INTERNAL_DEF,
    "Prov_HF_internal": PROV_HF_INTERNAL_DEF,
}
_IS_FORM_SIDE_THEOREMS = {
    "is_axiom_internal": IS_FORM_IS_AXIOM_INTERNAL,
}


def _prove_is_term_syntax(tm, memo=None):
    if memo is None:
        memo = {}
    if tm in memo:
        return memo[tm]

    head, args = _head_args(tm)
    if head == "var_x" and not args:
        th = IS_TERM_VAR_X
    elif head == "var_y" and not args:
        th = IS_TERM_VAR_Y
    elif head == "var_z" and not args:
        th = IS_TERM_VAR_Z
    elif head == "Empty_t" and not args:
        th = IS_TERM_EMPTY
    elif head == "0" and not args:
        th = _IS_TERM_ZERO
    elif head == "Var_t" and len(args) == 1:
        th = EQT_ELIM(SPEC(args[0], IS_TERM_AT_VAR))
    elif head == "Insert_t" and len(args) == 2:
        left = _prove_is_term_syntax(args[0], memo)
        right = _prove_is_term_syntax(args[1], memo)
        th = MP(SPECL(args, IS_TERM_INSERT), CONJ(left, right))
    else:
        raise ValueError(f"no is_term syntax proof rule for {head or tm!r}")

    memo[tm] = th
    return th


def _prove_is_form_syntax(tm, memo=None, term_memo=None):
    if memo is None:
        memo = {}
    if term_memo is None:
        term_memo = {}
    if tm in memo:
        return memo[tm]

    head, args = _head_args(tm)
    if head in _IS_FORM_SIDE_THEOREMS and not args:
        th = _IS_FORM_SIDE_THEOREMS[head]
    elif head in _IS_FORM_DEF_THEOREMS and not args:
        def_th = _IS_FORM_DEF_THEOREMS[head]
        _, rhs = dest_eq(def_th._concl)
        body_th = _prove_is_form_syntax(rhs, memo, term_memo)
        th = EQ_MP(SYM(AP_TERM(_IS_FORM_CONST, def_th)), body_th)
    elif head == "Not_f" and len(args) == 1:
        body = _prove_is_form_syntax(args[0], memo, term_memo)
        th = EQ_MP(SYM(SPEC(args[0], IS_FORM_AT_NOT)), body)
    elif head == "Imp_f" and len(args) == 2:
        left = _prove_is_form_syntax(args[0], memo, term_memo)
        right = _prove_is_form_syntax(args[1], memo, term_memo)
        th = EQ_MP(SYM(SPECL(args, IS_FORM_AT_IMP)), CONJ(left, right))
    elif head == "Forall_f" and len(args) == 2:
        body = _prove_is_form_syntax(args[1], memo, term_memo)
        th = EQ_MP(SYM(SPECL(args, IS_FORM_AT_FORALL)), body)
    elif head == "Eq_f" and len(args) == 2:
        left = _prove_is_term_syntax(args[0], term_memo)
        right = _prove_is_term_syntax(args[1], term_memo)
        th = EQ_MP(SYM(SPECL(args, IS_FORM_AT_EQ)), CONJ(left, right))
    elif head == "In_a" and len(args) == 2:
        left = _prove_is_term_syntax(args[0], term_memo)
        right = _prove_is_term_syntax(args[1], term_memo)
        th = EQ_MP(SYM(SPECL(args, IS_FORM_AT_IN)), CONJ(left, right))
    elif head == "substitute" and len(args) == 3:
        formula = _prove_is_form_syntax(args[0], memo, term_memo)
        term = _prove_is_term_syntax(args[1], term_memo)
        th = MP(SPECL(args, SUBSTITUTE_PRESERVES_IS_FORM), CONJ(formula, term))
    elif head == "template_fill" and len(args) == 3:
        formula = _prove_is_form_syntax(args[0], memo, term_memo)
        term = _prove_is_term_syntax(args[1], term_memo)
        th = MP(MP(SPECL(args, TEMPLATE_FILL_PRESERVES_IS_FORM), formula), term)
    else:
        raise ValueError(f"no is_form syntax proof rule for {head or tm!r}")

    memo[tm] = th
    return th


_IS_FORM_PROV_HF_INTERNAL_THM = _prove_is_form_syntax(Prov_HF_internal)


@proof
def PROV_HF_REPRESENTS(p):
    """|- !n. Prov_HF n <=>
              Prov_HF (substitute Prov_HF_internal (numeral n) var_x).

    Stage 3D(a) representability of ``Prov_HF``. AXIOMATIZED via
    ``p.sorry()``; see the Stage 3D section comment above for the
    deferred construction (Proof_HF_internal + Sigma_1
    completeness/soundness).
    """
    p.goal("!n. Prov_HF n = Prov_HF (substitute Prov_HF_internal (numeral n) idx_x)")
    p.sorry()


@proof
def IS_FORM_PROV_HF_INTERNAL(p):
    """|- is_form Prov_HF_internal.

    Side condition for the diagonal lemma, discharged by a structural
    syntax walk over the dependency-set ``Prov_HF_internal`` body.
    """
    p.goal("is_form Prov_HF_internal")
    p.thus("is_form Prov_HF_internal").by_thm(_IS_FORM_PROV_HF_INTERNAL_THM)


@proof
def FREE_IN_PROV_HF_INTERNAL(p):
    """|- !v. free_in Prov_HF_internal v <=> v = var_x.

    Side condition for the diagonal lemma, discharged from the final
    package free-variable contract for ``Prov_HF_internal``.
    """
    p.goal("!v. free_in Prov_HF_internal v = (v = idx_x)")
    p.thus("!v. free_in Prov_HF_internal v = (v = idx_x)").by_thm(
        FREE_IN_PROV_HF_INTERNAL_BODY
    )


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage 3 high layer -- measured quote route + representability stubs.")
    print("    IS_TERM_VAR_X :", pp_thm(IS_TERM_VAR_X))
    print("    IS_TERM_VAR_Y :", pp_thm(IS_TERM_VAR_Y))
    print("    IS_TERM_VAR_Z :", pp_thm(IS_TERM_VAR_Z))
    print("    HF1_INST      :", pp_thm(HF1_INST))
    print("    HF2_INST      :", pp_thm(HF2_INST))
    print("    HF3_INST      :", pp_thm(HF3_INST))
    print("    QUOTE_HF_INJ  :", pp_thm(QUOTE_HF_INJ))
    print("    HF4_INST                       :", pp_thm(HF4_INST))
    print("    PROV_HF_NEQ_FROM_MEM_DIFF     :", pp_thm(PROV_HF_NEQ_FROM_MEM_DIFF))
    print(
        "    PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT:",
        pp_thm(PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT),
    )
    print("    BOOL_NEQ_XOR                         :", pp_thm(BOOL_NEQ_XOR))
    print("    HF_EXT_DIFF                          :", pp_thm(HF_EXT_DIFF))
    print(
        "    QUOTE_HF_MEM_DECISION                  :",
        pp_thm(QUOTE_HF_MEM_DECISION),
    )
    print(
        "    QUOTE_HF_PROV_NEQ                      :",
        pp_thm(QUOTE_HF_PROV_NEQ),
    )
    print("    QUOTE_HF_QPARSE_EMPTY                  :", pp_thm(QUOTE_HF_QPARSE_EMPTY))
    print("    QUOTE_HF_MEM_MEASURE_AT                :", pp_thm(QUOTE_HF_MEM_MEASURE_AT))
    print("    QUOTE_HF_NEQ_MEASURE_AT                :", pp_thm(QUOTE_HF_NEQ_MEASURE_AT))
    print(
        "    QUOTE_HF_MEM_MEASURE_CLEAR_LOW_DECREASE:",
        pp_thm(QUOTE_HF_MEM_MEASURE_CLEAR_LOW_DECREASE),
    )
    print(
        "    QUOTE_HF_MEM_HEAD_NEQ_RAW_DECREASE:",
        pp_thm(QUOTE_HF_MEM_HEAD_NEQ_RAW_DECREASE),
    )
    print(
        "    QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE:",
        pp_thm(QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE),
    )
    print(
        "    QUOTE_HF_NEQ_MEASURE_LT_FROM_BOTH      :",
        pp_thm(QUOTE_HF_NEQ_MEASURE_LT_FROM_BOTH),
    )
    print(
        "    QUOTE_HF_NEQ_MEASURE_LT_FROM_FOUR_MEM_BOUNDS:",
        pp_thm(QUOTE_HF_NEQ_MEASURE_LT_FROM_FOUR_MEM_BOUNDS),
    )
    print(
        "    QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES:",
        pp_thm(QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES),
    )
    print(
        "    QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES:",
        pp_thm(QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES),
    )
    print("    QUOTE_HF_MUTUAL_MEASURED                :", pp_thm(QUOTE_HF_MUTUAL_MEASURED))
    print("    HF_SUPPORT_PREDICATE_PACKAGE          :", pp_thm(HF_SUPPORT_PREDICATE_PACKAGE))
    print("    IS_TERM_INTERNAL_REPRESENTS           :", pp_thm(IS_TERM_INTERNAL_REPRESENTS))
    print("    NOT_IS_TERM_INTERNAL_REPRESENTS       :", pp_thm(NOT_IS_TERM_INTERNAL_REPRESENTS))
    print("    IS_FORM_INTERNAL_REPRESENTS           :", pp_thm(IS_FORM_INTERNAL_REPRESENTS))
    print("    NOT_IS_FORM_INTERNAL_REPRESENTS       :", pp_thm(NOT_IS_FORM_INTERNAL_REPRESENTS))
    print("    FREE_IN_INTERNAL_REPRESENTS           :", pp_thm(FREE_IN_INTERNAL_REPRESENTS))
    print("    NOT_FREE_IN_INTERNAL_REPRESENTS       :", pp_thm(NOT_FREE_IN_INTERNAL_REPRESENTS))
    print("    HF_SUPPORT_EQUIV_PACKAGE              :", pp_thm(HF_SUPPORT_EQUIV_PACKAGE))
    print("    IS_TERM_INTERNAL_EQUIV                :", pp_thm(IS_TERM_INTERNAL_EQUIV))
    print("    IS_FORM_INTERNAL_EQUIV                :", pp_thm(IS_FORM_INTERNAL_EQUIV))
    print("    FREE_IN_INTERNAL_EQUIV                :", pp_thm(FREE_IN_INTERNAL_EQUIV))
    print("    SUBSTITUTE_INTERNAL_EQUIV             :", pp_thm(SUBSTITUTE_INTERNAL_EQUIV))
    print("    SUBSTITUTE_INTERNAL_FUNCTIONAL        :", pp_thm(SUBSTITUTE_INTERNAL_FUNCTIONAL))
    print("    HF_PACKAGE_SIDE_CONDITION_PACKAGE      :", pp_thm(HF_PACKAGE_SIDE_CONDITION_PACKAGE))
    print("    IS_FORM_IS_AXIOM_INTERNAL              :", pp_thm(IS_FORM_IS_AXIOM_INTERNAL))
    print("    FREE_IN_IS_AXIOM_INTERNAL              :", pp_thm(FREE_IN_IS_AXIOM_INTERNAL))
    print("    IS_TERM_QPARSE_PAIR_ORD                :", pp_thm(IS_TERM_QPARSE_PAIR_ORD))
    print("    FREE_IN_QPARSE_PAIR_ORD                :", pp_thm(FREE_IN_QPARSE_PAIR_ORD))
    print("    IS_TERM_QPARSE_IMP_F                   :", pp_thm(IS_TERM_QPARSE_IMP_F))
    print("    FREE_IN_QPARSE_IMP_F                   :", pp_thm(FREE_IN_QPARSE_IMP_F))
    print("    IS_TERM_QPARSE_FORALL_F                :", pp_thm(IS_TERM_QPARSE_FORALL_F))
    print("    FREE_IN_QPARSE_FORALL_F                :", pp_thm(FREE_IN_QPARSE_FORALL_F))
    print("    HF_PROV_FREE_CONDITION_PACKAGE         :", pp_thm(HF_PROV_FREE_CONDITION_PACKAGE))
    print("    FREE_IN_PROV_HF_INTERNAL_BODY          :", pp_thm(FREE_IN_PROV_HF_INTERNAL_BODY))
    print("    HF_SYNTAX_REC_PACKAGE                  :", pp_thm(HF_SYNTAX_REC_PACKAGE))
    print(
        "    SUBSTITUTE_REPRESENTS_SYNTACTIC        :",
        pp_thm(SUBSTITUTE_REPRESENTS_SYNTACTIC),
    )
    print("    SUBSTITUTE_REPRESENTS_TERM             :", pp_thm(SUBSTITUTE_REPRESENTS_TERM))
    print("    SUBSTITUTE_REPRESENTS_FORM             :", pp_thm(SUBSTITUTE_REPRESENTS_FORM))
    print("    TEMPLATE_FILL_EMPTY                    :", pp_thm(TEMPLATE_FILL_EMPTY))
    print("    TEMPLATE_FILL_HOLE_HIT                 :", pp_thm(TEMPLATE_FILL_HOLE_HIT))
    print("    TEMPLATE_FILL_HOLE_MISS                :", pp_thm(TEMPLATE_FILL_HOLE_MISS))
    print("    TEMPLATE_FILL_INSERT                   :", pp_thm(TEMPLATE_FILL_INSERT))
    print("    TEMPLATE_FILL_QPARSE_VAR_T             :", pp_thm(TEMPLATE_FILL_QPARSE_VAR_T))
    print("    TEMPLATE_FILL_REPRESENTS_TERM          :", pp_thm(TEMPLATE_FILL_REPRESENTS_TERM))
    print(
        "    PROV_HF_REPRESENTS (SORRY)             :",
        pp_thm(PROV_HF_REPRESENTS),
    )
    print(
        "    IS_FORM_PROV_HF_INTERNAL               :",
        pp_thm(IS_FORM_PROV_HF_INTERNAL),
    )
    print(
        "    FREE_IN_PROV_HF_INTERNAL              :",
        pp_thm(FREE_IN_PROV_HF_INTERNAL),
    )
