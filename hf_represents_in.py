# ---------------------------------------------------------------------------
# Stage B1.0(c) part 2 -- IS_IN_REPRESENTS body and prerequisites.
#
# Discharges the SORRY in ``hf_repr.IS_IN_REPRESENTS`` (kept in place
# so ``IS_SUBSTITUTE_STEP_REPRESENTS`` and downstream consumers see no
# layout change), via a freshly proved twin ``IS_IN_REPRESENTS_TH``
# whose statement is identical.
#
# Lives downstream of ``hf_logic.py`` because the proofs need:
#   * PROV_HF_UI / PROV_HF_UI_IMP -- universal instantiation
#   * PROV_HF_AND_INTRO/ELIM, PROV_HF_CONTRAP, PROV_HF_DOUBLE_NEG_*,
#     PROV_HF_TRANS_IMP -- propositional toolkit
# all of which transitively import ``PROV_HF_AXIOM`` / ``PROV_HF_MP``
# from ``hf_repr``. Putting these proofs back in ``hf_repr`` would
# create a cycle.
#
# Build order:
#   (a) HF1_INST / HF2_INST / HF3_INST -- closed HF1-3 axioms
#       instantiated at concrete HF-syntax terms, via PROV_HF_UI plus
#       the substitute reduction lemmas.
#   (b) QUOTE_HF_INJ -- HOL-level injectivity of the quoting map.
#   (c) IS_IN_REPRESENTS_TH -- HF_INDUCTION on ``y`` with x fixed.
# ---------------------------------------------------------------------------


from fusion import Var
from basics import mk_app, mk_eq
from nat0 import nat0_ty, ZERO, mk_suc0
from proof import proof
from tactics import (
    SPEC,
    SPECL,
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
    EQT_ELIM,
    REWRITE_RULE,
)

from hf_proof import (
    HF1_axiom,
    HF2_axiom,
    HF3_axiom,
    HF1_AXIOM_DEF,
    HF2_AXIOM_DEF,
    HF3_AXIOM_DEF,
    IS_HF_AXIOM_HOLDS,
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
)
from hf_repr import (
    PROV_HF_AXIOM,
    IS_TERM_EMPTY,
    IS_TERM_INSERT,
    QUOTE_HF_AT_EMPTY,
    _QUOTE_HF_AT_NZ,
)
from hf_sets import EMPTY_DEF
from hf_syntax import INSERT_T_INJ, INSERT_T_NEQ_EMPTY
from bits import (
    INSERT_LOW_BIT_CLEAR_LOW,
    LOW_BIT_LT,
    CLEAR_LOW_LT,
)
from classical import EXCLUDED_MIDDLE
from hf_logic import (
    PROV_HF_UI,
    PROV_HF_SUBST_EQ,
    PROV_HF_HYP_DROP,
    PROV_HF_DT_MP,
    PROV_HF_CONTRAP,
    PROV_HF_DOUBLE_NEG_INTRO,
)
from hf_repr import IS_TERM_QUOTE_HF, SUBSTITUTE_QUOTE_HF, PROV_HF_MP


_t_n0 = Var("t", nat0_ty)
_u_n0 = Var("u", nat0_ty)
_w_n0 = Var("w", nat0_ty)


# ---------------------------------------------------------------------------
# Helper: lift |- is_hf_axiom HF_axiom to |- Prov_HF HF_axiom.
# ---------------------------------------------------------------------------
def _prov_of_hf_axiom(axiom_const):
    """|- Prov_HF HF{n}_axiom from |- is_hf_axiom HF{n}_axiom.

    is_axiom = is_hf_axiom \\/ is_logical_axiom; lift through DISJ1
    then PROV_HF_AXIOM.
    """
    name = axiom_const.name
    is_hf_th = IS_HF_AXIOM_HOLDS[name]  # |- is_hf_axiom HF{n}_axiom
    is_axiom_at = SPEC(axiom_const, IS_AXIOM_AT)
    log_part = mk_app(is_logical_axiom, axiom_const)
    is_axiom_th = EQ_MP(SYM(is_axiom_at), DISJ1(is_hf_th, log_part))
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
# consumers (IS_IN_REPRESENTS) discharge it via SUBSTITUTE_QUOTE_HF on
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
# HF2/HF3_INST.  Stubbed (sorry) for now; the discharge follows the
# same template (``_prov_of_hf_axiom`` + UI + reductions) but the body's
# ∀z layer plus encoded-iff make the substitute reduction longer than
# HF3 -- estimated ~600 lines.  We use it as a black-box lemma below.
# ---------------------------------------------------------------------------


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

    HF4 (extensionality) instantiated at (a, b).  SORRY -- mechanical
    extension of HF2/HF3_INST: two PROV_HF_UI steps interleaved with
    substitute reductions through the body's ∀z + encoded-iff
    structure.  Estimated ~600 lines.

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
    p.sorry()


# ---------------------------------------------------------------------------
# Insert_t-injectivity lifts at Prov_HF, restricted to canonical bit-
# decomposition of HF set values.
#
# In general HF, Insert is not injective (Insert a {} = Insert a {a} =
# {a}).  Under the canonical-form precondition that the head element is
# strictly less than every element of the tail (LOW_BIT_CLEAR_LOW_PRECOND),
# Insert is injective in *both* arguments jointly.  These two helpers
# encapsulate that fact at the Prov_HF level for ``quote_hf`` images;
# they are SORRY pending the full HF4_INST + canonical-form chain
# (each ~150 lines on top of HF4_INST).  Used by QUOTE_HF_PROV_NEQ to
# lift bit-component inequalities to whole-quote_hf inequalities.
# ---------------------------------------------------------------------------


@proof
def QUOTE_HF_NEQ_FROM_LOW_BIT(p):
    """|- !s t. ~(s = 0) /\\ ~(t = 0)
                /\\ Prov_HF (Not_f (Eq_f (quote_hf (low_bit s))
                                         (quote_hf (low_bit t))))
                ==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))).

    SORRY (~150 lines on top of HF4_INST).

    Outline -- under canonical form ``low_bit s ∉ clear_low s`` and
    similarly for t, distinct heads force distinct Insert_t towers:

      Suppose Insert_t (q lb_s) (q cl_s) = Insert_t (q lb_t) (q cl_t).
      HF2 + Eq-substitutivity: q lb_s ∈ Insert_t (q lb_t) (q cl_t).
      HF3 (cond q lb_t ≠ q lb_s, given by the input Prov_HF Not_f Eq):
         ⟹ q lb_s ∈ q cl_t.
      By symmetry: q lb_t ∈ q cl_s.
      Combined with canonical-form non-membership of heads in their own
      tails (q lb_s ∉ q cl_s, q lb_t ∉ q cl_t) and the bit-ordering
      ``lb_s < lb_t`` or ``lb_s > lb_t`` (one direction or the other),
      derive contradiction via HF4 contrapositively + LOW_BIT_LT.
    """
    p.goal(
        "!s t. ~(s = 0) /\\ ~(t = 0) "
        "/\\ Prov_HF (Not_f (Eq_f (quote_hf (low_bit s)) "
        "                          (quote_hf (low_bit t)))) "
        "==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))",
        types={"s": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


@proof
def QUOTE_HF_NEQ_FROM_CLEAR_LOW(p):
    """|- !s t. ~(s = 0) /\\ ~(t = 0)
                /\\ (low_bit s = low_bit t)
                /\\ Prov_HF (Not_f (Eq_f (quote_hf (clear_low s))
                                         (quote_hf (clear_low t))))
                ==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))).

    SORRY (~150 lines on top of HF4_INST).

    Outline -- under canonical form, with matching heads and distinct
    tails, the Insert_t towers differ in the tail.  The proof uses
    HF4_INST (extensionality) to reduce ``Eq_f Insert_t Insert_t``
    membership-questionwise; canonical-form non-membership of heads in
    tails kills the head-witness branch, so the discriminator from the
    IH-supplied tail Prov_HF inequality lifts cleanly.

    The ``low_bit s = low_bit t`` precondition lets us share the head
    rewrite throughout the substitutivity chain.
    """
    p.goal(
        "!s t. ~(s = 0) /\\ ~(t = 0) "
        "/\\ (low_bit s = low_bit t) "
        "/\\ Prov_HF (Not_f (Eq_f (quote_hf (clear_low s)) "
        "                          (quote_hf (clear_low t)))) "
        "==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))",
        types={"s": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


# ---------------------------------------------------------------------------
# QUOTE_HF_PROV_NEQ -- Prov_HF-level inequality for distinct quoted terms.
#
# This is the meta-result missing from the original IS_IN_REPRESENTS
# docstring's "PROV_HF_REFL + PROV_HF_CONTRAP / N" fragment. ``HF`` is
# decidable on closed Insert_t/Empty_t towers in canonical form; from
# HOL-distinct ``s, t`` we can effectively produce a Prov_HF derivation
# of the inequality of their quoted images, but the construction is its
# own induction on the canonical bit decomposition.
# ---------------------------------------------------------------------------


def _empty_neq_insert_quotes(p, lb_label, cl_label, nz_label, dir_left_zero):
    """Build Prov_HF (Not_f (Eq_f Empty_t (Insert_t (q lb) (q cl)))) (when
    ``dir_left_zero=True``) or Prov_HF (Not_f (Eq_f (Insert_t (q lb) (q cl))
    Empty_t)) (when ``dir_left_zero=False``).

    Discrimination via HF1 + HF2 + PROV_HF_SUBST_EQ.  ``lb_label`` /
    ``cl_label`` name HOL nat0 *expressions* whose ``quote_hf`` images
    fill the Insert_t slots (e.g. ``"low_bit t"`` and ``"clear_low t"``).
    ``nz_label`` names a fact ``~(<x> = 0)`` for the variable whose
    nonzero-decomposition produces the Insert_t (used only in
    ``_QUOTE_HF_AT_NZ``-flavoured downstream chains; here it is not
    consumed -- caller provides the bit-decomposition by other means).

    Returns the desired Prov_HF Not_f Eq_f fact under the label
    ``h_qhf_neq``.
    """
    A = f"quote_hf ({lb_label})"
    B = f"quote_hf ({cl_label})"
    insert_AB = f"Insert_t ({A}) ({B})"
    if dir_left_zero:
        eq_term = f"Eq_f Empty_t ({insert_AB})"
        t1, t2 = "Empty_t", insert_AB
    else:
        eq_term = f"Eq_f ({insert_AB}) Empty_t"
        t1, t2 = insert_AB, "Empty_t"

    # is_term proofs.
    p.have(f"h_t_lb: is_term ({A})").by(IS_TERM_QUOTE_HF, lb_label)
    p.have(f"h_t_cl: is_term ({B})").by(IS_TERM_QUOTE_HF, cl_label)
    p.have(f"h_t_ins: is_term ({insert_AB})").by(
        IS_TERM_INSERT, A, B, CONJ(p.fact("h_t_lb"), p.fact("h_t_cl")),
    )
    p.have("h_t_empty: is_term Empty_t").by_thm(IS_TERM_EMPTY)
    is_term_v0 = EQT_ELIM(SPEC(ZERO, IS_TERM_AT_VAR))
    p.have("h_t_v0: is_term (Var_t 0)").by_thm(is_term_v0)

    # is_form proofs (for the Prov_HF toolkit).
    is_form_in_a_v0 = EQ_MP(
        SYM(SPECL([p._parse(A), p._parse("Var_t 0")], IS_FORM_AT_IN)),
        CONJ(p.fact("h_t_lb"), p.fact("h_t_v0")),
    )
    p.have(f"h_f_in_a_v0: is_form (In_a ({A}) (Var_t 0))").by_thm(
        is_form_in_a_v0
    )
    is_form_phi = EQ_MP(
        SYM(SPEC(p._parse(f"In_a ({A}) (Var_t 0)"), IS_FORM_AT_NOT)),
        is_form_in_a_v0,
    )
    p.have(
        f"h_f_phi: is_form (Not_f (In_a ({A}) (Var_t 0)))"
    ).by_thm(is_form_phi)

    # PROV_HF_SUBST_EQ at (0, Not_f (In_a A (Var_t 0)), t1, t2):
    #   Prov_HF (Imp_f (Eq_f t1 t2) (Imp_f phi[t1/0] phi[t2/0])).
    p.have(
        f"h_subst_eq: Prov_HF (Imp_f ({eq_term}) "
        f"(Imp_f (substitute (Not_f (In_a ({A}) (Var_t 0))) ({t1}) 0) "
        f"       (substitute (Not_f (In_a ({A}) (Var_t 0))) ({t2}) 0)))"
    ).by(
        PROV_HF_SUBST_EQ, "0",
        f"Not_f (In_a ({A}) (Var_t 0))", t1, t2,
        CONJ(
            p.fact("h_f_phi"),
            CONJ(
                p.fact("h_t_empty") if t1 == "Empty_t" else p.fact("h_t_ins"),
                p.fact("h_t_ins") if t2 == insert_AB else p.fact("h_t_empty"),
            ),
        ),
    )

    # Reduce the substitutes symbolically.
    # substitute (Not_f (In_a A (Var_t 0))) T 0
    #   = Not_f (In_a (substitute A T 0) (substitute (Var_t 0) T 0))
    #   = Not_f (In_a A T)             [SUBSTITUTE_QUOTE_HF on A; HIT for Var_t 0]
    subst_v0_at_0_t1 = MP(
        SPECL([ZERO, p._parse(t1), ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    subst_v0_at_0_t2 = MP(
        SPECL([ZERO, p._parse(t2), ZERO], SUBSTITUTE_AT_VAR_HIT),
        REFL(ZERO),
    )
    p.have(
        f"h_imp_phi_phi: Prov_HF (Imp_f ({eq_term}) "
        f"(Imp_f (Not_f (In_a ({A}) ({t1}))) "
        f"       (Not_f (In_a ({A}) ({t2})))))"
    ).by_rewrite_of(
        "h_subst_eq",
        [
            SUBSTITUTE_AT_NOT, SUBSTITUTE_AT_IN,
            SUBSTITUTE_QUOTE_HF, SUBSTITUTE_AT_EMPTY,
            SUBSTITUTE_AT_INSERT,
            subst_v0_at_0_t1, subst_v0_at_0_t2,
        ],
    )

    # HF1_INST gives Prov_HF (Not_f (In_a A Empty_t)).
    # HF2_INST gives Prov_HF (In_a A (Insert_t A B))  (under the
    # substitute-stability precond, vacuous for quote_hf images).
    p.have(
        f"h_hf1: Prov_HF (Not_f (In_a ({A}) Empty_t))"
    ).by(HF1_INST, A, "h_t_lb")

    # substitute (q lb) (q cl) (SUC0 0) = q lb -- precond for HF2_INST.
    p.have(
        f"h_subst_qhf_lb: substitute ({A}) ({B}) (SUC0 0) = ({A})"
    ).by(SUBSTITUTE_QUOTE_HF, lb_label, B, "SUC0 0")
    p.have(
        f"h_hf2: Prov_HF (In_a ({A}) (Insert_t ({A}) ({B})))"
    ).by(
        HF2_INST, A, B,
        CONJ(
            p.fact("h_t_lb"),
            CONJ(p.fact("h_t_cl"), p.fact("h_subst_qhf_lb")),
        ),
    )

    # is_form for the toolkit calls.
    is_form_in_A_emp = EQ_MP(
        SYM(SPECL([p._parse(A), p._parse("Empty_t")], IS_FORM_AT_IN)),
        CONJ(p.fact("h_t_lb"), p.fact("h_t_empty")),
    )
    p.have(f"h_f_in_A_emp: is_form (In_a ({A}) Empty_t)").by_thm(
        is_form_in_A_emp
    )
    is_form_not_in_A_emp = EQ_MP(
        SYM(SPEC(p._parse(f"In_a ({A}) Empty_t"), IS_FORM_AT_NOT)),
        is_form_in_A_emp,
    )
    p.have(
        f"h_f_not_in_A_emp: is_form (Not_f (In_a ({A}) Empty_t))"
    ).by_thm(is_form_not_in_A_emp)

    is_form_in_A_ins = EQ_MP(
        SYM(SPECL([p._parse(A), p._parse(insert_AB)], IS_FORM_AT_IN)),
        CONJ(p.fact("h_t_lb"), p.fact("h_t_ins")),
    )
    p.have(f"h_f_in_A_ins: is_form (In_a ({A}) ({insert_AB}))").by_thm(
        is_form_in_A_ins
    )
    is_form_not_in_A_ins = EQ_MP(
        SYM(SPEC(p._parse(f"In_a ({A}) ({insert_AB})"), IS_FORM_AT_NOT)),
        is_form_in_A_ins,
    )
    p.have(
        f"h_f_not_in_A_ins: is_form (Not_f (In_a ({A}) ({insert_AB})))"
    ).by_thm(is_form_not_in_A_ins)

    # is_form (Eq_f t1 t2) -- the discriminator equation.
    from hf_syntax import IS_FORM_AT_EQ
    is_form_eq = EQ_MP(
        SYM(SPECL([p._parse(t1), p._parse(t2)], IS_FORM_AT_EQ)),
        CONJ(
            p.fact("h_t_empty") if t1 == "Empty_t" else p.fact("h_t_ins"),
            p.fact("h_t_ins") if t2 == insert_AB else p.fact("h_t_empty"),
        ),
    )
    p.have(f"h_f_eq: is_form ({eq_term})").by_thm(is_form_eq)

    # HYP_DROP h_hf1 under hyp (Eq_f t1 t2):
    #   Prov_HF (Imp_f (Eq_f t1 t2) (Not_f (In_a A Empty_t))).
    p.have(
        f"h_drop_hf1: Prov_HF (Imp_f ({eq_term}) "
        f"(Not_f (In_a ({A}) Empty_t)))"
    ).by(
        PROV_HF_HYP_DROP,
        eq_term, f"Not_f (In_a ({A}) Empty_t)",
        CONJ(
            p.fact("h_f_eq"),
            CONJ(p.fact("h_f_not_in_A_emp"), p.fact("h_hf1")),
        ),
    )

    # The (Empty side) operand of the inner Imp_f phi[t1/0] = Not_f (In_a A
    # Empty_t) only when t1 = Empty_t (dir_left_zero=True); otherwise t1 =
    # Insert_t A B and the corresponding inner premise is Not_f (In_a A
    # (Insert_t A B)).  We therefore branch the DT_MP shape on direction.
    if dir_left_zero:
        # h_imp_phi_phi : Imp_f Eq (Imp_f (Not_f (In A Empty)) (Not_f (In A Insert))).
        # h_drop_hf1    : Imp_f Eq (Not_f (In A Empty)).
        # PROV_HF_DT_MP : Imp_f Eq (Not_f (In A Insert)).
        p.have(
            f"h_imp_eq_neg_ins: Prov_HF (Imp_f ({eq_term}) "
            f"(Not_f (In_a ({A}) ({insert_AB}))))"
        ).by(
            PROV_HF_DT_MP,
            eq_term, f"Not_f (In_a ({A}) Empty_t)",
            f"Not_f (In_a ({A}) ({insert_AB}))",
            CONJ(
                p.fact("h_f_eq"),
                CONJ(
                    p.fact("h_f_not_in_A_emp"),
                    CONJ(
                        p.fact("h_f_not_in_A_ins"),
                        CONJ(p.fact("h_drop_hf1"), p.fact("h_imp_phi_phi")),
                    ),
                ),
            ),
        )
        # PROV_HF_CONTRAP at (Eq, Not_f (In A Insert)):
        #   need Prov_HF (Not_f (Not_f (In A Insert))) -- DNI(h_hf2).
        p.have(
            f"h_dni_hf2: Prov_HF (Not_f (Not_f (In_a ({A}) ({insert_AB}))))"
        ).by(
            PROV_HF_DOUBLE_NEG_INTRO,
            f"In_a ({A}) ({insert_AB})",
            CONJ(p.fact("h_f_in_A_ins"), p.fact("h_hf2")),
        )
        # PROV_HF_CONTRAP gives the *implication* (¬B → ¬A); MP with
        # ``h_dni_hf2`` (Prov_HF (Not_f (Not_f In_a A Insert))) finishes.
        p.have(
            f"h_contrap: Prov_HF (Imp_f "
            f"(Not_f (Not_f (In_a ({A}) ({insert_AB})))) "
            f"(Not_f ({eq_term})))"
        ).by(
            PROV_HF_CONTRAP,
            eq_term, f"Not_f (In_a ({A}) ({insert_AB}))",
            CONJ(
                p.fact("h_f_eq"),
                CONJ(
                    p.fact("h_f_not_in_A_ins"),
                    p.fact("h_imp_eq_neg_ins"),
                ),
            ),
        )
        p.have(f"h_qhf_neq: Prov_HF (Not_f ({eq_term}))").by(
            PROV_HF_MP,
            f"Not_f (Not_f (In_a ({A}) ({insert_AB})))",
            f"Not_f ({eq_term})",
            CONJ(p.fact("h_dni_hf2"), p.fact("h_contrap")),
        )
    else:
        # Symmetric: t1 = Insert, t2 = Empty.  Use the *positive* phi
        # variant -- HF2_INST gives In_a A (Insert), and after substitutivity
        # the implication chain delivers In_a A Empty, which contradicts
        # HF1_INST.  We re-derive the chain from PROV_HF_SUBST_EQ at the
        # positive phi (In_a A (Var_t 0)) instead.
        is_form_phi_pos = is_form_in_a_v0  # already proved
        p.have(
            f"h_subst_eq_pos: Prov_HF (Imp_f ({eq_term}) "
            f"(Imp_f (substitute (In_a ({A}) (Var_t 0)) ({t1}) 0) "
            f"       (substitute (In_a ({A}) (Var_t 0)) ({t2}) 0)))"
        ).by(
            PROV_HF_SUBST_EQ, "0",
            f"In_a ({A}) (Var_t 0)", t1, t2,
            CONJ(
                p.fact("h_f_in_a_v0"),
                CONJ(p.fact("h_t_ins"), p.fact("h_t_empty")),
            ),
        )
        p.have(
            f"h_imp_phi_phi_pos: Prov_HF (Imp_f ({eq_term}) "
            f"(Imp_f (In_a ({A}) ({t1})) "
            f"       (In_a ({A}) ({t2}))))"
        ).by_rewrite_of(
            "h_subst_eq_pos",
            [
                SUBSTITUTE_AT_IN,
                SUBSTITUTE_QUOTE_HF, SUBSTITUTE_AT_EMPTY,
                SUBSTITUTE_AT_INSERT,
                subst_v0_at_0_t1, subst_v0_at_0_t2,
            ],
        )
        # HYP_DROP h_hf2 under hyp (Eq_f Insert Empty):
        p.have(
            f"h_drop_hf2: Prov_HF (Imp_f ({eq_term}) "
            f"(In_a ({A}) ({insert_AB})))"
        ).by(
            PROV_HF_HYP_DROP,
            eq_term, f"In_a ({A}) ({insert_AB})",
            CONJ(
                p.fact("h_f_eq"),
                CONJ(p.fact("h_f_in_A_ins"), p.fact("h_hf2")),
            ),
        )
        # DT_MP gives Imp_f Eq (In A Empty).
        p.have(
            f"h_imp_eq_in_emp: Prov_HF (Imp_f ({eq_term}) "
            f"(In_a ({A}) Empty_t))"
        ).by(
            PROV_HF_DT_MP,
            eq_term, f"In_a ({A}) ({insert_AB})",
            f"In_a ({A}) Empty_t",
            CONJ(
                p.fact("h_f_eq"),
                CONJ(
                    p.fact("h_f_in_A_ins"),
                    CONJ(
                        p.fact("h_f_in_A_emp"),
                        CONJ(p.fact("h_drop_hf2"), p.fact("h_imp_phi_phi_pos")),
                    ),
                ),
            ),
        )
        # PROV_HF_CONTRAP at (Eq, In A Empty) -- implication form.
        p.have(
            f"h_contrap: Prov_HF (Imp_f "
            f"(Not_f (In_a ({A}) Empty_t)) "
            f"(Not_f ({eq_term})))"
        ).by(
            PROV_HF_CONTRAP,
            eq_term, f"In_a ({A}) Empty_t",
            CONJ(
                p.fact("h_f_eq"),
                CONJ(
                    p.fact("h_f_in_A_emp"),
                    p.fact("h_imp_eq_in_emp"),
                ),
            ),
        )
        p.have(f"h_qhf_neq: Prov_HF (Not_f ({eq_term}))").by(
            PROV_HF_MP,
            f"Not_f (In_a ({A}) Empty_t)",
            f"Not_f ({eq_term})",
            CONJ(p.fact("h_hf1"), p.fact("h_contrap")),
        )


@proof
def QUOTE_HF_PROV_NEQ(p):
    """|- !s t. ~(s = t) ==>
                Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))).

    Strong induction on ``s``.  Four-way case-split on (s=0)/(t=0):

      * (s=0 ∧ t=0):     contradicts ~(s = t).
      * (s=0 ∧ t≠0):     quote_hf s = Empty_t, quote_hf t = Insert_t _ _.
                         Discriminate via HF1_INST (¬In Empty) + HF2_INST
                         (In a (Insert a b)) + PROV_HF_SUBST_EQ + the
                         propositional toolkit (HYP_DROP, DT_MP, CONTRAP,
                         DNI).  ``_empty_neq_insert_quotes`` does the heavy
                         lifting.
      * (s≠0 ∧ t=0):     symmetric.
      * (s≠0 ∧ t≠0):     SORRY (residual gap).  Requires HF4_INST
                         (extensionality) plus a witness-construction
                         argument: pick a discriminating element of
                         (Insert_t a c) ∆ (Insert_t b d) and run
                         HF4 contrapositively.  Estimated ~250-400 lines
                         of additional infrastructure (HF4_INST itself,
                         plus an ``Insert_t`` injectivity lemma at the
                         Prov_HF level).

    Why the (s=0)-cases work without HF4 -- they reduce to discriminating
    Empty_t from Insert_t _ _, which HF1 + HF2 + PROV_HF_SUBST_EQ already
    decide.  The (s≠0, t≠0) case has to discriminate two Insert_t towers
    with potentially distinct heads or tails; HF1 + HF2 + HF3 alone do
    not suffice (HF3 reduces ``a ∈ Insert_t b d`` to ``a ∈ d`` under
    ``a ≠ b``, which leaves the membership question recursive without
    an extensionality fixpoint).
    """
    p.goal(
        "!s t. ~(s = t) ==> "
        "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))",
        types={"s": nat0_ty, "t": nat0_ty},
    )
    with p.strong_induction("s", "IH"):
        p.fix("t")
        p.assume("h_neq: ~(s = t)")
        with p.cases_on(EXCLUDED_MIDDLE, "s = 0"):
            with p.case("hsz: s = 0"):
                with p.cases_on(EXCLUDED_MIDDLE, "t = 0"):
                    with p.case("htz: t = 0"):
                        # Both 0 contradicts ~(s = t).
                        from fusion import ASSUME
                        from tactics import DISCH, NOT_INTRO, NOT_ELIM
                        eq_st = TRANS(p.fact("hsz"), SYM(p.fact("htz")))
                        contra = MP(NOT_ELIM(p.fact("h_neq")), eq_st)
                        p.thus(
                            "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
                        ).by_thm(
                            CONTR(
                                p._parse(
                                    "Prov_HF (Not_f (Eq_f "
                                    "(quote_hf s) (quote_hf t)))"
                                ),
                                contra,
                            )
                        )
                    with p.case("htnz: ~(t = 0)"):
                        # quote_hf s = Empty_t, quote_hf t = Insert_t (q lb_t) (q cl_t).
                        p.have("h_qs: quote_hf s = Empty_t").by_rewrite(
                            ["hsz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                        )
                        p.have(
                            "h_qt: quote_hf t = "
                            "Insert_t (quote_hf (low_bit t)) "
                            "         (quote_hf (clear_low t))"
                        ).by(_QUOTE_HF_AT_NZ, "t", "htnz")
                        # Build the Empty_t-on-the-left discriminator.
                        _empty_neq_insert_quotes(
                            p, "low_bit t", "clear_low t", "htnz",
                            dir_left_zero=True,
                        )
                        p.thus(
                            "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
                        ).by_rewrite_of(
                            "h_qhf_neq",
                            [SYM(p.fact("h_qs")), SYM(p.fact("h_qt"))],
                        )
            with p.case("hsnz: ~(s = 0)"):
                with p.cases_on(EXCLUDED_MIDDLE, "t = 0"):
                    with p.case("htz: t = 0"):
                        # Symmetric: quote_hf t = Empty_t, quote_hf s = Insert_t _ _.
                        p.have("h_qt: quote_hf t = Empty_t").by_rewrite(
                            ["htz", SYM(EMPTY_DEF), QUOTE_HF_AT_EMPTY]
                        )
                        p.have(
                            "h_qs: quote_hf s = "
                            "Insert_t (quote_hf (low_bit s)) "
                            "         (quote_hf (clear_low s))"
                        ).by(_QUOTE_HF_AT_NZ, "s", "hsnz")
                        # Build the Empty_t-on-the-right discriminator.
                        _empty_neq_insert_quotes(
                            p, "low_bit s", "clear_low s", "hsnz",
                            dir_left_zero=False,
                        )
                        p.thus(
                            "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))"
                        ).by_rewrite_of(
                            "h_qhf_neq",
                            [SYM(p.fact("h_qs")), SYM(p.fact("h_qt"))],
                        )
                    with p.case("htnz: ~(t = 0)"):
                        # Both non-zero.  Bit-decompose s and t.
                        #
                        # By INSERT_LOW_BIT_CLEAR_LOW + ~(s = t), at
                        # least one of (low_bit s, clear_low s) and
                        # (low_bit t, clear_low t) differs.  EXCLUDED_MIDDLE
                        # on ``low_bit s = low_bit t``:
                        #   * different heads      → IH on low_bit s,
                        #                            QUOTE_HF_NEQ_FROM_LOW_BIT.
                        #   * matching heads       → tails must differ
                        #                            (else s = t); IH on
                        #                            clear_low s,
                        #                            QUOTE_HF_NEQ_FROM_CLEAR_LOW.
                        p.have("h_lb_lt: nat0_lt (low_bit s) s").by(
                            LOW_BIT_LT, "s", "hsnz"
                        )
                        p.have("h_cl_lt: nat0_lt (clear_low s) s").by(
                            CLEAR_LOW_LT, "s", "hsnz"
                        )
                        with p.cases_on(
                            EXCLUDED_MIDDLE, "low_bit s = low_bit t"
                        ):
                            with p.case("hlb_eq: low_bit s = low_bit t"):
                                # Tails must differ.  Use INSERT_LOW_BIT_CLEAR_LOW
                                # to derive ~(clear_low s = clear_low t)
                                # from ~(s = t).
                                p.have(
                                    "h_recon_s: s = "
                                    "set_bit (low_bit s) (clear_low s)"
                                ).by(INSERT_LOW_BIT_CLEAR_LOW, "s", "hsnz")
                                p.have(
                                    "h_recon_t: t = "
                                    "set_bit (low_bit t) (clear_low t)"
                                ).by(INSERT_LOW_BIT_CLEAR_LOW, "t", "htnz")
                                with p.cases_on(
                                    EXCLUDED_MIDDLE,
                                    "clear_low s = clear_low t",
                                ):
                                    with p.case(
                                        "hcl_eq: clear_low s = clear_low t"
                                    ):
                                        # Heads + tails match → s = t,
                                        # contradicts h_neq.
                                        p.have("h_st: s = t").by_rewrite_of(
                                            "h_recon_s",
                                            [
                                                "hlb_eq", "hcl_eq",
                                                SYM(p.fact("h_recon_t")),
                                            ],
                                        )
                                        contra = MP(
                                            NOT_ELIM(p.fact("h_neq")),
                                            p.fact("h_st"),
                                        )
                                        p.thus(
                                            "Prov_HF (Not_f (Eq_f "
                                            "(quote_hf s) (quote_hf t)))"
                                        ).by_thm(
                                            CONTR(
                                                p._parse(
                                                    "Prov_HF (Not_f (Eq_f "
                                                    "(quote_hf s) "
                                                    "(quote_hf t)))"
                                                ),
                                                contra,
                                            )
                                        )
                                    with p.case(
                                        "hcl_ne: ~(clear_low s = clear_low t)"
                                    ):
                                        # Tails differ at HOL.  IH on
                                        # clear_low s gives Prov_HF Not_f
                                        # Eq_f at the tails; lift via
                                        # QUOTE_HF_NEQ_FROM_CLEAR_LOW.
                                        p.have(
                                            "h_tail_neq: Prov_HF (Not_f "
                                            "(Eq_f (quote_hf (clear_low s)) "
                                            "      (quote_hf (clear_low t))))"
                                        ).by(
                                            "IH",
                                            "clear_low s",
                                            "h_cl_lt",
                                            "clear_low t",
                                            "hcl_ne",
                                        )
                                        p.thus(
                                            "Prov_HF (Not_f (Eq_f "
                                            "(quote_hf s) (quote_hf t)))"
                                        ).by(
                                            QUOTE_HF_NEQ_FROM_CLEAR_LOW,
                                            "s", "t",
                                            CONJ(
                                                p.fact("hsnz"),
                                                CONJ(
                                                    p.fact("htnz"),
                                                    CONJ(
                                                        p.fact("hlb_eq"),
                                                        p.fact("h_tail_neq"),
                                                    ),
                                                ),
                                            ),
                                        )
                            with p.case("hlb_ne: ~(low_bit s = low_bit t)"):
                                # Heads differ.  IH on low_bit s.
                                p.have(
                                    "h_head_neq: Prov_HF (Not_f "
                                    "(Eq_f (quote_hf (low_bit s)) "
                                    "      (quote_hf (low_bit t))))"
                                ).by(
                                    "IH",
                                    "low_bit s",
                                    "h_lb_lt",
                                    "low_bit t",
                                    "hlb_ne",
                                )
                                p.thus(
                                    "Prov_HF (Not_f (Eq_f "
                                    "(quote_hf s) (quote_hf t)))"
                                ).by(
                                    QUOTE_HF_NEQ_FROM_LOW_BIT,
                                    "s", "t",
                                    CONJ(
                                        p.fact("hsnz"),
                                        CONJ(
                                            p.fact("htnz"),
                                            p.fact("h_head_neq"),
                                        ),
                                    ),
                                )


# ---------------------------------------------------------------------------
# IS_IN_REPRESENTS_TH -- the discharged twin of hf_repr.IS_IN_REPRESENTS.
#
# Same statement; proved by HF_INDUCTION on ``y`` with ``x`` fixed.
# Lives here (downstream of hf_logic) so the propositional Prov_HF
# toolkit (PROV_HF_AND_INTRO/ELIM, PROV_HF_CONTRAP, PROV_HF_DOUBLE_NEG_*,
# PROV_HF_TRANS_IMP, PROV_HF_MP) is in scope.
#
# DSL friction: the substitute reductions inside the body have to
# unfold both ``var_x`` and ``var_y`` to ``Var_t 0`` / ``Var_t (SUC0 0)``
# before the SUBSTITUTE_AT_* lemmas fire (same simp normalisation as in
# HF2_INST above). Once that's done, SUBSTITUTE_QUOTE_HF flattens the
# ``quote_hf x`` slot through any subsequent substitute. The outer
# substitute reduction is identical for the positive and negative
# directions; factor it out as ``h_subst_red`` shared between branches.
# ---------------------------------------------------------------------------


@proof
def IS_IN_REPRESENTS_TH(p):
    """|- !x y. (In x y ==> Prov_HF (substitute (substitute is_In_internal
                                       (quote_hf x) idx_x)
                                       (quote_hf y) idx_y))
              /\\ (~In x y ==> Prov_HF (Not_f (substitute (substitute
                                       is_In_internal
                                       (quote_hf x) idx_x)
                                       (quote_hf y) idx_y))).

    SORRY (consumer body; ~80-100 lines on top of HF1_INST, HF2_INST,
    HF3_INST, QUOTE_HF_INJ, QUOTE_HF_PROV_NEQ).

    Proof outline -- HF_INDUCTION on ``y`` with predicate
        P y := (In x y ==> Prov_HF F[y])
            /\\ (~In x y ==> Prov_HF (Not_f F[y]))
    where F[y] = substitute (substitute is_In_internal (quote_hf x)
                              idx_x) (quote_hf y) idx_y.

    Outer substitute reduction (shared by base + step):
        substitute (substitute (In_a var_x var_y) (quote_hf x) idx_x)
                                                  (quote_hf y) idx_y
        = substitute (In_a (quote_hf x) var_y) (quote_hf y) idx_y
                                            [SUBSTITUTE_AT_IN +
                                             SUBSTITUTE_QUOTE_HF +
                                             var-HIT for var_x]
        = In_a (quote_hf x) (quote_hf y)    [SUBSTITUTE_AT_IN +
                                             SUBSTITUTE_QUOTE_HF +
                                             var-HIT for var_y]

    Base (y = Empty):
        F[Empty] reduces to In_a (quote_hf x) Empty_t (using
        QUOTE_HF_AT_EMPTY).
        + positive: In x Empty contradicts NOT_IN_EMPTY -- vacuous.
        + negative: HF1_INST at quote_hf x with IS_TERM_QUOTE_HF gives
          Prov_HF (Not_f (In_a (quote_hf x) Empty_t)) directly.

    Step (y = Insert i s under canonical-form precond):
        QUOTE_HF_AT_INSERT_LOW unfolds quote_hf (Insert i s) to
        Insert_t (quote_hf i) (quote_hf s); F[Insert i s] reduces to
        In_a (quote_hf x) (Insert_t (quote_hf i) (quote_hf s)).

        The IH supplies P s = (In x s ==> Prov_HF F[s])
                             /\\ (~In x s ==> Prov_HF (Not_f F[s])).

        Case-split on x = i via EXCLUDED_MIDDLE:

          x = i:
            + positive: In x (Insert i s) holds (IN_INSERT_SAME).
              HF2_INST(quote_hf i, quote_hf s, IS_TERM_QUOTE_HF i,
              IS_TERM_QUOTE_HF s, SUBSTITUTE_QUOTE_HF on idx_y) gives
              Prov_HF (In_a (quote_hf i) (Insert_t (quote_hf i)
                                                    (quote_hf s)));
              quote_hf x = quote_hf i (by x = i) closes.
            + negative: ~In x (Insert i s) is false (since x = i =>
              In x (Insert i s)) -- vacuous.

          ~(x = i):
            QUOTE_HF_INJ contrapositive: ~(quote_hf x = quote_hf i).
            QUOTE_HF_PROV_NEQ: Prov_HF (Not_f (Eq_f (quote_hf i)
                                                     (quote_hf x))).
            HF3_INST(quote_hf i, quote_hf x, quote_hf s, ...) gives
              Prov_HF (Imp_f (Not_f (Eq_f (quote_hf i) (quote_hf x)))
                              (Not_f (Imp_f
                                 (Imp_f (In_a x (Insert_t i s))
                                        (In_a x s))
                                 (Not_f (Imp_f (In_a x s)
                                                (In_a x (Insert_t
                                                          i s)))))))
            (with the variable names referring to the quoted images).
            One PROV_HF_MP gives the iff body.

            + positive: In x (Insert i s), with ~(x = i), reduces to
              In x s by IN_INSERT_DIFF. IH+ gives Prov_HF F[s] =
              Prov_HF (In_a (quote_hf x) (quote_hf s)). Lift through
              the right-to-left direction of HF3's biconditional:
              extract Q -> P by AND_ELIM_RIGHT (after PROV_HF_DOUBLE_NEG_ELIM
              of the outer Not_f), then PROV_HF_MP delivers the goal.
            + negative: ~In x (Insert i s), with ~(x = i), reduces to
              ~In x s. IH- gives Prov_HF (Not_f F[s]). Use the left-to-
              right direction of HF3 contrapositively: P -> Q in HF3
              gives ~Q -> ~P, which combined with IH- yields ~(In_a x
              (Insert_t i s)).

    Status: deferred. All five named prerequisites are stated above;
    HF1_INST and HF2_INST are real proofs, the rest are SORRYs with
    expansion sketches.
    """
    p.goal(
        "!x y. (In x y ==> Prov_HF (substitute (substitute "
        "  is_In_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y)) "
        "/\\ (~(In x y) ==> Prov_HF (Not_f (substitute (substitute "
        "  is_In_internal (quote_hf x) idx_x) "
        "  (quote_hf y) idx_y)))"
    )
    p.sorry()


if __name__ == "__main__":
    from parser import pp_thm

    print("Stage B1.0(c) part 2 -- IS_IN_REPRESENTS prerequisites.")
    print("    IS_TERM_VAR_X :", pp_thm(IS_TERM_VAR_X))
    print("    IS_TERM_VAR_Y :", pp_thm(IS_TERM_VAR_Y))
    print("    IS_TERM_VAR_Z :", pp_thm(IS_TERM_VAR_Z))
    print("    HF1_INST      :", pp_thm(HF1_INST))
    print("    HF2_INST      :", pp_thm(HF2_INST))
    print("    HF3_INST      :", pp_thm(HF3_INST))
    print("    QUOTE_HF_INJ  :", pp_thm(QUOTE_HF_INJ))
    print("    HF4_INST (SORRY)               :", pp_thm(HF4_INST))
    print(
        "    QUOTE_HF_NEQ_FROM_LOW_BIT (SORRY) :",
        pp_thm(QUOTE_HF_NEQ_FROM_LOW_BIT),
    )
    print(
        "    QUOTE_HF_NEQ_FROM_CLEAR_LOW (SORRY) :",
        pp_thm(QUOTE_HF_NEQ_FROM_CLEAR_LOW),
    )
    print("    QUOTE_HF_PROV_NEQ              :", pp_thm(QUOTE_HF_PROV_NEQ))
    print("    IS_IN_REPRESENTS_TH (SORRY) :", pp_thm(IS_IN_REPRESENTS_TH))
