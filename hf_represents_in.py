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
    CONJ,
    DISJ1,
    EQT_ELIM,
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
    SUBSTITUTE_AT_VAR_HIT,
    SUBSTITUTE_AT_VAR_MISS,
    SUBSTITUTE_AT_FORALL_MISS,
    IS_FORM_AT_NOT,
    IS_FORM_AT_IN,
    IS_FORM_AT_FORALL,
    IS_TERM_AT_VAR,
)
from hf_repr import (
    PROV_HF_AXIOM,
    IS_TERM_EMPTY,
    IS_TERM_INSERT,
)
from hf_logic import PROV_HF_UI


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
    at (a, b, c). The encoded biconditional spells out as
        ~ ((P -> Q) -> ~(Q -> P))
    where P := In_a b (Insert_t a c) and Q := In_a b c.

    SORRY (mechanical, ~150 lines on top of HF1/HF2_INST).

    Proof outline -- three UI steps with substitute reductions:

      Step 1. Lift |- is_hf_axiom HF3_axiom to |- Prov_HF HF3_axiom via
              ``_prov_of_hf_axiom``, then unfold HF3_AXIOM_DEF.

      Step 2. Build ``is_form`` for each Forall_f layer's body, bottom-up
              from IS_TERM_VAR_{X,Y,Z}, IS_FORM_AT_{EQ,NOT,IMP,IN,FORALL}.
              Three layers (B0 = innermost body, B1 = Forall_f (SUC0 SUC0 0)
              B0, B2 = Forall_f (SUC0 0) B1) -- ~30 lines of CONJ chains.

      Step 3. UI 1 at (0, B2, a): PROV_HF_UI peels the outermost Forall_f
              and yields ``Prov_HF (substitute B2 a 0)``. Reduce
              symbolically:
                * SUBSTITUTE_AT_FORALL_MISS (cond ~(0 = SUC0 0),
                  ~(0 = SUC0 (SUC0 0))) walks past the two inner Forall_f's;
                * SUBSTITUTE_AT_{IMP,NOT,EQ,IN,INSERT} push through B0;
                * leaf rewrites: var_x → a (HIT), var_y unchanged (MISS),
                  var_z unchanged (MISS).
              Result: ``Prov_HF (Forall_f (SUC0 0) (Forall_f (SUC0 SUC0 0)
              B0[a/var_x]))``.

      Step 4. UI 2 at (SUC0 0, B1[a/var_x], b): same pattern. The
              outer FORALL_MISS at SUC0 (SUC0 0) ≠ SUC0 0 walks past the
              innermost Forall_f, then leaf rewrites: substitute(a, b,
              SUC0 0) = a (precond h_ab); var_y → b (HIT); var_z
              unchanged (MISS).
              Result: ``Prov_HF (Forall_f (SUC0 SUC0 0) B0[a/var_x,
              b/var_y])``.

      Step 5. UI 3 at (SUC0 SUC0 0, B0[a/var_x, b/var_y], c): leaf
              rewrites: substitute(a, c, SUC0 SUC0 0) = a (precond
              h_ac); substitute(b, c, SUC0 SUC0 0) = b (precond h_bc);
              var_z → c (HIT).
              Result: the desired closed-form Imp_f tree.

    Each FORALL_MISS firing requires a specialised conditional rewrite
    (the unconditional form is built by MP'ing the AT-equation with the
    matching index inequality from {_neq_0_s0, _neq_0_ss0, _neq_s0_ss0}).
    The structure mirrors HF2_INST -- only the body is bigger.

    Status: deferred. Marked SORRY for now so downstream IS_IN_REPRESENTS
    work can proceed with a clean interface; mechanically expandable
    via the same ``by_rewrite_of`` discipline used in HF2_INST.
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
    p.sorry()


# ---------------------------------------------------------------------------
# QUOTE_HF_INJ -- HOL-level injectivity of the quoting map.
# ---------------------------------------------------------------------------


@proof
def QUOTE_HF_INJ(p):
    """|- !s t. quote_hf s = quote_hf t ==> s = t.

    SORRY (~80-120 lines, all HOL-level).

    Proof outline -- strong induction on ``s`` (predicate
    ``\\s. !t. quote_hf s = quote_hf t ==> s = t``); IH at ``u`` gives
    ``!t'. quote_hf u = quote_hf t' ==> u = t'`` for any ``u``
    nat0-less than s. After ``p.fix("t")`` and assuming the
    quote_hf-equation, case-split on ``s = 0`` and (separately)
    ``t = 0`` via EXCLUDED_MIDDLE, yielding four branches:

      * (s = 0 /\\ t = 0): ``s = 0 = t`` is immediate.
      * (s = 0 /\\ ~(t = 0)):
            quote_hf s = Empty_t                [QUOTE_HF_AT_EMPTY +
                                                  EMPTY_DEF on hsz]
            quote_hf t = Insert_t (quote_hf (low_bit t))
                                  (quote_hf (clear_low t))
                                                [_QUOTE_HF_AT_NZ on htnz]
        The quote_hf equation forces ``Empty_t = Insert_t _ _``, which
        contradicts ``INSERT_T_NEQ_EMPTY``. Discharge via NOT_ELIM +
        CONTR.
      * (~(s = 0) /\\ t = 0): symmetric to the above (flip sides via
        SYM on h_qeq, then run the previous case).
      * (~(s = 0) /\\ ~(t = 0)):
            quote_hf s = Insert_t (quote_hf (low_bit s))
                                  (quote_hf (clear_low s))     [(*1*)]
            quote_hf t = Insert_t (quote_hf (low_bit t))
                                  (quote_hf (clear_low t))     [(*2*)]
        Combine (*1*), (*2*), and h_qeq to get
            Insert_t (quote_hf (low_bit s)) (quote_hf (clear_low s)) =
            Insert_t (quote_hf (low_bit t)) (quote_hf (clear_low t)).
        ``INSERT_T_INJ`` peels both sides:
            quote_hf (low_bit s) = quote_hf (low_bit t)        [eq_lb_q]
            quote_hf (clear_low s) = quote_hf (clear_low t)    [eq_cl_q]
        Both sub-quantities are nat0-less than s
        (LOW_BIT_LT, CLEAR_LOW_LT under hsnz), so the IH fires twice:
            low_bit s = low_bit t                              [eq_lb]
            clear_low s = clear_low t                          [eq_cl]
        Reconstruct s and t via INSERT_LOW_BIT_CLEAR_LOW:
            s = set_bit (low_bit s) (clear_low s)             [hsnz]
              = set_bit (low_bit t) (clear_low t)             [eq_lb, eq_cl]
              = t                                              [SYM htnz]
        which closes the case.

    The four-way split mirrors the structure of QUOTE_HF_AT_EMPTY +
    _QUOTE_HF_AT_NZ. INSERT_T_INJ and INSERT_T_NEQ_EMPTY are pre-built
    in hf_syntax.py (constructor injectivity / disjointness).

    Status: deferred. The proof reduces entirely to existing primitives
    (no SORRY underneath); marked here to keep IS_IN_REPRESENTS_TH's
    interface clean while the hand-written reduction is filled in.
    """
    p.goal(
        "!s t. quote_hf s = quote_hf t ==> s = t",
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


@proof
def QUOTE_HF_PROV_NEQ(p):
    """|- !s t. ~(s = t) ==>
                Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t))).

    SORRY (~120-160 lines, the deepest sub-proof in the IS_IN_REPRESENTS
    chain).

    Why this is needed -- the ``x != i`` branch of IS_IN_REPRESENTS
    needs to lift the *HOL-level* inequality ``~(i = x)`` into a *Prov_HF*
    fact ``Prov_HF (Not_f (Eq_f (quote_hf i) (quote_hf x)))`` to
    discharge HF3's antecedent. PROV_HF_REFL only delivers
    ``Prov_HF (Eq_f t t)``; nothing in the propositional Prov_HF toolkit
    bridges HOL inequality to Prov_HF inequality without an explicit
    structural induction.

    Proof outline -- strong induction on ``max(s, t)`` (HOL-side; we
    shift to ``s`` after a SYM-flip so the smaller of the two indexes
    the induction). Cases via EXCLUDED_MIDDLE on ``s = 0`` and ``t = 0``:

      * (s = 0 /\\ t = 0): contradicts ``~(s = t)``.
      * (s = 0 /\\ ~(t = 0)):
            quote_hf s = Empty_t                  [QUOTE_HF_AT_EMPTY]
            quote_hf t = Insert_t (quote_hf (low_bit t))
                                  (quote_hf (clear_low t))
                                                  [_QUOTE_HF_AT_NZ]
        Reduce to ``Prov_HF (Not_f (Eq_f Empty_t (Insert_t _ _)))`` --
        a closed inequality of two distinct HF-syntax shapes.
        Provable from HF1 + HF2:
            HF1_INST(quote_hf low_bit_t):
                Prov_HF (Not_f (In_a (quote_hf low_bit_t) Empty_t))
            HF2_INST(quote_hf low_bit_t, quote_hf clear_low_t, ...):
                Prov_HF (In_a (quote_hf low_bit_t)
                              (Insert_t (quote_hf low_bit_t)
                                         (quote_hf clear_low_t)))
        If Empty_t = Insert_t _ _ at the Prov_HF level (assumed via
        contradiction), then In_a (quote_hf low_bit_t) Empty_t would
        hold, contradicting HF1. Lift via PROV_HF_CONTRAP +
        PROV_HF_SUBST_EQ.

      * (~(s = 0) /\\ t = 0): symmetric.

      * (~(s = 0) /\\ ~(t = 0)):
        Two sub-cases on whether the ``low_bit``s match:
          - low_bit s = low_bit t: then clear_low s != clear_low t
            (otherwise s = t by INSERT_LOW_BIT_CLEAR_LOW). IH at
            (clear_low s, clear_low t) gives Prov_HF inequality of
            their quotes, then HF4 (extensionality) lifts the tail
            inequality to whole-Insert_t inequality.
          - low_bit s != low_bit t: similar IH at the heads, then
            HF2_INST + HF1_INST contrapositively distinguishes the two
            sets via membership of the smaller head.

    HF4_INST (extensionality) is itself a fresh derived rule, ~80 lines.
    The full chain (this proof + HF3_INST + HF4_INST + QUOTE_HF_INJ) is
    ~400 lines of new theory.

    Status: deferred. Expected discharge via the structural induction
    above; no SORRY beneath once HF3_INST and HF4_INST are built.
    """
    p.goal(
        "!s t. ~(s = t) ==> "
        "Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))",
        types={"s": nat0_ty, "t": nat0_ty},
    )
    p.sorry()


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
    print("    HF3_INST (SORRY)         :", pp_thm(HF3_INST))
    print("    QUOTE_HF_INJ (SORRY)     :", pp_thm(QUOTE_HF_INJ))
    print("    QUOTE_HF_PROV_NEQ (SORRY):", pp_thm(QUOTE_HF_PROV_NEQ))
    print("    IS_IN_REPRESENTS_TH (SORRY) :", pp_thm(IS_IN_REPRESENTS_TH))
