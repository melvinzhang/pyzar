"""Church-Rosser confluence for SK via parallel reduction.

Takahashi's complete-development function ``sk_bullet`` + triangle property
+ Tait/Martin-Loef diamond + Church-Rosser confluence on ``sk_par_step``.
Also bundles ``PAR_STEPS_TRANS`` and the ``NORMAL_STABILITY_*`` lemmas.

This stage originally powered ``HALTS_INVARIANT`` (invariance of halting
under parallel reduction).  ``halting.py``'s Stage 2.5 introduces
``par_conv`` and bypasses confluence entirely; this module is preserved
as a standalone confluence proof, no longer on the path to
``HALTING_UNDECIDABLE``.

Exported headline theorems (not currently consumed elsewhere):
  * ``SK_BULLET_TRIANGLE``  : !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A)
  * ``PAR_STEP_DIAMOND``    : Tait/Martin-Loef diamond for sk_par_step
  * ``PAR_STEPS_CONFLUENT`` : Church-Rosser for sk_par_steps
  * ``PAR_STEPS_TRANS``     : transitivity of sk_par_steps
  * ``NORMAL_STABILITY_PAR_STEP`` / ``NORMAL_STABILITY_PAR_STEPS``
"""

from fusion import Var
from basics import mk_const, mk_app, mk_abs, mk_eq, rand, rator, aconv
from parser import define, parse_type, pp
from nat0 import nat0_ty, ZERO, mk_suc0
from nat0_order import define_wf_lt, NAT0_LT_TRANS
from proof import proof, define_with_at, register_intro_set
from tactics import REFL, SPEC, SPECL, SYM, EQ_MP, DISJ1, DISJ2, CONJ, EXISTS, MP
from tactics import AP_TERM, TRANS, BETA_NORM, unfold_def_at
from axioms import mk_exists
from hf_sets import Pair_ord
from hf_syntax import (
    _proof_lt_binary_left,
    _proof_lt_binary_right,
    _unfold_rec_via_F_def,
    mono_iff_binary_step,
)
from tactics import or_chain_collapse
from hf_syntax import _proof_binary_inj, _TAG_NEQS  # noqa: E402
from hf_sets import PAIR_ORD_INJ  # noqa: E402
from tactics import CONJUNCT1  # noqa: E402

# Stage 0/1/IS_NORMAL symbols carried over from halting.py.
from halting import (
    S_t, K_t, App_t,
    APP_T_INJ, S_T_NEQ_K_T, S_T_NEQ_APP_T, K_T_NEQ_APP_T,
    NAT0_LT_APP_T_L, NAT0_LT_APP_T_R,
    sk_par_step, sk_par_steps,
    SK_PAR_STEP_DEF, SK_PAR_STEPS_DEF,
    PAR_REFL, PAR_K, PAR_S, PAR_APP,
    PAR_STEPS_REFL, PAR_STEPS_STEP,
    PAR_STEP_S_T_INV, PAR_STEP_K_T_INV,
    is_normal, IS_NORMAL_DEF,
)
# Stage-1 private helpers that Stage 2 reuses.
from halting import (
    _PAR_STEP_CLOSURE,
    _nat0_fn_ty,
    _atom_neq_App_negations,
    _lift_select_eq,
    _select_via_rec,
)


# Stage 2 -- Takahashi's complete-development function ``sk_bullet``.
#
# Defined by well-founded recursion on Pair_ord depth (via
# ``define_wf_lt``).  Contracts every redex visible at a node
# simultaneously:
#
#     sk_bullet S_t                          = S_t
#     sk_bullet K_t                          = K_t
#     sk_bullet (App_t (App_t K_t X) Y)      = sk_bullet X
#     sk_bullet (App_t (App_t (App_t S_t X) Y) Z)
#       = App_t (App_t (sk_bullet X) (sk_bullet Z))
#               (App_t (sk_bullet Y) (sk_bullet Z))
#     sk_bullet (App_t X Y) [otherwise]      = App_t (sk_bullet X) (sk_bullet Y)
#
# The body is a SELECT over four guarded disjuncts (K-redex, S-redex,
# other-App, leaf).  Atom unfolds (S_t / K_t) fall into the leaf branch.
#
# The triangle property
#     SK_BULLET_TRIANGLE : !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A)
# is the headline lemma; ``TRIANGLE_EXISTS`` packages it as the
# existential consumed by ``PAR_STEP_DIAMOND`` / ``PAR_STEPS_STRIP`` /
# ``PAR_STEPS_CONFLUENT`` (Tait/Martin-Loef diamond + Church-Rosser).
# ---------------------------------------------------------------------------


_SK_BULLET_F_DEF = define(
    "_sk_bullet_F",
    parse_type("(nat0 -> nat0) -> nat0 -> nat0"),
    "\\f:nat0->nat0. \\t:nat0. "
    "@r:nat0. "
    "(?x y. t = App_t (App_t K_t x) y /\\ r = f x) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ?x y z. t = App_t (App_t (App_t S_t x) y) z /\\ "
    "         r = App_t (App_t (f x) (f z)) (App_t (f y) (f z))) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " (?a b. t = App_t a b /\\ r = App_t (f a) (f b))) \\/ "
    "(~(?x y. t = App_t (App_t K_t x) y) /\\ "
    " ~(?x y z. t = App_t (App_t (App_t S_t x) y) z) /\\ "
    " ~(?a b. t = App_t a b) /\\ r = t)",
)
_SK_BULLET_F = mk_const("_sk_bullet_F", [])


def _prove_sk_bullet_F_at():
    """|- !f t. _sk_bullet_F f t = body[f, t]  (two BETAs).

    Mirror of ``_prove_sk_step_F_at`` (halting.py:704).  AP_THM at f,
    BETA the resulting lambda; AP_THM at t, BETA again; GENL.
    """
    from tactics import AP_THM, BETA_CONV, TRANS, GENL
    f_var = Var("f", _nat0_fn_ty)
    t_var = Var("t", nat0_ty)
    th_f = AP_THM(_SK_BULLET_F_DEF, f_var)
    th_f_eq = TRANS(th_f, BETA_CONV(rand(th_f._concl)))
    th_ft = AP_THM(th_f_eq, t_var)
    th_ft_eq = TRANS(th_ft, BETA_CONV(rand(th_ft._concl)))
    return GENL([f_var, t_var], th_ft_eq)


_SK_BULLET_F_AT = _prove_sk_bullet_F_at()


# ---------------------------------------------------------------------------
# Per-disjunct mono iffs for the bullet body.
#
#   D1 (K-redex)   : single recurse under binary ?x y existential.
#   D2 (S-redex)   : ternary recurse under triple ?x y z existential.
#   D3 (other-App) : binary recurse under ?a b -- covered by the existing
#                    ``_mono_iff_value_binary_pw_step``.
#   D4 (leaf)      : f-free, REFL.
#
# D1 and D2 don't fit the existing helper's shape (D1 has only one
# recursive call buried under two binders; D2 has three recursive calls
# under three binders).  Both follow the same CHOOSE_WITNESS / LT chain
# / MP-hyp / EXISTS-repack template -- only the binder count, the LT
# chain depths, and the payload shape differ.
#
# Shared piece factored out as ``_lt_trans_chain``; the rest is inlined
# per-disjunct because the binder-count variation would force a generic
# combinator more complex than the direct code (the EXISTS repack
# requires per-depth predicate construction).
# ---------------------------------------------------------------------------


def _lt_trans_chain(lt_steps, n_eq_th):
    """TRANS-compose a list of LT hops into ``|- nat0_lt a0 n``.

    Args:
      lt_steps : list of theorems ``[|- nat0_lt a0 a1, |- nat0_lt a1 a2,
                  ..., |- nat0_lt a_{k-1} a_k]``.  Each step's right
                  must match the next step's left.
      n_eq_th  : ``|- n = a_k`` (rewriting the final endpoint to ``n``).

    Returns ``|- nat0_lt a0 n``.

    Two call sites (D1's depth-2 chain, D2's depth-{1,2,3} chains); the
    factored piece is the TRANS-fold + final ``REWRITE_RULE [SYM(n_eq)]``.
    """
    from tactics import MP, REWRITE_RULE, SPECL, SYM
    from nat0_order import NAT0_LT_TRANS
    chain = lt_steps[0]
    for s in lt_steps[1:]:
        a_t = rand(rator(chain._concl))
        m_t = rand(chain._concl)
        b_t = rand(s._concl)
        chain = MP(
            MP(SPECL([a_t, m_t, b_t], NAT0_LT_TRANS), chain),
            s,
        )
    return REWRITE_RULE([SYM(n_eq_th)], chain)


def _bullet_F_d1_mono_iff(hyp_th, r_term):
    """|- (?x y. n = App_t (App_t K_t x) y /\\ r = f x)
        = (?x y. n = App_t (App_t K_t x) y /\\ r = g x)
    where ``n, f, g`` are read from ``hyp_th`` and ``r := r_term``.

    Direction template (mirrors ``_mono_iff_value_binary_pw_step``):
      1. CHOOSE_WITNESS x (outer ?) then y (inner ?).
      2. Extract witnesses w_x, w_y from the conjuncts.
      3. LT chain: w_x < App_t K_t w_x [NAT0_LT_APP_T_R] < n [NAT0_LT_APP_T_L]
         (two steps, composed via ``_lt_trans_chain``).
      4. MP hyp at w_x → ``f w_x = g w_x``.
      5. REWRITE_RULE payload to flip ``r = f w_x`` ↔ ``r = g w_x``.
      6. Re-pack via two EXISTS.
      7. DEDUCT_ANTISYM_RULE the two directions.
    """
    from tactics import (
        SPEC, MP, SYM, CONJ, CONJUNCT1, CONJUNCT2,
        REWRITE_RULE, DEDUCT_ANTISYM_RULE, ASSUME,
        CHOOSE_WITNESS, SPECL,
    )
    from axioms import dest_exists, mk_and
    from hf_syntax import _extract_nfg

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    y_var = Var("y", k_ty)
    K_redex = mk_app(App_t, mk_app(App_t, K_t, x_var), y_var)

    def _body(fn):
        return mk_and(
            mk_eq(n_t, K_redex),
            mk_eq(r_term, mk_app(fn, x_var)),
        )

    body_l = _body(f_t)
    body_r = _body(g_t)
    LHS = mk_exists(x_var, mk_exists(y_var, body_l))
    RHS = mk_exists(x_var, mk_exists(y_var, body_r))

    def _direction(src, target_inner, target_fn, swap_fg):
        h_top = ASSUME(src)
        chosen_x = CHOOSE_WITNESS(dest_exists(src), h_top)
        chosen_y = CHOOSE_WITNESS(
            dest_exists(chosen_x._concl), chosen_x
        )
        n_eq_th = CONJUNCT1(chosen_y)
        payload = CONJUNCT2(chosen_y)
        # Extract witnesses from `n = App_t (App_t K_t w_x) w_y`.
        ctor_app = rand(n_eq_th._concl)
        w_y = rand(ctor_app)
        AppKwx = rand(rator(ctor_app))
        w_x = rand(AppKwx)
        # LT chain: w_x < App_t K_t w_x < App_t (App_t K_t w_x) w_y = n.
        lt_inner = SPECL([K_t, w_x], NAT0_LT_APP_T_R)
        lt_outer = SPECL([AppKwx, w_y], NAT0_LT_APP_T_L)
        lt_w_x_n = _lt_trans_chain([lt_inner, lt_outer], n_eq_th)
        # MP hyp at w_x; sym for the reverse direction.
        eq_at_wx = MP(SPEC(w_x, hyp_th), lt_w_x_n)
        if swap_fg:
            eq_at_wx = SYM(eq_at_wx)
        new_payload = REWRITE_RULE([eq_at_wx], payload)
        new_body = CONJ(n_eq_th, new_payload)
        # Re-pack: inner EXISTS over w_y, outer over w_x.
        outer_pred = mk_abs(x_var, mk_exists(y_var, target_inner))
        inner_pred_at_wx = mk_abs(
            y_var,
            mk_and(
                mk_eq(
                    n_t,
                    mk_app(App_t, mk_app(App_t, K_t, w_x), y_var),
                ),
                mk_eq(r_term, mk_app(target_fn, w_x)),
            ),
        )
        inner_th = EXISTS(inner_pred_at_wx, w_y, new_body)
        return EXISTS(outer_pred, w_x, inner_th)

    R_th = _direction(LHS, body_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


def _bullet_F_d2_mono_iff(hyp_th, r_term):
    """|- (?x y z. n = App_t (App_t (App_t S_t x) y) z /\\
                   r = App_t (App_t (f x) (f z)) (App_t (f y) (f z)))
        = (?x y z. ... same with g ...)
    where ``n, f, g`` come from ``hyp_th``.

    Same template as D1, scaled to three binders.  LT-chain depths:
      * z: 1 step  -- z < (App_t ... z) = n  via NAT0_LT_APP_T_R.
      * y: 2 steps -- y < App_t (App_t S_t x) y [R]
                         < (App_t (App_t (App_t S_t x) y) z) [L] = n.
      * x: 3 steps -- x < App_t S_t x [R]
                         < App_t (App_t S_t x) y [L]
                         < (App_t (App_t (App_t S_t x) y) z) [L] = n.

    All three LT-to-n facts feed independent ``MP(SPEC(w, hyp), ...)``
    calls; a single ``REWRITE_RULE`` with the three eqs simultaneously
    substitutes on the payload (which mentions ``f x, f y, f z``).
    """
    from tactics import (
        SPEC, MP, SYM, CONJ, CONJUNCT1, CONJUNCT2,
        REWRITE_RULE, DEDUCT_ANTISYM_RULE, ASSUME,
        CHOOSE_WITNESS, SPECL,
    )
    from axioms import dest_exists, mk_and
    from hf_syntax import _extract_nfg

    n_t, f_t, g_t, k_ty = _extract_nfg(hyp_th)
    x_var = Var("x", k_ty)
    y_var = Var("y", k_ty)
    z_var = Var("z", k_ty)
    AppSx = mk_app(App_t, S_t, x_var)
    AppAppSxy = mk_app(App_t, AppSx, y_var)
    S_redex = mk_app(App_t, AppAppSxy, z_var)

    def _val(fn):
        return mk_app(
            App_t,
            mk_app(App_t, mk_app(fn, x_var), mk_app(fn, z_var)),
            mk_app(App_t, mk_app(fn, y_var), mk_app(fn, z_var)),
        )

    def _body(fn):
        return mk_and(mk_eq(n_t, S_redex), mk_eq(r_term, _val(fn)))

    body_l = _body(f_t)
    body_r = _body(g_t)
    LHS = mk_exists(
        x_var, mk_exists(y_var, mk_exists(z_var, body_l))
    )
    RHS = mk_exists(
        x_var, mk_exists(y_var, mk_exists(z_var, body_r))
    )

    def _direction(src, target_inner, target_fn, swap_fg):
        h_top = ASSUME(src)
        chosen_x = CHOOSE_WITNESS(dest_exists(src), h_top)
        chosen_y = CHOOSE_WITNESS(
            dest_exists(chosen_x._concl), chosen_x
        )
        chosen_z = CHOOSE_WITNESS(
            dest_exists(chosen_y._concl), chosen_y
        )
        n_eq_th = CONJUNCT1(chosen_z)
        payload = CONJUNCT2(chosen_z)
        # Extract witnesses from
        #   n = App_t (App_t (App_t S_t w_x) w_y) w_z.
        outer_app = rand(n_eq_th._concl)
        w_z = rand(outer_app)
        mid_app = rand(rator(outer_app))  # App_t (App_t S_t w_x) w_y
        w_y = rand(mid_app)
        AppSwx = rand(rator(mid_app))      # App_t S_t w_x
        w_x = rand(AppSwx)
        # LT chains, all to n via _lt_trans_chain (which auto-rewrites
        # the final endpoint with SYM(n_eq_th)).
        lt_z = _lt_trans_chain(
            [SPECL([mid_app, w_z], NAT0_LT_APP_T_R)],
            n_eq_th,
        )
        lt_y = _lt_trans_chain(
            [
                SPECL([AppSwx, w_y], NAT0_LT_APP_T_R),
                SPECL([mid_app, w_z], NAT0_LT_APP_T_L),
            ],
            n_eq_th,
        )
        lt_x = _lt_trans_chain(
            [
                SPECL([S_t, w_x], NAT0_LT_APP_T_R),
                SPECL([AppSwx, w_y], NAT0_LT_APP_T_L),
                SPECL([mid_app, w_z], NAT0_LT_APP_T_L),
            ],
            n_eq_th,
        )
        eq_at_wx = MP(SPEC(w_x, hyp_th), lt_x)
        eq_at_wy = MP(SPEC(w_y, hyp_th), lt_y)
        eq_at_wz = MP(SPEC(w_z, hyp_th), lt_z)
        if swap_fg:
            eq_at_wx = SYM(eq_at_wx)
            eq_at_wy = SYM(eq_at_wy)
            eq_at_wz = SYM(eq_at_wz)
        # Simultaneous rewrite on the payload: three f-calls become
        # three g-calls (or vice versa for the reverse direction).
        new_payload = REWRITE_RULE(
            [eq_at_wx, eq_at_wy, eq_at_wz], payload
        )
        new_body = CONJ(n_eq_th, new_payload)
        # Re-pack: triple EXISTS.  Each predicate captures the previous
        # witnesses; only the current binder is free.
        outermost_pred = mk_abs(
            x_var,
            mk_exists(y_var, mk_exists(z_var, target_inner)),
        )
        # Compute target_inner with x:=w_x: substitute mentally; we
        # rebuild the term explicitly to avoid INST subtleties.
        AppSwx_t = mk_app(App_t, S_t, w_x)

        def _val_at(fn, x_t, y_t, z_t):
            return mk_app(
                App_t,
                mk_app(App_t, mk_app(fn, x_t), mk_app(fn, z_t)),
                mk_app(App_t, mk_app(fn, y_t), mk_app(fn, z_t)),
            )

        mid_pred_at_wx = mk_abs(
            y_var,
            mk_exists(
                z_var,
                mk_and(
                    mk_eq(
                        n_t,
                        mk_app(
                            App_t,
                            mk_app(App_t, AppSwx_t, y_var),
                            z_var,
                        ),
                    ),
                    mk_eq(
                        r_term,
                        _val_at(target_fn, w_x, y_var, z_var),
                    ),
                ),
            ),
        )
        AppAppSwxwy_t = mk_app(App_t, AppSwx_t, w_y)
        innermost_pred_at_wxwy = mk_abs(
            z_var,
            mk_and(
                mk_eq(
                    n_t,
                    mk_app(App_t, AppAppSwxwy_t, z_var),
                ),
                mk_eq(
                    r_term,
                    _val_at(target_fn, w_x, w_y, z_var),
                ),
            ),
        )
        z_ex = EXISTS(innermost_pred_at_wxwy, w_z, new_body)
        y_ex = EXISTS(mid_pred_at_wx, w_y, z_ex)
        return EXISTS(outermost_pred, w_x, y_ex)

    R_th = _direction(LHS, body_r, g_t, swap_fg=False)
    L_th = _direction(RHS, body_l, f_t, swap_fg=True)
    return DEDUCT_ANTISYM_RULE(L_th, R_th)


@proof
def SK_BULLET_MONO(p):
    """|- !f g n. (!k. nat0_lt k n ==> f k = g k)
                 ==> _sk_bullet_F f n = _sk_bullet_F g n.

    Stitch pattern (or_chain_collapse + _lift_select_eq + SPECL through
    ``_SK_BULLET_F_AT``).  Per-disjunct iffs:
      D1 (K-redex, single recurse)    -- ``_bullet_F_d1_mono_iff``.
      D2 (S-redex, ternary recurse)   -- ``_bullet_F_d2_mono_iff``;
                                         prepended with ``~K`` via
                                         AP_TERM(/\\) lift.
      D3 (other-App, binary recurse)  -- ``_mono_iff_value_binary_pw_step``;
                                         prepended with ``~K /\\ ~S`` via
                                         two AP_TERM(/\\) lifts.
      D4 (leaf, f-free)               -- REFL.

    DSL friction: the per-disjunct iffs return kernel theorems with
    ``r_var`` free.  ``or_chain_collapse`` consumes them as a list;
    ``_lift_select_eq`` ABSes over ``r_var`` and AP_TERMs through the
    polymorphic ``@``.  All four iffs must share the same free
    ``r_var`` -- we use the kernel ``Var("r", nat0_ty)`` consistently
    rather than reparsing.
    """
    from tactics import (
        AP_TERM as _AP_TERM,
        SPECL as _SPECL,
        TRANS as _TRANS,
        SYM as _SYM,
        or_chain_collapse as _or_collapse,
    )
    from hf_syntax import _mono_iff_value_binary_pw_step, _extract_nfg
    from fusion import mk_comb as _mk_comb
    from axioms import (
        mk_and as _mk_and,
        mk_not as _mk_not,
        mk_exists as _mk_exists,
    )
    from basics import mk_eq as _mk_eq

    p.goal(
        "!f g n. (!k. nat0_lt k n ==> f k = g k) "
        "==> _sk_bullet_F f n = _sk_bullet_F g n",
        types={
            "f": _nat0_fn_ty,
            "g": _nat0_fn_ty,
            "n": nat0_ty,
            "k": nat0_ty,
        },
    )
    p.fix("f g n")
    p.assume("h: !k. nat0_lt k n ==> f k = g k")
    h_th = p.fact("h")
    n_t, f_t, g_t, _k_ty = _extract_nfg(h_th)
    r_var = Var("r", nat0_ty)

    # K-shape, S-shape, App-shape -- needed for the ~-prefixes on
    # D2/D3 and the D4 disjunct body.  Bvars ``x, y, z, a, b`` match
    # the F_DEF body exactly (NOT the alpha-renamed ``a, b, c`` from
    # _sk_bullet_disjuncts -- those are for surface case-splits;
    # here we need term-level identity with the F_DEF for the SPECL
    # chain through _SK_BULLET_F_AT to align).
    x_v = Var("x", nat0_ty)
    y_v = Var("y", nat0_ty)
    z_v = Var("z", nat0_ty)
    a_v = Var("a", nat0_ty)
    b_v = Var("b", nat0_ty)
    K_redex_body = _mk_eq(
        n_t, mk_app(App_t, mk_app(App_t, K_t, x_v), y_v)
    )
    K_shape = _mk_exists(x_v, _mk_exists(y_v, K_redex_body))
    S_redex_body = _mk_eq(
        n_t,
        mk_app(App_t, mk_app(App_t, mk_app(App_t, S_t, x_v), y_v), z_v),
    )
    S_shape = _mk_exists(
        x_v, _mk_exists(y_v, _mk_exists(z_v, S_redex_body))
    )
    App_body = _mk_eq(n_t, mk_app(App_t, a_v, b_v))
    App_shape = _mk_exists(a_v, _mk_exists(b_v, App_body))
    AND_C = mk_const("/\\", [])

    # --- Per-disjunct iffs ------------------------------------------------

    # D1: bare existential with single recursion.
    eq_D1 = _bullet_F_d1_mono_iff(h_th, r_var)

    # D2: ~K /\ (S-existential with triple recursion).  AP_TERM lifts
    # the inner iff through the ~K conjunct.
    eq_D2_inner = _bullet_F_d2_mono_iff(h_th, r_var)
    eq_D2 = _AP_TERM(_mk_comb(AND_C, _mk_not(K_shape)), eq_D2_inner)

    # D3: ~K /\ ~S /\ (App-existential with binary recursion).  Uses
    # the existing generic binary helper; rest_builder produces the
    # payload ``r = App_t (fn a) (fn b)`` -- two AP_TERMs prepend
    # ~S then ~K.
    def _D3_rest_builder(fn, a_t, b_t, args):
        return _mk_eq(
            r_var,
            mk_app(App_t, mk_app(fn, a_t), mk_app(fn, b_t)),
        )

    eq_D3_inner = _mono_iff_value_binary_pw_step(
        App_t,
        NAT0_LT_APP_T_L,
        NAT0_LT_APP_T_R,
        h_th,
        args=[],
        rest_builder=_D3_rest_builder,
        recurses_l=True,
    )
    eq_D3_with_ns = _AP_TERM(
        _mk_comb(AND_C, _mk_not(S_shape)), eq_D3_inner
    )
    eq_D3 = _AP_TERM(_mk_comb(AND_C, _mk_not(K_shape)), eq_D3_with_ns)

    # D4: f-free leaf branch.  REFL of the full disjunct.
    D4 = _mk_and(
        _mk_not(K_shape),
        _mk_and(
            _mk_not(S_shape),
            _mk_and(_mk_not(App_shape), _mk_eq(r_var, n_t)),
        ),
    )
    eq_D4 = REFL(D4)

    # --- Stitch + lift + chain through F_AT -------------------------------

    body_eq_at_r = _or_collapse([eq_D1, eq_D2, eq_D3, eq_D4])
    select_eq = _lift_select_eq(r_var, body_eq_at_r)
    spec_f = _SPECL([f_t, n_t], _SK_BULLET_F_AT)
    spec_g = _SPECL([g_t, n_t], _SK_BULLET_F_AT)
    final = _TRANS(spec_f, _TRANS(select_eq, _SYM(spec_g)))

    p.thus("_sk_bullet_F f n = _sk_bullet_F g n").by_thm(final)


# Well-founded recursive definition.
#   SK_BULLET_DEF      : |- sk_bullet = (@h. !n. h n = _sk_bullet_F h n)
#   _SK_BULLET_REC_RAW : |- !n. sk_bullet n = _sk_bullet_F sk_bullet n
SK_BULLET_DEF, _SK_BULLET_REC_RAW = define_wf_lt(
    "sk_bullet",
    _nat0_fn_ty,
    _SK_BULLET_F,
    SK_BULLET_MONO,
)
sk_bullet = mk_const("sk_bullet", [])


# SK_BULLET_REC : |- !n. sk_bullet n = body[sk_bullet, n]
SK_BULLET_REC = _unfold_rec_via_F_def(_SK_BULLET_REC_RAW, _SK_BULLET_F_DEF)


def _sk_bullet_disjuncts(t, r):
    """Return the four disjunct strings of ``_sk_bullet_F``'s body at
    input ``t`` with the SELECT-bound variable substituted by ``r``.

    DSL friction: the F_DEF body uses ``x, y, z`` and ``a, b`` as the
    existential bvars, but unfold-lemma callers commonly fix surface
    vars ``X, Y, Z``.  We rename to ``a, b, c`` here (alpha-equivalent;
    REC is up to bvar renaming) so the case-split disjuncts can be
    pretty-printed without shadowing the surface vars.
    """
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    App_shape = f"?a b. {t} = App_t a b"
    D1 = f"(?a b. {t} = App_t (App_t K_t a) b /\\ {r} = sk_bullet a)"
    D2 = (
        f"(~({K_shape}) /\\ "
        f" ?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"         {r} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                     (App_t (sk_bullet b) (sk_bullet c)))"
    )
    D3 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ "
        f" (?a b. {t} = App_t a b /\\ "
        f"        {r} = App_t (sk_bullet a) (sk_bullet b)))"
    )
    D4 = (
        f"(~({K_shape}) /\\ ~({S_shape}) /\\ "
        f" ~({App_shape}) /\\ {r} = {t})"
    )
    return [D1, D2, D3, D4]


def _sk_bullet_body(t, r):
    return " \\/ ".join(_sk_bullet_disjuncts(t, r))


def _sk_bullet_select_at(p, t, witness_r, inner_branch_th):
    """Mirror of ``_sk_step_select_at`` for sk_bullet's 4-disjunct body.

    Combines: ``ex: ?r. body[t, r]`` (DISJ-chain + EXISTS) with
    ``_select_via_rec(SK_BULLET_REC, ...)`` to land on
    ``|- body[t, sk_bullet t]``.
    """
    body_at_r = _sk_bullet_body(t, witness_r)
    body_at_r_var = _sk_bullet_body(t, "r")
    p.have(f"_bullet_disj_rhs: {body_at_r}").by_disj(inner_branch_th)
    p.have(f"_bullet_ex: ?r. {body_at_r_var}").by_witness(
        witness_r, "_bullet_disj_rhs"
    )
    return _select_via_rec(SK_BULLET_REC, [p._parse(t)], p.fact("_bullet_ex"))


def _prove_sk_bullet_leaf(p, atom_str, atom_neq_lemma):
    """Shared body of SK_BULLET_S_T / SK_BULLET_K_T.  Proves
    ``sk_bullet <atom> = <atom>`` where ``atom`` is ``S_t`` or ``K_t``.

    D4 (leaf branch) fires at ``r := <atom>``: its payload is exactly
    ``r = t`` which is reflexive at this witness.  D1 / D2 / D3 all
    contain App_t-shaped existentials over ``t = <atom>``; each is
    refuted via ``_atom_neq_App_negations`` applied to ``atom_neq_lemma``.

    Direct mirror of ``_prove_sk_step_leaf`` (halting.py:2025) — the
    disjunct structure of bullet's body matches sk_step's at D1/D2/D3
    (App-shaped existentials, modulo payload) and at D4 (the leaf
    branch with ``r = t``).
    """
    from tactics import CONJ as _CONJ
    t = atom_str
    sk_t = f"sk_bullet {t}"
    nK_lbl, nS_lbl, nApp_lbl = _atom_neq_App_negations(p, t, atom_neq_lemma)
    # Leaf-disjunct inner: nK /\ nS /\ nApp /\ atom = atom (the r = t
    # payload, instantiated at r := atom, becomes the trivial REFL).
    p.have(
        f"inner_leaf: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f"~(?a b c. {t} = App_t (App_t (App_t S_t a) b) c) /\\ "
        f"~(?a b. {t} = App_t a b) /\\ {t} = {t}"
    ).by_thm(
        _CONJ(
            p.fact(nK_lbl),
            _CONJ(
                p.fact(nS_lbl),
                _CONJ(p.fact(nApp_lbl), REFL(p._parse(t))),
            ),
        )
    )
    body_th = _sk_bullet_select_at(p, t, t, "inner_leaf")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)
    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # D1: ?a b. atom = App_t (App_t K_t a) b /\ sk_bullet atom = sk_bullet a.
            # cases_on auto-introduces 'a' and 'b'; strip the
            # sk_bullet-payload, extract bare K-shape, contradict nK.
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nK_lbl, "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                f"h_sred_ex: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], p.fact("h_app"))
            p.absurd().by_conj(nS_lbl, "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_app)")
            p.choose("a", from_="h3_app")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_app_ex: ?a b. {t} = App_t a b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj(nApp_lbl, "h_app_ex")
        with p.case(f"h4: {D4}"):
            # D4 firing: ~K /\ ~S /\ ~App /\ sk_bullet atom = atom.
            # The fourth conjunct IS the goal.
            p.split("h4", "(_, _, _, h_sk)")
            p.thus(f"{sk_t} = {t}").by_thm(p.fact("h_sk"))


@proof
def SK_BULLET_S_T(p):
    """|- sk_bullet S_t = S_t.  D4 fires; D1/D2/D3 refuted via S_T_NEQ_APP_T."""
    p.goal("sk_bullet S_t = S_t")
    _prove_sk_bullet_leaf(p, "S_t", S_T_NEQ_APP_T)


@proof
def SK_BULLET_K_T(p):
    """|- sk_bullet K_t = K_t.  Same structure as SK_BULLET_S_T via K_T_NEQ_APP_T."""
    p.goal("sk_bullet K_t = K_t")
    _prove_sk_bullet_leaf(p, "K_t", K_T_NEQ_APP_T)


@proof
def SK_BULLET_K_REDEX(p):
    """|- !X Y. sk_bullet (App_t (App_t K_t X) Y) = sk_bullet X.

    K-redex disjunct (D1) fires at the natural witness ``r := sk_bullet X``;
    D2 / D3 / D4 all carry a ~K guard, refuted by the obvious K-redex
    existence of the input.  Structure mirrors SK_STEP_K.

    In D1's firing branch, the existential bvars ``a, b`` from the body's
    D1 must be identified with the surface ``X, Y`` so that ``h_sk:
    sk_t = sk_bullet a`` can be lifted back to ``sk_t = sk_bullet X``.
    APP_T_INJ peels the K-redex twice: first to extract ``App_t K_t X =
    App_t K_t a /\\ Y = b``, then to extract ``K_t = K_t /\\ X = a``.
    """
    from tactics import CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. "
        "sk_bullet (App_t (App_t K_t X) Y) = sk_bullet X"
    )
    p.fix("X Y")
    t = "App_t (App_t K_t X) Y"
    sk_t = f"sk_bullet ({t})"
    val = "sk_bullet X"

    # D1 inner witness at (a, b) := (X, Y), r := val.
    p.have(
        f"inner_K: ?a b. {t} = App_t (App_t K_t a) b /\\ "
        f"          {val} = sk_bullet a"
    ).by_exists(
        ["X", "Y"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    body_th = _sk_bullet_select_at(p, t, val, "inner_K")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # K-redex existence at the input; refutes ~K guards in D2-D4.
    p.have(f"is_kred: ?a b. {t} = App_t (App_t K_t a) b").by_exists(
        ["X", "Y"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # cases_on auto-binds both existentials ``a`` and ``b``.
            p.split("b_eq", "(h_app, h_sk)")
            # APP_T_INJ twice: outer App layer, then inner App_t K_t _.
            p.have(
                "h_o: App_t K_t X = App_t K_t a /\\ Y = b"
            ).by(APP_T_INJ, "App_t K_t X", "Y", "App_t K_t a", "b", "h_app")
            p.have(
                "h_o1: App_t K_t X = App_t K_t a"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                "h_i: K_t = K_t /\\ X = a"
            ).by(APP_T_INJ, "K_t", "X", "K_t", "a", "h_o1")
            p.have("h_Xa: X = a").by_thm(_C2(p.fact("h_i")))
            # h_sk: sk_t = sk_bullet a.  SYM(h_Xa) rewrites a -> X.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk", [SYM(p.fact("h_Xa"))]
            )
        with p.case(f"h2: {D2}"):
            p.split("h2", "(h_nk, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(h_nk, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(h_nk, _, _, _)")
            p.absurd().by_conj("h_nk", "is_kred")


@proof
def SK_BULLET_S_REDEX(p):
    """|- !X Y Z. sk_bullet (App_t (App_t (App_t S_t X) Y) Z)
                  = App_t (App_t (sk_bullet X) (sk_bullet Z))
                          (App_t (sk_bullet Y) (sk_bullet Z)).

    S-redex disjunct (D2, guarded by ~K) fires at the natural witness.
    D1 (K-branch) is refuted via ``not_kred`` (S-input's
    App_t (App_t S_t X) Y head can't unify with App_t K_t _ by
    APP_T_INJ + K_T_NEQ_APP_T at the inner App_t S_t X = K_t step).
    D3 / D4 are refuted via the obvious S-redex existence of the
    input.  Structure mirrors SK_STEP_S.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_bullet (App_t (App_t (App_t S_t X) Y) Z) = "
        "App_t (App_t (sk_bullet X) (sk_bullet Z)) "
        "      (App_t (sk_bullet Y) (sk_bullet Z))"
    )
    p.fix("X Y Z")
    t = "App_t (App_t (App_t S_t X) Y) Z"
    sk_t = f"sk_bullet ({t})"
    val = (
        "App_t (App_t (sk_bullet X) (sk_bullet Z)) "
        "      (App_t (sk_bullet Y) (sk_bullet Z))"
    )

    # not_kred: head App_t (App_t S_t X) Y can't match App_t K_t _.
    # Two APP_T_INJ peels strip the outer/middle App layers and surface
    # ``App_t S_t X = K_t``; SYM + K_T_NEQ_APP_T gives the contradiction.
    with p.have(
        f"not_kred: ~(?a b. {t} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex_kred: ?a b. {t} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex_kred")
            p.choose("b", from_="a_eq")
            p.have(
                "h_o: App_t (App_t S_t X) Y = App_t K_t a /\\ Z = b"
            ).by(APP_T_INJ, "App_t (App_t S_t X) Y", "Z",
                 "App_t K_t a", "b", "b_eq")
            p.have(
                "h_o1: App_t (App_t S_t X) Y = App_t K_t a"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t X = K_t /\\ Y = a"
            ).by(APP_T_INJ, "App_t S_t X", "Y", "K_t", "a", "h_o1")
            p.have("ASx_eq_K: App_t S_t X = K_t").by_thm(_C1(p.fact("h_m")))
            p.have("K_neq: ~(K_t = App_t S_t X)").by(
                K_T_NEQ_APP_T, "S_t", "X"
            )
            p.have("K_eq: K_t = App_t S_t X").by_thm(
                SYM(p.fact("ASx_eq_K"))
            )
            p.absurd().by_conj("K_neq", "K_eq")

    # D2 inner witness at r := val.  Witness tuple is (X, Y, Z); the
    # body's recursive ``sk_bullet a / b / c`` get substituted to
    # ``sk_bullet X / Y / Z`` in the expected pattern.
    p.have(
        f"inner_S_inner: "
        f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"        {val} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                      (App_t (sk_bullet b) (sk_bullet c))"
    ).by_exists(
        ["X", "Y", "Z"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    p.have(
        f"inner_S: ~(?a b. {t} = App_t (App_t K_t a) b) /\\ "
        f" (?a b c. {t} = App_t (App_t (App_t S_t a) b) c /\\ "
        f"          {val} = App_t (App_t (sk_bullet a) (sk_bullet c)) "
        f"                        (App_t (sk_bullet b) (sk_bullet c)))"
    ).by_thm(_CONJ(p.fact("not_kred"), p.fact("inner_S_inner")))
    body_th = _sk_bullet_select_at(p, t, val, "inner_S")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # is_sred: refutes ~S guards in D3, D4.
    p.have(
        f"is_sred: ?a b c. {t} = App_t (App_t (App_t S_t a) b) c"
    ).by_exists(["X", "Y", "Z"], REFL(p._parse(t)))

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # K-branch fires on an S-input: extract the (a, b) witnesses
            # via cases_on's auto-choose, then re-pack as
            # ?a b. t = App_t (App_t K_t a) b to contradict not_kred.
            p.split("b_eq", "(h_app, _)")
            p.have(
                f"h_kred_ex: ?a b. {t} = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], p.fact("h_app"))
            p.absurd().by_conj("not_kred", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            # The firing branch: unpack the existential triple, then
            # use APP_T_INJ three times to identify X=a, Y=b, Z=c, and
            # rewrite ``h_sk: val = App_t (App_t (sk_bullet a) (sk_bullet c))
            #                          (App_t (sk_bullet b) (sk_bullet c))``
            # back into the surface (X, Y, Z) form.
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, h_sk)")
            p.have(
                "h_o: App_t (App_t S_t X) Y = App_t (App_t S_t a) b /\\ "
                "     Z = c"
            ).by(APP_T_INJ, "App_t (App_t S_t X) Y", "Z",
                 "App_t (App_t S_t a) b", "c", "h_app")
            p.have(
                "h_o1: App_t (App_t S_t X) Y = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_o")))
            p.have("h_Zc: Z = c").by_thm(_C2(p.fact("h_o")))
            p.have(
                "h_m: App_t S_t X = App_t S_t a /\\ Y = b"
            ).by(APP_T_INJ, "App_t S_t X", "Y",
                 "App_t S_t a", "b", "h_o1")
            p.have(
                "h_m1: App_t S_t X = App_t S_t a"
            ).by_thm(_C1(p.fact("h_m")))
            p.have("h_Yb: Y = b").by_thm(_C2(p.fact("h_m")))
            p.have(
                "h_i: S_t = S_t /\\ X = a"
            ).by(APP_T_INJ, "S_t", "X", "S_t", "a", "h_m1")
            p.have("h_Xa: X = a").by_thm(_C2(p.fact("h_i")))
            # DSL friction: by_rewrite_of rewrites the *source* fact's
            # surface form using the supplied SYM equations.  h_sk is
            # ``sk_bullet t = App_t ... a ... b ... c ...``; the three
            # SYMs turn it back to ``... X ... Y ... Z ...``.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_Xa")), SYM(p.fact("h_Yb")),
                 SYM(p.fact("h_Zc"))],
            )
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, h_ns, _)")
            p.absurd().by_conj("h_ns", "is_sred")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, h_ns, _, _)")
            p.absurd().by_conj("h_ns", "is_sred")


@proof
def SK_BULLET_APP_OTHER(p):
    """|- !X Y.
            ~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\
            ~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c)
          ==> sk_bullet (App_t X Y) = App_t (sk_bullet X) (sk_bullet Y).

    Non-redex App congruence: D3 fires at the natural witness
    (a, b) := (X, Y); D1 and D2 directly carry the K-/S-redex existence
    needed to contradict the assumed negations; D4 carries the ~App
    guard, refuted by ``is_app``.

    Structure mirrors SK_STEP_LEFT but is simpler -- bullet's D3 has a
    single ``r = App_t (sk_bullet a) (sk_bullet b)`` payload (no nested
    descend-left/descend-right/fixed split), so once X = a3 and Y = b3
    are pinned via APP_T_INJ a single by_rewrite_of suffices.

    DSL friction: the negation antecedents use lowercase ``a b c`` as
    existential bvars (matching SK_STEP_LEFT's convention) -- this aligns
    with ``_sk_bullet_disjuncts``' bvar choice so
    ``by_conj("not_kred", "h_kred")`` matches without surprise.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1, CONJUNCT2 as _C2
    p.goal(
        "!X:nat0. !Y:nat0. "
        "~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c) "
        "==> sk_bullet (App_t X Y) = App_t (sk_bullet X) (sk_bullet Y)"
    )
    p.fix("X Y")
    p.assume(
        "(not_kred, not_sred): "
        "~(?a b. App_t X Y = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t X Y = App_t (App_t (App_t S_t a) b) c)"
    )

    t = "App_t X Y"
    sk_t = f"sk_bullet ({t})"
    val = "App_t (sk_bullet X) (sk_bullet Y)"
    K_shape = f"?a b. {t} = App_t (App_t K_t a) b"
    S_shape = f"?a b c. {t} = App_t (App_t (App_t S_t a) b) c"

    # D3 inner witness at (a, b) := (X, Y), r := val.
    p.have(
        f"inner_ex: ?a b. {t} = App_t a b /\\ "
        f"          {val} = App_t (sk_bullet a) (sk_bullet b)"
    ).by_exists(
        ["X", "Y"], REFL(p._parse(t)), REFL(p._parse(val))
    )
    p.have(
        f"inner_d3: ~({K_shape}) /\\ ~({S_shape}) /\\ "
        f"          (?a b. {t} = App_t a b /\\ "
        f"                 {val} = App_t (sk_bullet a) (sk_bullet b))"
    ).by_thm(
        _CONJ(
            p.fact("not_kred"),
            _CONJ(p.fact("not_sred"), p.fact("inner_ex")),
        )
    )

    body_th = _sk_bullet_select_at(p, t, val, "inner_d3")
    p.have(f"body: {_sk_bullet_body(t, sk_t)}").by_thm(body_th)

    # App-shape witness for D4 contradiction.
    p.have(f"is_app: ?a b. {t} = App_t a b").by_exists(
        ["X", "Y"], REFL(p._parse(t))
    )

    D1, D2, D3, D4 = _sk_bullet_disjuncts(t, sk_t)
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # D1 itself is the K-redex existence (with payload r=sk_bullet a
            # tacked on); peel the ``/\\ r = sk_bullet a`` to recover the
            # bare K-shape and contradict not_kred.
            p.choose("a_d1", from_="h1")
            p.choose("b_d1", from_="a_d1_eq")
            p.split("b_d1_eq", "(h_app, _)")
            p.have(f"h_kred: {K_shape}").by_exists(
                ["a_d1", "b_d1"], "h_app"
            )
            p.absurd().by_conj("not_kred", "h_kred")
        with p.case(f"h2: {D2}"):
            # D2 has ~K guard upfront; strip it, the remaining triple
            # existential is the S-redex existence (modulo payload).
            p.split("h2", "(_, h2_ex)")
            p.choose("a_d2", from_="h2_ex")
            p.choose("b_d2", from_="a_d2_eq")
            p.choose("c_d2", from_="b_d2_eq")
            p.split("c_d2_eq", "(h_app, _)")
            p.have(f"h_sred: {S_shape}").by_exists(
                ["a_d2", "b_d2", "c_d2"], "h_app"
            )
            p.absurd().by_conj("not_sred", "h_sred")
        with p.case(f"h3: {D3}"):
            # The firing branch.  Strip the two leading negations
            # (already known), then unpack the App-existential and
            # pin X=a3, Y=b3 via APP_T_INJ.
            p.split("h3", "(_, _, h3_ex)")
            p.choose("a3", from_="h3_ex")
            p.choose("b3", from_="a3_eq")
            p.split("b3_eq", "(h_app, h_sk)")
            p.have("h_inj: X = a3 /\\ Y = b3").by(
                APP_T_INJ, "X", "Y", "a3", "b3", "h_app"
            )
            p.have("h_Xa: X = a3").by_thm(_C1(p.fact("h_inj")))
            p.have("h_Yb: Y = b3").by_thm(_C2(p.fact("h_inj")))
            # h_sk: sk_t = App_t (sk_bullet a3) (sk_bullet b3).
            # The two SYMs rewrite a3 -> X, b3 -> Y in the source.
            p.thus(f"{sk_t} = {val}").by_rewrite_of(
                "h_sk",
                [SYM(p.fact("h_Xa")), SYM(p.fact("h_Yb"))],
            )
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, h_napp, _)")
            p.absurd().by_conj("h_napp", "is_app")


# ---------------------------------------------------------------------------
# Dependencies for SK_BULLET_TRIANGLE.
#
# PAR_STEP_K_APP_INV and PAR_STEP_S_APP_APP_INV are discharged below
# via the shared ``_par_step_app_atom_inv`` template.  TRIANGLE itself
# (further below) assembles the four pieces via impredicative
# P-instantiation with the strengthened invariant
#   ``P := \A B. sk_par_step A B /\ sk_par_step B (sk_bullet A)``.
# ---------------------------------------------------------------------------


def _par_step_app_atom_inv(p, atom_str, atom_inv_thm, atom_neq_app_t):
    """Discharge
        ``!X Y. sk_par_step (App_t <atom> X) Y ==>
                  ?XP. Y = App_t <atom> XP /\\ sk_par_step X XP``
    where ``<atom>`` is ``S_t`` or ``K_t``.

    Strategy: instantiate the impredicative encoding's ``P`` with
        Q := \\A B. sk_par_step A B /\\
                     (!W. A = App_t <atom> W ==>
                          ?Wp. B = App_t <atom> Wp /\\ sk_par_step W Wp)
    The first conjunct propagates par_step inside the closure
    rules (each rule's hypothesis carries it through); the second
    conjunct is the actual inversion shape.

    Closure analysis after BETA_NORM:
      REFL : both conjuncts via PAR_REFL.
      K    : par_step propagated by PAR_K from the IHs; inversion is
             vacuous -- ``App_t (App_t K_t _) _ = App_t <atom> _`` clashes
             at ``App_t K_t _ = <atom>`` (App vs leaf, ``atom_neq_app_t``).
      S    : par_step propagated by PAR_S; inversion clashes at
             ``App_t (App_t S_t _) _ = <atom>`` (same shape).
      APP  : the firing case.  ``App_t M N = App_t <atom> W`` gives
             ``M = <atom>``, ``N = W`` via APP_T_INJ; then the IH's
             par_step conjunct ``par_step M M1`` becomes ``par_step
             <atom> M1``, which ``atom_inv_thm`` collapses to ``M1 =
             <atom>``.  Witness ``Wp := N1``; ``App_t M1 N1 = App_t
             <atom> N1`` via AP_TERM + AP_THM.

    DSL friction (general):
    * SPEC at a 2-arg lambda Q creates beta redexes throughout the
      closures body and in the final ``Q (App_t <atom> X) Y``
      application; ``BETA_NORM`` is the only way to clean them in one
      shot.  ``by_def_at`` doesn't cover lambda-shaped P arguments.
    * The closure bvars in ``_PAR_STEP_CLOSURE`` (A Y A1 Y1 ...) clash
      with the outer ``Y``; we name the closure bvars freshly (M N P
      M1 N1 P1) and rely on alpha-conversion at the final CONJ.

    DSL friction (firing-case specific):
    * Rewriting ``par_step M M1`` to ``par_step <atom> M1`` via
      ``M = <atom>`` works through ``by_rewrite_of`` -- the equation
      fires under both Comb layers.
    * Lifting ``M1 = <atom>`` to ``App_t M1 N1 = App_t <atom> N1``
      uses raw AP_TERM + AP_THM (one congruence step per kernel arg).
      ``by_cong(App_t, eq, refl)`` would also work; the explicit form
      is cheaper because we already have ``M1 = <atom>`` as a
      registered fact.
    """
    from tactics import (
        BETA_NORM,
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
        AP_TERM as _AP_TERM,
        AP_THM as _AP_THM,
    )

    p.goal(
        f"!X:nat0. !Y:nat0. "
        f"sk_par_step (App_t {atom_str} X) Y ==> "
        f"?XP:nat0. Y = App_t {atom_str} XP /\\ sk_par_step X XP"
    )
    p.fix("X Y")
    p.assume(f"h: sk_par_step (App_t {atom_str} X) Y")

    # Unfold sk_par_step at (App_t <atom> X, Y); SPEC at Q via
    # ``by_spec`` (SPECL + BETA_NORM in one shot).
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF,
        p._parse(f"App_t {atom_str} X"),
        p._parse("Y"),
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))
    Q_tm = p._parse(
        f"\\A:nat0. \\B:nat0. "
        f"sk_par_step A B /\\ "
        f"(!W:nat0. A = App_t {atom_str} W ==> "
        f"  ?Wp:nat0. B = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    )
    p.have("h_at_Q:").by_spec(h_univ, Q_tm)

    # --- REFL closure --------------------------------------------------
    with p.have(
        f"c_refl: !Z:nat0. sk_par_step Z Z /\\ "
        f"(!W:nat0. Z = App_t {atom_str} W ==> "
        f" ?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("Z")
        p.have("h_par: sk_par_step Z Z").by(PAR_REFL, "Z")
        with p.have(
            f"h_inv: !W:nat0. Z = App_t {atom_str} W ==> "
            f"?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(f"h_eq: Z = App_t {atom_str} W")
            p.have("h_par_WW: sk_par_step W W").by(PAR_REFL, "W")
            p.thus(
                f"?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp"
            ).by_exists(["W"], "h_eq", "h_par_WW")
        p.thus(
            f"sk_par_step Z Z /\\ "
            f"(!W:nat0. Z = App_t {atom_str} W ==> "
            f" ?Wp:nat0. Z = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par"), p.fact("h_inv")))

    # --- K-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_K: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t (App_t K_t M) N) M1 /\\ "
        f"(!W:nat0. App_t (App_t K_t M) N = App_t {atom_str} W ==> "
        f" ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_KMN_M1: sk_par_step (App_t (App_t K_t M) N) M1"
        ).by(PAR_K, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            f"h_inv_K: !W:nat0. "
            f"App_t (App_t K_t M) N = App_t {atom_str} W ==> "
            f"?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(
                f"h_eq: App_t (App_t K_t M) N = App_t {atom_str} W"
            )
            p.have(
                f"h_inj: App_t K_t M = {atom_str} /\\ N = W"
            ).by(APP_T_INJ, "App_t K_t M", "N", atom_str, "W", "h_eq")
            p.have(
                f"h_inj_L: App_t K_t M = {atom_str}"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                f"h_neq: ~({atom_str} = App_t K_t M)"
            ).by(atom_neq_app_t, "K_t", "M")
            p.absurd().by_conj("h_neq", "h_inj_L")
        p.thus(
            f"sk_par_step (App_t (App_t K_t M) N) M1 /\\ "
            f"(!W:nat0. App_t (App_t K_t M) N = App_t {atom_str} W ==> "
            f" ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_KMN_M1"), p.fact("h_inv_K")))

    # --- S-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_S: !M:nat0. !N:nat0. !P:nat0. !M1:nat0. !N1:nat0. !P1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step P P1 /\\ "
        f"  (!W:nat0. P = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. P1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t (App_t (App_t S_t M) N) P) "
        f"            (App_t (App_t M1 P1) (App_t N1 P1)) /\\ "
        f"(!W:nat0. "
        f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
        f" ?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
        f"            App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).proof():
        p.fix("M N P M1 N1 P1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N), (h_par_P, h_inv_P)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step P P1 /\\ "
            f"  (!W:nat0. P = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. P1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_3: sk_par_step M M1 /\\ sk_par_step N N1 /\\ "
            "          sk_par_step P P1"
        ).by_thm(_CONJ(
            p.fact("h_par_M"),
            _CONJ(p.fact("h_par_N"), p.fact("h_par_P")),
        ))
        p.have(
            "h_par_Sred: sk_par_step (App_t (App_t (App_t S_t M) N) P) "
            "            (App_t (App_t M1 P1) (App_t N1 P1))"
        ).by(PAR_S, "M", "M1", "N", "N1", "P", "P1", "h_conj_3")
        with p.have(
            f"h_inv_S: !W:nat0. "
            f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
            f"?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
            f"           App_t {atom_str} Wp /\\ sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(
                f"h_eq: App_t (App_t (App_t S_t M) N) P = "
                f"      App_t {atom_str} W"
            )
            p.have(
                f"h_inj: App_t (App_t S_t M) N = {atom_str} /\\ P = W"
            ).by(
                APP_T_INJ,
                "App_t (App_t S_t M) N", "P", atom_str, "W", "h_eq",
            )
            p.have(
                f"h_inj_L: App_t (App_t S_t M) N = {atom_str}"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                f"h_neq: ~({atom_str} = App_t (App_t S_t M) N)"
            ).by(atom_neq_app_t, "App_t S_t M", "N")
            p.absurd().by_conj("h_neq", "h_inj_L")
        p.thus(
            f"sk_par_step (App_t (App_t (App_t S_t M) N) P) "
            f"            (App_t (App_t M1 P1) (App_t N1 P1)) /\\ "
            f"(!W:nat0. "
            f"App_t (App_t (App_t S_t M) N) P = App_t {atom_str} W ==> "
            f" ?Wp:nat0. App_t (App_t M1 P1) (App_t N1 P1) = "
            f"            App_t {atom_str} Wp /\\ sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_Sred"), p.fact("h_inv_S")))

    # --- APP-rule closure (firing case) --------------------------------
    with p.have(
        f"c_APP: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"(sk_par_step M M1 /\\ "
        f"  (!W:nat0. M = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"/\\ "
        f"(sk_par_step N N1 /\\ "
        f"  (!W:nat0. N = App_t {atom_str} W ==> "
        f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
        f"==> "
        f"sk_par_step (App_t M N) (App_t M1 N1) /\\ "
        f"(!W:nat0. App_t M N = App_t {atom_str} W ==> "
        f" ?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
        f"            sk_par_step W Wp)"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"(sk_par_step M M1 /\\ "
            f"  (!W:nat0. M = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. M1 = App_t {atom_str} Wp /\\ sk_par_step W Wp)) "
            f"/\\ "
            f"(sk_par_step N N1 /\\ "
            f"  (!W:nat0. N = App_t {atom_str} W ==> "
            f"   ?Wp:nat0. N1 = App_t {atom_str} Wp /\\ sk_par_step W Wp))"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_APP: sk_par_step (App_t M N) (App_t M1 N1)"
        ).by(PAR_APP, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            f"h_inv_APP: !W:nat0. App_t M N = App_t {atom_str} W ==> "
            f"?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
            f"           sk_par_step W Wp"
        ).proof():
            p.fix("W")
            p.assume(f"h_eq: App_t M N = App_t {atom_str} W")
            p.have(
                f"h_inj: M = {atom_str} /\\ N = W"
            ).by(APP_T_INJ, "M", "N", atom_str, "W", "h_eq")
            p.have(f"h_M_eq: M = {atom_str}").by_thm(_C1(p.fact("h_inj")))
            p.have("h_N_eq: N = W").by_thm(_C2(p.fact("h_inj")))
            # par_step M M1 + M = <atom>  ==>  par_step <atom> M1.
            p.have(
                f"h_par_atom_M1: sk_par_step {atom_str} M1"
            ).by_rewrite_of("h_par_M", [p.fact("h_M_eq")])
            # atom inversion collapses M1 to <atom>.
            p.have(
                f"h_M1_eq: M1 = {atom_str}"
            ).by(atom_inv_thm, "M1", "h_par_atom_M1")
            # par_step N N1 + N = W  ==>  par_step W N1.
            p.have(
                "h_par_W_N1: sk_par_step W N1"
            ).by_rewrite_of("h_par_N", [p.fact("h_N_eq")])
            # App_t M1 N1 = App_t <atom> N1 via AP_TERM + AP_THM.
            ap1 = _AP_TERM(App_t, p.fact("h_M1_eq"))
            ap2 = _AP_THM(ap1, p._parse("N1"))
            p.have(
                f"h_app_eq: App_t M1 N1 = App_t {atom_str} N1"
            ).by_thm(ap2)
            p.thus(
                f"?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
                f"           sk_par_step W Wp"
            ).by_exists(["N1"], "h_app_eq", "h_par_W_N1")
        p.thus(
            f"sk_par_step (App_t M N) (App_t M1 N1) /\\ "
            f"(!W:nat0. App_t M N = App_t {atom_str} W ==> "
            f" ?Wp:nat0. App_t M1 N1 = App_t {atom_str} Wp /\\ "
            f"            sk_par_step W Wp)"
        ).by_thm(_CONJ(p.fact("h_par_APP"), p.fact("h_inv_APP")))

    # --- Compose closures, MP, project, conclude -----------------------
    cl_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    p.have(f"h_cl: {pp(cl_th._concl)}").by_thm(cl_th)
    p.have(
        f"h_Q: sk_par_step (App_t {atom_str} X) Y /\\ "
        f"(!W:nat0. App_t {atom_str} X = App_t {atom_str} W ==> "
        f" ?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step W Wp)"
    ).by("h_at_Q", "h_cl")

    # Extract the inversion conjunct, SPEC at X, MP at the trivial REFL.
    p.split("h_Q", "(_, h_inv_Q)")
    p.have(
        f"h_inv_X: App_t {atom_str} X = App_t {atom_str} X ==> "
        f"?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step X Wp"
    ).by("h_inv_Q", "X")
    p.have(
        f"h_refl: App_t {atom_str} X = App_t {atom_str} X"
    ).by_thm(REFL(p._parse(f"App_t {atom_str} X")))
    p.have(
        f"h_ex: ?Wp:nat0. Y = App_t {atom_str} Wp /\\ sk_par_step X Wp"
    ).by("h_inv_X", "h_refl")
    p.choose("XP", from_="h_ex")
    p.split("XP_eq", "(h_Y_eq, h_par_X_XP)")
    p.thus(
        f"?XP:nat0. Y = App_t {atom_str} XP /\\ sk_par_step X XP"
    ).by_exists(["XP"], "h_Y_eq", "h_par_X_XP")


@proof
def PAR_STEP_K_APP_INV(p):
    """|- !X Y. sk_par_step (App_t K_t X) Y ==>
                  ?XP. Y = App_t K_t XP /\\ sk_par_step X XP.

    App-shape par_step inversion at the K_t head: any par-reduct of
    ``App_t K_t X`` must itself be ``App_t K_t XP`` where ``X`` par-
    reduces to ``XP``.  Since ``App_t K_t X`` is not a redex (only 1
    App layer; K-redex requires 2, S-redex 3), par_step can only fire
    via REFL or APP-rule; the APP-rule head ``K_t`` then collapses
    back to ``K_t`` via PAR_STEP_K_T_INV.

    Delegated to ``_par_step_app_atom_inv`` with atom = K_t.
    """
    _par_step_app_atom_inv(
        p, "K_t", PAR_STEP_K_T_INV, K_T_NEQ_APP_T
    )


@proof
def PAR_STEP_S_T_APP_INV(p):
    """|- !X Y. sk_par_step (App_t S_t X) Y ==>
                  ?XP. Y = App_t S_t XP /\\ sk_par_step X XP.

    Sister of PAR_STEP_K_APP_INV at the S_t head -- the inner inversion
    needed by PAR_STEP_S_APP_APP_INV's APP-rule firing case (where the
    par-step head ``App_t S_t X`` must be inverted before the S-shape
    survival argument can fire).

    Delegated to ``_par_step_app_atom_inv`` with atom = S_t.
    """
    _par_step_app_atom_inv(
        p, "S_t", PAR_STEP_S_T_INV, S_T_NEQ_APP_T
    )


@proof
def PAR_STEP_S_APP_APP_INV(p):
    """|- !X Y Z. sk_par_step (App_t (App_t S_t X) Y) Z ==>
                  ?XP YP. Z = App_t (App_t S_t XP) YP /\\
                          sk_par_step X XP /\\ sk_par_step Y YP.

    Two-App-deep par_step inversion at the S_t head.  ``App_t (App_t
    S_t X) Y`` has 2 App layers; S-redex needs 3 and K-redex needs 2
    with K_t (not S_t) at depth-1, so neither fires.  Only REFL and
    APP-rule.  The APP-rule case recursively inverts the head
    ``App_t S_t X`` via PAR_STEP_S_T_APP_INV.

    Strategy: instantiate the impredicative ``P`` with
        Q := \\A B. sk_par_step A B /\\
                     (!W1 W2. A = App_t (App_t S_t W1) W2 ==>
                          ?W1p W2p. B = App_t (App_t S_t W1p) W2p
                                       /\\ sk_par_step W1 W1p
                                       /\\ sk_par_step W2 W2p)

    Closures: REFL trivial; K/S vacuous via 1-2 layer APP_T_INJ
    descent ending in S_t vs K_t / S_t vs App_t clash; APP fires using
    PAR_STEP_S_T_APP_INV on the depth-1 head par-step.

    DSL friction: the inversion existentials are now binary (W1p,
    W2p) so ``by_exists`` takes two witnesses; ``h_inv_Q`` after
    extraction is also two-arg (``!W1 W2. ...``), so SPECL via the
    DSL needs sequential ``by(... "X", "Y", ...)``.
    """
    from tactics import (
        BETA_NORM,
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
        AP_TERM as _AP_TERM,
        AP_THM as _AP_THM,
    )

    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step (App_t (App_t S_t X) Y) Z ==> "
        "?XP:nat0. ?YP:nat0. "
        "Z = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step X XP /\\ sk_par_step Y YP"
    )
    p.fix("X Y Z")
    p.assume("h: sk_par_step (App_t (App_t S_t X) Y) Z")

    # Unfold sk_par_step at the input; SPEC at the binary-inversion Q
    # via ``by_spec`` (SPECL + BETA_NORM in one shot).
    sps_unfold = unfold_def_at(
        SK_PAR_STEP_DEF,
        p._parse("App_t (App_t S_t X) Y"),
        p._parse("Z"),
    )
    h_univ = EQ_MP(sps_unfold, p.fact("h"))
    Q_tm = p._parse(
        "\\A:nat0. \\B:nat0. "
        "sk_par_step A B /\\ "
        "(!W1:nat0. !W2:nat0. A = App_t (App_t S_t W1) W2 ==> "
        " ?W1p:nat0. ?W2p:nat0. "
        " B = App_t (App_t S_t W1p) W2p /\\ "
        " sk_par_step W1 W1p /\\ sk_par_step W2 W2p)"
    )
    p.have("h_at_Q:").by_spec(h_univ, Q_tm)

    # Q body, parameterized over (A, B), as a reusable string.
    def _q_body(A_str, B_str):
        return (
            f"sk_par_step {A_str} {B_str} /\\ "
            f"(!W1:nat0. !W2:nat0. {A_str} = App_t (App_t S_t W1) W2 ==> "
            f" ?W1p:nat0. ?W2p:nat0. "
            f" {B_str} = App_t (App_t S_t W1p) W2p /\\ "
            f" sk_par_step W1 W1p /\\ sk_par_step W2 W2p)"
        )

    # --- REFL closure --------------------------------------------------
    with p.have(f"c_refl: !Zc:nat0. {_q_body('Zc', 'Zc')}").proof():
        p.fix("Zc")
        p.have("h_par: sk_par_step Zc Zc").by(PAR_REFL, "Zc")
        with p.have(
            "h_inv: !W1:nat0. !W2:nat0. Zc = App_t (App_t S_t W1) W2 "
            "==> ?W1p:nat0. ?W2p:nat0. "
            "    Zc = App_t (App_t S_t W1p) W2p /\\ "
            "    sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume("h_eq: Zc = App_t (App_t S_t W1) W2")
            p.have("h_par_W1: sk_par_step W1 W1").by(PAR_REFL, "W1")
            p.have("h_par_W2: sk_par_step W2 W2").by(PAR_REFL, "W2")
            p.thus(
                "?W1p:nat0. ?W2p:nat0. "
                "Zc = App_t (App_t S_t W1p) W2p /\\ "
                "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
            ).by_exists(
                ["W1", "W2"], "h_eq", "h_par_W1", "h_par_W2"
            )
        p.thus(f"{_q_body('Zc', 'Zc')}").by_thm(
            _CONJ(p.fact("h_par"), p.fact("h_inv"))
        )

    # --- K-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_K: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) ==> "
        f"{_q_body('(App_t (App_t K_t M) N)', 'M1')}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')})"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_KMN: sk_par_step (App_t (App_t K_t M) N) M1"
        ).by(PAR_K, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            "h_inv_K: !W1:nat0. !W2:nat0. "
            "App_t (App_t K_t M) N = App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "M1 = App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume(
                "h_eq: App_t (App_t K_t M) N = App_t (App_t S_t W1) W2"
            )
            # Outer APP_T_INJ: App_t K_t M = App_t S_t W1 /\ N = W2.
            p.have(
                "h_inj1: App_t K_t M = App_t S_t W1 /\\ N = W2"
            ).by(
                APP_T_INJ,
                "App_t K_t M", "N", "App_t S_t W1", "W2", "h_eq",
            )
            p.have(
                "h_inj1_L: App_t K_t M = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj1")))
            # Inner APP_T_INJ: K_t = S_t.
            p.have(
                "h_inj2: K_t = S_t /\\ M = W1"
            ).by(APP_T_INJ, "K_t", "M", "S_t", "W1", "h_inj1_L")
            p.have("h_K_eq_S: K_t = S_t").by_thm(_C1(p.fact("h_inj2")))
            p.absurd().by_conj(S_T_NEQ_K_T, "h_K_eq_S")
        p.thus(
            f"{_q_body('(App_t (App_t K_t M) N)', 'M1')}"
        ).by_thm(_CONJ(p.fact("h_par_KMN"), p.fact("h_inv_K")))

    # --- S-rule closure (vacuous inversion) ----------------------------
    with p.have(
        f"c_S: !M:nat0. !N:nat0. !P:nat0. !M1:nat0. !N1:nat0. !P1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) /\\ "
        f"({_q_body('P', 'P1')}) ==> "
        f"{_q_body('(App_t (App_t (App_t S_t M) N) P)', '(App_t (App_t M1 P1) (App_t N1 P1))')}"
    ).proof():
        p.fix("M N P M1 N1 P1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N), (h_par_P, h_inv_P)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) /\\ "
            f"({_q_body('P', 'P1')})"
        )
        p.have(
            "h_conj_3: sk_par_step M M1 /\\ sk_par_step N N1 /\\ "
            "          sk_par_step P P1"
        ).by_thm(_CONJ(
            p.fact("h_par_M"),
            _CONJ(p.fact("h_par_N"), p.fact("h_par_P")),
        ))
        p.have(
            "h_par_Sred: sk_par_step "
            "  (App_t (App_t (App_t S_t M) N) P) "
            "  (App_t (App_t M1 P1) (App_t N1 P1))"
        ).by(PAR_S, "M", "M1", "N", "N1", "P", "P1", "h_conj_3")
        with p.have(
            "h_inv_S: !W1:nat0. !W2:nat0. "
            "App_t (App_t (App_t S_t M) N) P = "
            "  App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "App_t (App_t M1 P1) (App_t N1 P1) = "
            "  App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume(
                "h_eq: App_t (App_t (App_t S_t M) N) P = "
                "      App_t (App_t S_t W1) W2"
            )
            # Outer APP_T_INJ: App_t (App_t S_t M) N = App_t S_t W1.
            p.have(
                "h_inj1: App_t (App_t S_t M) N = App_t S_t W1 /\\ P = W2"
            ).by(
                APP_T_INJ,
                "App_t (App_t S_t M) N", "P",
                "App_t S_t W1", "W2", "h_eq",
            )
            p.have(
                "h_inj1_L: App_t (App_t S_t M) N = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj1")))
            # Inner APP_T_INJ: App_t S_t M = S_t.  App vs leaf.
            p.have(
                "h_inj2: App_t S_t M = S_t /\\ N = W1"
            ).by(
                APP_T_INJ, "App_t S_t M", "N", "S_t", "W1", "h_inj1_L"
            )
            p.have(
                "h_inj2_L: App_t S_t M = S_t"
            ).by_thm(_C1(p.fact("h_inj2")))
            p.have("h_neq: ~(S_t = App_t S_t M)").by(
                S_T_NEQ_APP_T, "S_t", "M"
            )
            p.absurd().by_conj("h_neq", "h_inj2_L")
        p.thus(
            f"{_q_body('(App_t (App_t (App_t S_t M) N) P)', '(App_t (App_t M1 P1) (App_t N1 P1))')}"
        ).by_thm(_CONJ(p.fact("h_par_Sred"), p.fact("h_inv_S")))

    # --- APP-rule closure (firing case) --------------------------------
    with p.have(
        f"c_APP: !M:nat0. !N:nat0. !M1:nat0. !N1:nat0. "
        f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')}) ==> "
        f"{_q_body('(App_t M N)', '(App_t M1 N1)')}"
    ).proof():
        p.fix("M N M1 N1")
        p.assume(
            f"((h_par_M, h_inv_M), (h_par_N, h_inv_N)): "
            f"({_q_body('M', 'M1')}) /\\ ({_q_body('N', 'N1')})"
        )
        p.have(
            "h_conj_MN: sk_par_step M M1 /\\ sk_par_step N N1"
        ).by_thm(_CONJ(p.fact("h_par_M"), p.fact("h_par_N")))
        p.have(
            "h_par_APP: sk_par_step (App_t M N) (App_t M1 N1)"
        ).by(PAR_APP, "M", "M1", "N", "N1", "h_conj_MN")
        with p.have(
            "h_inv_APP: !W1:nat0. !W2:nat0. "
            "App_t M N = App_t (App_t S_t W1) W2 ==> "
            "?W1p:nat0. ?W2p:nat0. "
            "App_t M1 N1 = App_t (App_t S_t W1p) W2p /\\ "
            "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
        ).proof():
            p.fix("W1 W2")
            p.assume("h_eq: App_t M N = App_t (App_t S_t W1) W2")
            p.have(
                "h_inj: M = App_t S_t W1 /\\ N = W2"
            ).by(APP_T_INJ, "M", "N", "App_t S_t W1", "W2", "h_eq")
            p.have(
                "h_M_eq: M = App_t S_t W1"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have("h_N_eq: N = W2").by_thm(_C2(p.fact("h_inj")))
            # par_step M M1 + M = App_t S_t W1 ==> par_step (App_t S_t W1) M1.
            p.have(
                "h_par_SW1_M1: sk_par_step (App_t S_t W1) M1"
            ).by_rewrite_of("h_par_M", [p.fact("h_M_eq")])
            # Recursive App-atom inversion at the S_t head.
            p.have(
                "h_M1_shape: ?XP:nat0. "
                "M1 = App_t S_t XP /\\ sk_par_step W1 XP"
            ).by(
                PAR_STEP_S_T_APP_INV, "W1", "M1", "h_par_SW1_M1"
            )
            p.choose("M1_inner", from_="h_M1_shape")
            p.split("M1_inner_eq", "(h_M1_eq, h_par_W1_inner)")
            # par_step N N1 + N = W2  ==>  par_step W2 N1.
            p.have(
                "h_par_W2_N1: sk_par_step W2 N1"
            ).by_rewrite_of("h_par_N", [p.fact("h_N_eq")])
            # App_t M1 N1 = App_t (App_t S_t M1_inner) N1 via congruence.
            ap1 = _AP_TERM(App_t, p.fact("h_M1_eq"))
            ap2 = _AP_THM(ap1, p._parse("N1"))
            p.have(
                "h_app_eq: App_t M1 N1 = App_t (App_t S_t M1_inner) N1"
            ).by_thm(ap2)
            p.thus(
                "?W1p:nat0. ?W2p:nat0. "
                "App_t M1 N1 = App_t (App_t S_t W1p) W2p /\\ "
                "sk_par_step W1 W1p /\\ sk_par_step W2 W2p"
            ).by_exists(
                ["M1_inner", "N1"],
                "h_app_eq", "h_par_W1_inner", "h_par_W2_N1",
            )
        p.thus(
            f"{_q_body('(App_t M N)', '(App_t M1 N1)')}"
        ).by_thm(_CONJ(p.fact("h_par_APP"), p.fact("h_inv_APP")))

    # --- Compose closures, MP, project, conclude -----------------------
    cl_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    p.have(f"h_cl: {pp(cl_th._concl)}").by_thm(cl_th)
    p.have(
        f"h_Q: {_q_body('(App_t (App_t S_t X) Y)', 'Z')}"
    ).by("h_at_Q", "h_cl")

    p.split("h_Q", "(_, h_inv_Q)")
    p.have(
        "h_inv_XY: App_t (App_t S_t X) Y = App_t (App_t S_t X) Y ==> "
        "?W1p:nat0. ?W2p:nat0. "
        "Z = App_t (App_t S_t W1p) W2p /\\ "
        "sk_par_step X W1p /\\ sk_par_step Y W2p"
    ).by("h_inv_Q", "X", "Y")
    p.have(
        "h_refl: App_t (App_t S_t X) Y = App_t (App_t S_t X) Y"
    ).by_thm(REFL(p._parse("App_t (App_t S_t X) Y")))
    p.have(
        "h_ex: ?W1p:nat0. ?W2p:nat0. "
        "Z = App_t (App_t S_t W1p) W2p /\\ "
        "sk_par_step X W1p /\\ sk_par_step Y W2p"
    ).by("h_inv_XY", "h_refl")
    p.choose("XP", from_="h_ex")
    p.choose("YP", from_="XP_eq")
    p.split("YP_eq", "(h_Z_eq, h_par_X_XP, h_par_Y_YP)")
    p.thus(
        "?XP:nat0. ?YP:nat0. "
        "Z = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step X XP /\\ sk_par_step Y YP"
    ).by_exists(
        ["XP", "YP"], "h_Z_eq", "h_par_X_XP", "h_par_Y_YP"
    )


def _bullet_refl_app_case(p):
    """BULLET_REFL's App-but-not-K/S sub-case.

    Closes ``sk_par_step A (sk_bullet A)`` from:
      * ``b_eq``: ``A = App_t a b`` (``a`` and ``b`` auto-bound by
        outer ``cases_on``)
      * ``h_nK``, ``h_nS``: A is neither K- nor S-redex
      * ``IH``:  the strong-induction hypothesis on ``A``

    PAR_APP combines IH at (a, b); SK_BULLET_APP_OTHER unfolds
    ``sk_bullet (App_t a b)`` to ``App_t (sk_bullet a) (sk_bullet b)``.
    Mirrors _par_step_app_case (halting.py:7185).
    """
    from tactics import CONJ as _CONJ, BETA_RULE

    # b_eq : A = App_t a b.
    # Lift the non-redex hypotheses from A to App_t a b via AP_TERM at
    # the negation-shape predicate, then BETA_RULE, then EQ_MP.
    P_K = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. x = App_t (App_t K_t u) v)"
    )
    h_nK_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_K, p.fact("b_eq"))),
        p.fact("h_nK"),
    )
    p.have(
        "h_nK_ab: ~(?u v. App_t a b = App_t (App_t K_t u) v)"
    ).by_thm(h_nK_ab_thm)
    P_S = p._parse(
        "\\x:nat0. ~(?u:nat0. ?v:nat0. ?w:nat0. "
        "          x = App_t (App_t (App_t S_t u) v) w)"
    )
    h_nS_ab_thm = EQ_MP(
        BETA_RULE(AP_TERM(P_S, p.fact("b_eq"))),
        p.fact("h_nS"),
    )
    p.have(
        "h_nS_ab: ~(?u v w. App_t a b = "
        "         App_t (App_t (App_t S_t u) v) w)"
    ).by_thm(h_nS_ab_thm)
    # IH at a, b -- both strictly smaller via NAT0_LT_APP_T_L/R.
    p.have(
        "h_lt_a_AB: nat0_lt a (App_t a b)"
    ).by(NAT0_LT_APP_T_L, "a", "b")
    p.have(
        "h_lt_b_AB: nat0_lt b (App_t a b)"
    ).by(NAT0_LT_APP_T_R, "a", "b")
    p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
        "h_lt_a_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
        "h_lt_b_AB", [SYM(p.fact("b_eq"))]
    )
    p.have("h_ih_a: sk_par_step a (sk_bullet a)").by(
        "IH", "a", "h_lt_a"
    )
    p.have("h_ih_b: sk_par_step b (sk_bullet b)").by(
        "IH", "b", "h_lt_b"
    )
    # PAR_APP combines the two IHs.
    p.have(
        "h_par_AB: sk_par_step (App_t a b) "
        "                     (App_t (sk_bullet a) (sk_bullet b))"
    ).by(
        PAR_APP, "a", "sk_bullet a", "b", "sk_bullet b",
        _CONJ(p.fact("h_ih_a"), p.fact("h_ih_b")),
    )
    # SK_BULLET_APP_OTHER under the lifted non-redex guards.
    p.have(
        "h_nKnS_ab: "
        "~(?u v. App_t a b = App_t (App_t K_t u) v) /\\ "
        "~(?u v w. App_t a b = "
        "          App_t (App_t (App_t S_t u) v) w)"
    ).by_thm(_CONJ(p.fact("h_nK_ab"), p.fact("h_nS_ab")))
    p.have(
        "h_bullet_AB: sk_bullet (App_t a b) = "
        "             App_t (sk_bullet a) (sk_bullet b)"
    ).by(SK_BULLET_APP_OTHER, "a", "b", "h_nKnS_ab")
    p.have(
        "h_bullet_A: sk_bullet A = "
        "            App_t (sk_bullet a) (sk_bullet b)"
    ).by_rewrite_of("h_bullet_AB", [SYM(p.fact("b_eq"))])
    # Fold App_t a b back to A on the LHS slot, then sk_bullet a b's
    # RHS-form back to sk_bullet A.
    p.have(
        "h_par_A_bull: sk_par_step A "
        "             (App_t (sk_bullet a) (sk_bullet b))"
    ).by_rewrite_of("h_par_AB", [SYM(p.fact("b_eq"))])
    p.thus("sk_par_step A (sk_bullet A)").by_rewrite_of(
        "h_par_A_bull", [SYM(p.fact("h_bullet_A"))]
    )


def _bullet_refl_leaf_case(p):
    """BULLET_REFL's non-App leaf sub-case.

    Builds the D4 inner branch from h_nK / h_nS / h_nApp, lifts it via
    ``_sk_bullet_select_at`` to ``body[A, sk_bullet A]``, case-splits;
    D1/D2/D3 are App-shaped existentials refuted by the three non-shape
    hypotheses, D4 yields ``sk_bullet A = A`` which PAR_REFL closes.
    Mirrors _par_step_leaf_case (halting.py:7323).
    """
    from tactics import CONJ as _CONJ

    p.have(
        "inner_leaf: "
        "~(?a b. A = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. A = App_t (App_t (App_t S_t a) b) c) /\\ "
        "~(?a b. A = App_t a b) /\\ A = A"
    ).by_thm(
        _CONJ(
            p.fact("h_nK"),
            _CONJ(
                p.fact("h_nS"),
                _CONJ(p.fact("h_nApp"), REFL(p._parse("A"))),
            ),
        )
    )
    body_th = _sk_bullet_select_at(p, "A", "A", "inner_leaf")
    p.have(
        f"body: {_sk_bullet_body('A', 'sk_bullet A')}"
    ).by_thm(body_th)
    D1, D2, D3, D4 = _sk_bullet_disjuncts("A", "sk_bullet A")
    with p.cases_on("body"):
        with p.case(f"h1: {D1}"):
            # cases_on auto-introduces both 'a' and 'b'.
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_kred_ex: ?a b. A = App_t (App_t K_t a) b"
            ).by_exists(["a", "b"], "h_app")
            p.absurd().by_conj("h_nK", "h_kred_ex")
        with p.case(f"h2: {D2}"):
            p.split("h2", "(_, h2_ex)")
            p.choose("a", from_="h2_ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.split("c_eq", "(h_app, _)")
            p.have(
                "h_sred_ex: ?a b c. A = "
                "           App_t (App_t (App_t S_t a) b) c"
            ).by_exists(["a", "b", "c"], "h_app")
            p.absurd().by_conj("h_nS", "h_sred_ex")
        with p.case(f"h3: {D3}"):
            p.split("h3", "(_, _, h3_app)")
            p.choose("a", from_="h3_app")
            p.choose("b", from_="a_eq")
            p.split("b_eq", "(h_app, _)")
            p.have(
                "h_app_ex: ?a b. A = App_t a b"
            ).by_exists(["a", "b"], "h_app")
            p.absurd().by_conj("h_nApp", "h_app_ex")
        with p.case(f"h4: {D4}"):
            p.split("h4", "(_, _, _, h_bull)")
            # h_bull : sk_bullet A = A.  SYM as a rewrite rule
            # (A -> sk_bullet A) would loop; lift via AP_TERM at the
            # RHS slot of ``sk_par_step A _`` instead.  DSL friction:
            # by_rewrite_of refuses non-terminating rules silently and
            # ``sk_par_step A A`` doesn't simp-match the goal, so the
            # explicit AP_TERM lift is the cleanest route here.
            p.have("h_refl: sk_par_step A A").by(PAR_REFL, "A")
            p.thus("sk_par_step A (sk_bullet A)").by_thm(
                EQ_MP(
                    AP_TERM(
                        p._parse("sk_par_step A"),
                        SYM(p.fact("h_bull")),
                    ),
                    p.fact("h_refl"),
                )
            )


@proof
def BULLET_REFL(p):
    """|- !A. sk_par_step A (sk_bullet A).

    Every term parallel-reduces (in one parallel step) to its complete
    development.  Despite the name this is NOT par_step's REFL rule:
    ``sk_bullet`` contracts every redex it sees, so the proof actually
    fires PAR_K / PAR_S / PAR_APP at the redex / non-redex App cases.

    Strong induction on ``A`` over ``nat0_lt`` with a 4-way LEM split
    on A's shape:

      * K-redex (A = App K a b)         : sk_bullet A = sk_bullet a;
                                          PAR_K with IH at a, b.
      * S-redex (A = App (App S a) b c) : SK_BULLET_S_REDEX;
                                          PAR_S with IH at a, b, c.
      * generic App (~K, ~S)            : SK_BULLET_APP_OTHER;
                                          PAR_APP with IH at a, b.
      * leaf (~K, ~S, ~App)             : sk_bullet A = A via D4;
                                          PAR_REFL.

    Subterm-smaller-than-A facts go via NAT0_LT_APP_T_L/R (single hop
    in the App-other case) or NAT0_LT_TRANS chains (1 hop for the
    K-redex inner ``a``; 2-3 hops for the S-redex's a, b through
    nested App-spines).
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ

    p.goal("!A:nat0. sk_par_step A (sk_bullet A)")
    with p.strong_induction("A", "IH"):
        # IH : !k. nat0_lt k A ==> sk_par_step k (sk_bullet k).
        # ---- LEM split: is A a K-redex? ---------------------------------
        with p.cases_on(
            EXCLUDED_MIDDLE,
            "?a b. A = App_t (App_t K_t a) b",
        ):
            with p.case("h_K: ?a b. A = App_t (App_t K_t a) b"):
                # cases_on auto-introduces both 'a' and 'b' (spec has
                # two outer ? bvars).  b_eq : A = App_t (App_t K_t a) b.

                # nat0_lt a A: two-hop a < App K a < App (App K a) b.
                p.have(
                    "h_lt_a_Ka: nat0_lt a (App_t K_t a)"
                ).by(NAT0_LT_APP_T_R, "K_t", "a")
                p.have(
                    "h_lt_Ka_KAB: nat0_lt (App_t K_t a) "
                    "                     (App_t (App_t K_t a) b)"
                ).by(NAT0_LT_APP_T_L, "App_t K_t a", "b")
                p.have(
                    "h_lt_a_KAB: "
                    "nat0_lt a (App_t (App_t K_t a) b)"
                ).by(
                    NAT0_LT_TRANS,
                    "a", "App_t K_t a", "App_t (App_t K_t a) b",
                    "h_lt_a_Ka", "h_lt_Ka_KAB",
                )
                p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
                    "h_lt_a_KAB", [SYM(p.fact("b_eq"))]
                )
                # nat0_lt b A: direct from App_t-right.
                p.have(
                    "h_lt_b_KAB: "
                    "nat0_lt b (App_t (App_t K_t a) b)"
                ).by(NAT0_LT_APP_T_R, "App_t K_t a", "b")
                p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
                    "h_lt_b_KAB", [SYM(p.fact("b_eq"))]
                )

                p.have(
                    "h_ih_a: sk_par_step a (sk_bullet a)"
                ).by("IH", "a", "h_lt_a")
                p.have(
                    "h_ih_b: sk_par_step b (sk_bullet b)"
                ).by("IH", "b", "h_lt_b")
                # PAR_K with X1 := sk_bullet a, Y1 := sk_bullet b.
                p.have(
                    "h_par_KAB: "
                    "sk_par_step (App_t (App_t K_t a) b) (sk_bullet a)"
                ).by(
                    PAR_K, "a", "sk_bullet a", "b", "sk_bullet b",
                    _CONJ(p.fact("h_ih_a"), p.fact("h_ih_b")),
                )
                # Bullet collapses the K-redex.
                p.have(
                    "h_bullet_KAB: sk_bullet (App_t (App_t K_t a) b) "
                    "              = sk_bullet a"
                ).by(SK_BULLET_K_REDEX, "a", "b")
                p.have(
                    "h_bullet_A: sk_bullet A = sk_bullet a"
                ).by_rewrite_of(
                    "h_bullet_KAB", [SYM(p.fact("b_eq"))]
                )
                # Fold the K-redex back to A in the par-step, then
                # ``sk_bullet a`` back to ``sk_bullet A`` on the RHS.
                p.have(
                    "h_par_A_bull_a: sk_par_step A (sk_bullet a)"
                ).by_rewrite_of("h_par_KAB", [SYM(p.fact("b_eq"))])
                p.thus("sk_par_step A (sk_bullet A)").by_rewrite_of(
                    "h_par_A_bull_a", [SYM(p.fact("h_bullet_A"))]
                )
            with p.case("h_nK: ~(?a b. A = App_t (App_t K_t a) b)"):
                # ---- LEM split: is A an S-redex? --------------------
                with p.cases_on(
                    EXCLUDED_MIDDLE,
                    "?a b c. A = App_t (App_t (App_t S_t a) b) c",
                ):
                    with p.case(
                        "h_S: ?a b c. A = "
                        "     App_t (App_t (App_t S_t a) b) c"
                    ):
                        # cases_on auto-introduces 'a', 'b', 'c'.
                        # c_eq : A = App_t (App_t (App_t S_t a) b) c.

                        # nat0_lt c A: one hop.
                        p.have(
                            "h_lt_c_SABC: nat0_lt c "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_APP_T_R,
                            "App_t (App_t S_t a) b", "c",
                        )
                        p.have("h_lt_c: nat0_lt c A").by_rewrite_of(
                            "h_lt_c_SABC", [SYM(p.fact("c_eq"))]
                        )
                        # nat0_lt b A: two hops via App (App S a) b.
                        p.have(
                            "h_lt_b_SAb: "
                            "nat0_lt b (App_t (App_t S_t a) b)"
                        ).by(NAT0_LT_APP_T_R, "App_t S_t a", "b")
                        p.have(
                            "h_lt_SAb_SABC: "
                            "nat0_lt (App_t (App_t S_t a) b) "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_APP_T_L,
                            "App_t (App_t S_t a) b", "c",
                        )
                        p.have(
                            "h_lt_b_SABC: "
                            "nat0_lt b "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_TRANS,
                            "b", "App_t (App_t S_t a) b",
                            "App_t (App_t (App_t S_t a) b) c",
                            "h_lt_b_SAb", "h_lt_SAb_SABC",
                        )
                        p.have("h_lt_b: nat0_lt b A").by_rewrite_of(
                            "h_lt_b_SABC", [SYM(p.fact("c_eq"))]
                        )
                        # nat0_lt a A: three hops via App S a, App (App S a) b.
                        p.have(
                            "h_lt_a_Sa: nat0_lt a (App_t S_t a)"
                        ).by(NAT0_LT_APP_T_R, "S_t", "a")
                        p.have(
                            "h_lt_Sa_SAb: "
                            "nat0_lt (App_t S_t a) "
                            "(App_t (App_t S_t a) b)"
                        ).by(NAT0_LT_APP_T_L, "App_t S_t a", "b")
                        p.have(
                            "h_lt_a_SAb: "
                            "nat0_lt a (App_t (App_t S_t a) b)"
                        ).by(
                            NAT0_LT_TRANS,
                            "a", "App_t S_t a",
                            "App_t (App_t S_t a) b",
                            "h_lt_a_Sa", "h_lt_Sa_SAb",
                        )
                        p.have(
                            "h_lt_a_SABC: "
                            "nat0_lt a "
                            "(App_t (App_t (App_t S_t a) b) c)"
                        ).by(
                            NAT0_LT_TRANS,
                            "a", "App_t (App_t S_t a) b",
                            "App_t (App_t (App_t S_t a) b) c",
                            "h_lt_a_SAb", "h_lt_SAb_SABC",
                        )
                        p.have("h_lt_a: nat0_lt a A").by_rewrite_of(
                            "h_lt_a_SABC", [SYM(p.fact("c_eq"))]
                        )

                        p.have(
                            "h_ih_a: sk_par_step a (sk_bullet a)"
                        ).by("IH", "a", "h_lt_a")
                        p.have(
                            "h_ih_b: sk_par_step b (sk_bullet b)"
                        ).by("IH", "b", "h_lt_b")
                        p.have(
                            "h_ih_c: sk_par_step c (sk_bullet c)"
                        ).by("IH", "c", "h_lt_c")
                        # PAR_S aligned with SK_BULLET_S_REDEX's RHS:
                        # X1 := sk_bullet a, Y1 := sk_bullet b,
                        # Z1 := sk_bullet c.
                        p.have(
                            "h_par_SABC: "
                            "sk_par_step "
                            "(App_t (App_t (App_t S_t a) b) c) "
                            "(App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c)))"
                        ).by(
                            PAR_S,
                            "a", "sk_bullet a", "b", "sk_bullet b",
                            "c", "sk_bullet c",
                            _CONJ(
                                p.fact("h_ih_a"),
                                _CONJ(
                                    p.fact("h_ih_b"),
                                    p.fact("h_ih_c"),
                                ),
                            ),
                        )
                        p.have(
                            "h_bullet_SABC: "
                            "sk_bullet "
                            "(App_t (App_t (App_t S_t a) b) c) = "
                            "App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c))"
                        ).by(SK_BULLET_S_REDEX, "a", "b", "c")
                        p.have(
                            "h_bullet_A: sk_bullet A = "
                            "App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c))"
                        ).by_rewrite_of(
                            "h_bullet_SABC", [SYM(p.fact("c_eq"))]
                        )
                        p.have(
                            "h_par_A_bull: "
                            "sk_par_step A "
                            "(App_t "
                            "  (App_t (sk_bullet a) (sk_bullet c)) "
                            "  (App_t (sk_bullet b) (sk_bullet c)))"
                        ).by_rewrite_of(
                            "h_par_SABC", [SYM(p.fact("c_eq"))]
                        )
                        p.thus(
                            "sk_par_step A (sk_bullet A)"
                        ).by_rewrite_of(
                            "h_par_A_bull",
                            [SYM(p.fact("h_bullet_A"))],
                        )
                    with p.case(
                        "h_nS: ~(?a b c. A = "
                        "       App_t (App_t (App_t S_t a) b) c)"
                    ):
                        # ---- LEM split: is A an App at all? --------
                        with p.cases_on(
                            EXCLUDED_MIDDLE, "?a b. A = App_t a b"
                        ):
                            with p.case(
                                "h_App: ?a b. A = App_t a b"
                            ):
                                _bullet_refl_app_case(p)
                            with p.case(
                                "h_nApp: ~(?a b. A = App_t a b)"
                            ):
                                _bullet_refl_leaf_case(p)


def _bull_no_redex_guard_atom_head(p, atom_str, X_str, suffix):
    """For ``T := App_t {atom_str} ({X_str})`` with atom_str in
    {"S_t", "K_t"}, prove the SK_BULLET_APP_OTHER guard conjunction
    ``~(?a b. T = App_t (App_t K_t a) b)
      /\\ ~(?a b c. T = App_t (App_t (App_t S_t a) b) c)``
    and register it as ``h_nKnS_{suffix}``.  Each negation falls in
    one APP_T_INJ peel: the outer-App left-arg ({atom_str}) collides
    with App_t-headed RHS via S_T_NEQ_APP_T / K_T_NEQ_APP_T.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1
    atom_neq = S_T_NEQ_APP_T if atom_str == "S_t" else K_T_NEQ_APP_T
    T = f"App_t {atom_str} ({X_str})"
    nK = f"_nK_{suffix}"
    nS = f"_nS_{suffix}"
    with p.have(
        f"{nK}: ~(?a b. {T} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex: ?a b. {T} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                f"h_inj: {atom_str} = App_t K_t a /\\ ({X_str}) = b"
            ).by(APP_T_INJ, atom_str, X_str, "App_t K_t a", "b", "b_eq")
            p.have(f"h_a: {atom_str} = App_t K_t a").by_thm(
                _C1(p.fact("h_inj"))
            )
            p.have(f"h_n: ~({atom_str} = App_t K_t a)").by(
                atom_neq, "K_t", "a"
            )
            p.absurd().by_conj("h_n", "h_a")
    with p.have(
        f"{nS}: ~(?a b c. {T} = App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            f"ex: ?a b c. {T} = App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                f"h_inj: {atom_str} = App_t (App_t S_t a) b /\\ "
                f"({X_str}) = c"
            ).by(
                APP_T_INJ, atom_str, X_str,
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(f"h_a: {atom_str} = App_t (App_t S_t a) b").by_thm(
                _C1(p.fact("h_inj"))
            )
            p.have(f"h_n: ~({atom_str} = App_t (App_t S_t a) b)").by(
                atom_neq, "App_t S_t a", "b"
            )
            p.absurd().by_conj("h_n", "h_a")
    p.have(
        f"h_nKnS_{suffix}: "
        f"~(?a b. {T} = App_t (App_t K_t a) b) /\\ "
        f"~(?a b c. {T} = App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact(nK), p.fact(nS)))
    return f"h_nKnS_{suffix}"


def _bull_no_redex_guard_app_S_head(p, X_str, Y_str, suffix):
    """For ``T := App_t (App_t S_t {X_str}) ({Y_str})``, prove the
    SK_BULLET_APP_OTHER guard conjunction.  Two-level APP_T_INJ peel:
    the inner-App left-arg ``S_t`` clashes with K_t (S_T_NEQ_K_T) for
    the K-redex case, and with App_t S_t (S_T_NEQ_APP_T) for the
    S-redex case.
    """
    from tactics import CONJ as _CONJ, CONJUNCT1 as _C1
    T = f"App_t (App_t S_t ({X_str})) ({Y_str})"
    SX = f"App_t S_t ({X_str})"
    nK = f"_nK_{suffix}"
    nS = f"_nS_{suffix}"
    with p.have(
        f"{nK}: ~(?a b. {T} = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(f"ex: ?a b. {T} = App_t (App_t K_t a) b"):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                f"h_o: {SX} = App_t K_t a /\\ ({Y_str}) = b"
            ).by(APP_T_INJ, SX, Y_str, "App_t K_t a", "b", "b_eq")
            p.have(f"h_o_L: {SX} = App_t K_t a").by_thm(
                _C1(p.fact("h_o"))
            )
            p.have(
                f"h_i: S_t = K_t /\\ ({X_str}) = a"
            ).by(APP_T_INJ, "S_t", X_str, "K_t", "a", "h_o_L")
            p.have("h_SK: S_t = K_t").by_thm(_C1(p.fact("h_i")))
            p.absurd().by_conj(S_T_NEQ_K_T, "h_SK")
    with p.have(
        f"{nS}: ~(?a b c. {T} = App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            f"ex: ?a b c. {T} = App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                f"h_o: {SX} = App_t (App_t S_t a) b /\\ ({Y_str}) = c"
            ).by(
                APP_T_INJ, SX, Y_str,
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                f"h_o_L: {SX} = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_o")))
            p.have(
                f"h_i: S_t = App_t S_t a /\\ ({X_str}) = b"
            ).by(APP_T_INJ, "S_t", X_str, "App_t S_t a", "b", "h_o_L")
            p.have("h_a: S_t = App_t S_t a").by_thm(
                _C1(p.fact("h_i"))
            )
            p.have("h_n: ~(S_t = App_t S_t a)").by(
                S_T_NEQ_APP_T, "S_t", "a"
            )
            p.absurd().by_conj("h_n", "h_a")
    p.have(
        f"h_nKnS_{suffix}: "
        f"~(?a b. {T} = App_t (App_t K_t a) b) /\\ "
        f"~(?a b c. {T} = App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact(nK), p.fact(nS)))
    return f"h_nKnS_{suffix}"


def _triangle_K_case(p):
    """K-redex sub-case of _TRIANGLE_APP_CLOSURE.

    Context (from outer cases_on auto-introduce):
      ``Ai`` in scope; ``Ai_eq : A = App_t K_t Ai``.
      Plus the four hyps h_A / h_A_bull / h_B / h_B_bull.

    Goal: ``sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))``.

    App_t A B is the K-redex ``App_t (App_t K_t Ai) B`` whose bullet
    collapses to sk_bullet Ai (SK_BULLET_K_REDEX).  Strategy:
      1. PAR_STEP_K_APP_INV on h_A : A1 = App_t K_t A1_in,
         sk_par_step Ai A1_in.
      2. Compute sk_bullet (App_t K_t Ai) = App_t K_t (sk_bullet Ai)
         via SK_BULLET_APP_OTHER (App_t K_t Ai is not itself a K/S
         redex -- single App layer) + SK_BULLET_K_T.
      3. PAR_STEP_K_APP_INV on h_A_bull (rewritten through (1) and
         (2)) : sk_par_step A1_in (sk_bullet Ai).
      4. PAR_K with X1 := sk_bullet Ai, Y1 := sk_bullet B yields
         sk_par_step (App_t (App_t K_t A1_in) B1) (sk_bullet Ai).
      5. Fold (App_t K_t A1_in) -> A1 and sk_bullet Ai -> sk_bullet
         (App_t A B) via SK_BULLET_K_REDEX.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
    )

    # ---- Step 1: invert h_A using A = App_t K_t Ai. -------------------
    p.have(
        "h_A_K: sk_par_step (App_t K_t Ai) A1"
    ).by_rewrite_of("h_A", [p.fact("Ai_eq")])
    p.have(
        "h_A1_shape: ?XP:nat0. A1 = App_t K_t XP /\\ "
        "            sk_par_step Ai XP"
    ).by(PAR_STEP_K_APP_INV, "Ai", "A1", "h_A_K")
    p.choose("A1_in", from_="h_A1_shape")
    p.split("A1_in_eq", "(h_A1_eq, h_par_Ai_A1_in)")

    # ---- Step 2a: ~K and ~S guards for App_t K_t Ai. ------------------
    _bull_no_redex_guard_atom_head(p, "K_t", "Ai", "KAi")

    # ---- Step 2b: sk_bullet (App_t K_t Ai) = App_t K_t (sk_bullet Ai).
    p.have(
        "h_bull_KAi_raw: sk_bullet (App_t K_t Ai) = "
        "                App_t (sk_bullet K_t) (sk_bullet Ai)"
    ).by(SK_BULLET_APP_OTHER, "K_t", "Ai", "h_nKnS_KAi")
    p.have(
        "h_bull_KAi: sk_bullet (App_t K_t Ai) = "
        "            App_t K_t (sk_bullet Ai)"
    ).by_rewrite_of("h_bull_KAi_raw", [SK_BULLET_K_T])

    # ---- Step 3: invert h_A_bull. -------------------------------------
    # First propagate Ai_eq and A1_in_eq into h_A_bull's surface form.
    p.have(
        "h_bull_A_step1: sk_bullet A = sk_bullet (App_t K_t Ai)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("Ai_eq")))
    p.have(
        "h_bull_A: sk_bullet A = App_t K_t (sk_bullet Ai)"
    ).by_trans("h_bull_A_step1", "h_bull_KAi")
    # DSL friction: by_rewrite_of with h_A1_eq is rejected as
    # non-terminating because A1_in's @-binder body contains A1
    # free.  Compose the congruence equation manually via by_cong +
    # by_eq_mp -- this skips REWRITE_CONV's loop guard entirely.
    p.have(
        "h_A_bull_eq: "
        "sk_par_step A1 (sk_bullet A) = "
        "sk_par_step (App_t K_t A1_in) (App_t K_t (sk_bullet Ai))"
    ).by_cong(sk_par_step, "h_A1_eq", "h_bull_A")
    p.have(
        "h_A_bull_K: "
        "sk_par_step (App_t K_t A1_in) (App_t K_t (sk_bullet Ai))"
    ).by_eq_mp("h_A_bull_eq", "h_A_bull")
    # Now invert at K_t.
    p.have(
        "h_inv_A1: ?XP:nat0. "
        "App_t K_t (sk_bullet Ai) = App_t K_t XP /\\ "
        "sk_par_step A1_in XP"
    ).by(
        PAR_STEP_K_APP_INV,
        "A1_in", "App_t K_t (sk_bullet Ai)", "h_A_bull_K",
    )
    p.choose("Xp", from_="h_inv_A1")
    p.split("Xp_eq", "(h_app_eq, h_par_A1in_Xp)")
    p.have(
        "h_inj_Xp: K_t = K_t /\\ sk_bullet Ai = Xp"
    ).by(
        APP_T_INJ, "K_t", "sk_bullet Ai", "K_t", "Xp", "h_app_eq"
    )
    p.have(
        "h_Xp_eq: sk_bullet Ai = Xp"
    ).by_thm(_C2(p.fact("h_inj_Xp")))
    p.have(
        "h_par_A1in_bullAi: sk_par_step A1_in (sk_bullet Ai)"
    ).by_rewrite_of(
        "h_par_A1in_Xp", [SYM(p.fact("h_Xp_eq"))]
    )

    # ---- Step 4: PAR_K to assemble. -----------------------------------
    p.have(
        "h_par_PAR_K: "
        "sk_par_step (App_t (App_t K_t A1_in) B1) (sk_bullet Ai)"
    ).by(
        PAR_K,
        "A1_in", "sk_bullet Ai", "B1", "sk_bullet B",
        _CONJ(
            p.fact("h_par_A1in_bullAi"), p.fact("h_B_bull")
        ),
    )

    # ---- Step 5: fold to the goal form. -------------------------------
    # App_t A B = App_t (App_t K_t Ai) B; sk_bullet collapses to
    # sk_bullet Ai via SK_BULLET_K_REDEX.
    p.have(
        "h_AB_eq: App_t A B = App_t (App_t K_t Ai) B"
    ).by_cong(App_t, "Ai_eq", REFL(p._parse("B")))
    p.have(
        "h_bull_KaiB: "
        "sk_bullet (App_t (App_t K_t Ai) B) = sk_bullet Ai"
    ).by(SK_BULLET_K_REDEX, "Ai", "B")
    p.have(
        "h_bull_AB_eq1: "
        "sk_bullet (App_t A B) = sk_bullet (App_t (App_t K_t Ai) B)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("h_AB_eq")))
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = sk_bullet Ai"
    ).by_trans("h_bull_AB_eq1", "h_bull_KaiB")
    # SYM(h_A1_eq) rewrites App_t K_t A1_in -> A1 (safe).
    # SYM(h_bull_AB) rewrites sk_bullet Ai -> sk_bullet (App_t A B) (safe).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_K",
        [SYM(p.fact("h_A1_eq")), SYM(p.fact("h_bull_AB"))],
    )


def _triangle_S_case(p):
    """S-redex sub-case of _TRIANGLE_APP_CLOSURE.

    Context: Ai, Bi in scope; ``Bi_eq : A = App_t (App_t S_t Ai) Bi``
    (Bi_eq because the outer ``?Ai Bi.`` auto-introduced Ai and the
    inner ?Bi was choose'd).

    App_t A B = App_t (App_t (App_t S_t Ai) Bi) B is an S-redex;
    SK_BULLET_S_REDEX collapses its bullet to
    ``App_t (App_t (sk_bullet Ai) (sk_bullet B))
            (App_t (sk_bullet Bi) (sk_bullet B))``.

    Strategy mirrors _triangle_K_case but with a 2-tuple inversion
    via PAR_STEP_S_APP_APP_INV:
      1. PAR_STEP_S_APP_APP_INV on h_A : A1 = App_t (App_t S_t A1_in)
         B1_in, sk_par_step Ai A1_in, sk_par_step Bi B1_in.
      2. Compute sk_bullet A = App_t (App_t S_t (sk_bullet Ai))
         (sk_bullet Bi) via two SK_BULLET_APP_OTHER (App_t (App_t S_t
         Ai) Bi has 2 App layers, neither K- nor S-redex shape) +
         SK_BULLET_S_T.
      3. PAR_STEP_S_APP_APP_INV on h_A_bull (rewritten through (1)
         and (2)) : sk_par_step A1_in (sk_bullet Ai) and sk_par_step
         B1_in (sk_bullet Bi).
      4. PAR_S with X1 := sk_bullet Ai, Y1 := sk_bullet Bi, Z1 :=
         sk_bullet B.
      5. Fold to goal via SK_BULLET_S_REDEX.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
        CONJUNCT2 as _C2,
    )

    # ---- Step 1: invert h_A. -----------------------------------------
    p.have(
        "h_A_S: sk_par_step (App_t (App_t S_t Ai) Bi) A1"
    ).by_rewrite_of("h_A", [p.fact("Bi_eq")])
    p.have(
        "h_A1_shape: ?XP:nat0. ?YP:nat0. "
        "A1 = App_t (App_t S_t XP) YP /\\ "
        "sk_par_step Ai XP /\\ sk_par_step Bi YP"
    ).by(PAR_STEP_S_APP_APP_INV, "Ai", "Bi", "A1", "h_A_S")
    p.choose("A1_in", from_="h_A1_shape")
    p.choose("B1_in", from_="A1_in_eq")
    p.split(
        "B1_in_eq",
        "(h_A1_eq, h_par_Ai_A1_in, h_par_Bi_B1_in)",
    )

    # ---- Step 2: compute sk_bullet (App_t (App_t S_t Ai) Bi). ---------
    # Inner layer: App_t S_t Ai is not a K/S redex (1 App layer, S_t head).
    _bull_no_redex_guard_atom_head(p, "S_t", "Ai", "SAi")
    p.have(
        "h_bull_SAi_raw: sk_bullet (App_t S_t Ai) = "
        "                App_t (sk_bullet S_t) (sk_bullet Ai)"
    ).by(SK_BULLET_APP_OTHER, "S_t", "Ai", "h_nKnS_SAi")
    p.have(
        "h_bull_SAi: sk_bullet (App_t S_t Ai) = "
        "            App_t S_t (sk_bullet Ai)"
    ).by_rewrite_of("h_bull_SAi_raw", [SK_BULLET_S_T])

    # Outer layer: App_t (App_t S_t Ai) Bi has 2 App layers, neither
    # K- nor S-redex shape.
    _bull_no_redex_guard_app_S_head(p, "Ai", "Bi", "SAB")
    p.have(
        "h_bull_SAB_raw: "
        "sk_bullet (App_t (App_t S_t Ai) Bi) = "
        "App_t (sk_bullet (App_t S_t Ai)) (sk_bullet Bi)"
    ).by(
        SK_BULLET_APP_OTHER, "App_t S_t Ai", "Bi", "h_nKnS_SAB"
    )
    p.have(
        "h_bull_SAB: sk_bullet (App_t (App_t S_t Ai) Bi) = "
        "            App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)"
    ).by_rewrite_of("h_bull_SAB_raw", [p.fact("h_bull_SAi")])

    # ---- Step 3: invert h_A_bull. -------------------------------------
    p.have(
        "h_bull_A_step1: "
        "sk_bullet A = sk_bullet (App_t (App_t S_t Ai) Bi)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("Bi_eq")))
    p.have(
        "h_bull_A: sk_bullet A = "
        "          App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)"
    ).by_trans("h_bull_A_step1", "h_bull_SAB")
    # Same DSL friction as the K-case: h_A1_eq has A1 free inside
    # the A1_in / B1_in @-binders' bodies.  Use by_cong + by_eq_mp.
    p.have(
        "h_A_bull_S_eq: "
        "sk_par_step A1 (sk_bullet A) = "
        "sk_par_step (App_t (App_t S_t A1_in) B1_in) "
        "            (App_t (App_t S_t (sk_bullet Ai)) "
        "                   (sk_bullet Bi))"
    ).by_cong(sk_par_step, "h_A1_eq", "h_bull_A")
    p.have(
        "h_A_bull_S: "
        "sk_par_step (App_t (App_t S_t A1_in) B1_in) "
        "            (App_t (App_t S_t (sk_bullet Ai)) "
        "                   (sk_bullet Bi))"
    ).by_eq_mp("h_A_bull_S_eq", "h_A_bull")
    p.have(
        "h_inv_A1: ?XP:nat0. ?YP:nat0. "
        "App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi) = "
        "  App_t (App_t S_t XP) YP /\\ "
        "sk_par_step A1_in XP /\\ sk_par_step B1_in YP"
    ).by(
        PAR_STEP_S_APP_APP_INV,
        "A1_in", "B1_in",
        "App_t (App_t S_t (sk_bullet Ai)) (sk_bullet Bi)",
        "h_A_bull_S",
    )
    p.choose("Xp", from_="h_inv_A1")
    p.choose("Yp", from_="Xp_eq")
    p.split(
        "Yp_eq", "(h_app_eq, h_par_A1in_Xp, h_par_B1in_Yp)"
    )
    # APP_T_INJ peel outer: App_t S_t (sk_bullet Ai) = App_t S_t Xp;
    # sk_bullet Bi = Yp.
    p.have(
        "h_inj1: App_t S_t (sk_bullet Ai) = App_t S_t Xp /\\ "
        "        sk_bullet Bi = Yp"
    ).by(
        APP_T_INJ,
        "App_t S_t (sk_bullet Ai)", "sk_bullet Bi",
        "App_t S_t Xp", "Yp", "h_app_eq",
    )
    p.have(
        "h_inj1_L: App_t S_t (sk_bullet Ai) = App_t S_t Xp"
    ).by_thm(_C1(p.fact("h_inj1")))
    p.have(
        "h_Yp_eq: sk_bullet Bi = Yp"
    ).by_thm(_C2(p.fact("h_inj1")))
    # APP_T_INJ peel inner: S_t = S_t; sk_bullet Ai = Xp.
    p.have(
        "h_inj2: S_t = S_t /\\ sk_bullet Ai = Xp"
    ).by(
        APP_T_INJ,
        "S_t", "sk_bullet Ai", "S_t", "Xp", "h_inj1_L",
    )
    p.have(
        "h_Xp_eq: sk_bullet Ai = Xp"
    ).by_thm(_C2(p.fact("h_inj2")))
    p.have(
        "h_par_A1in_bullAi: sk_par_step A1_in (sk_bullet Ai)"
    ).by_rewrite_of(
        "h_par_A1in_Xp", [SYM(p.fact("h_Xp_eq"))]
    )
    p.have(
        "h_par_B1in_bullBi: sk_par_step B1_in (sk_bullet Bi)"
    ).by_rewrite_of(
        "h_par_B1in_Yp", [SYM(p.fact("h_Yp_eq"))]
    )

    # ---- Step 4: PAR_S to assemble. -----------------------------------
    p.have(
        "h_conj_3: "
        "sk_par_step A1_in (sk_bullet Ai) /\\ "
        "sk_par_step B1_in (sk_bullet Bi) /\\ "
        "sk_par_step B1 (sk_bullet B)"
    ).by_thm(
        _CONJ(
            p.fact("h_par_A1in_bullAi"),
            _CONJ(
                p.fact("h_par_B1in_bullBi"),
                p.fact("h_B_bull"),
            ),
        )
    )
    p.have(
        "h_par_PAR_S: "
        "sk_par_step "
        "  (App_t (App_t (App_t S_t A1_in) B1_in) B1) "
        "  (App_t "
        "    (App_t (sk_bullet Ai) (sk_bullet B)) "
        "    (App_t (sk_bullet Bi) (sk_bullet B)))"
    ).by(
        PAR_S,
        "A1_in", "sk_bullet Ai",
        "B1_in", "sk_bullet Bi",
        "B1", "sk_bullet B",
        "h_conj_3",
    )

    # ---- Step 5: fold to the goal form. -------------------------------
    # App_t A B = App_t (App_t (App_t S_t Ai) Bi) B (S-redex).
    p.have(
        "h_AB_eq: App_t A B = "
        "         App_t (App_t (App_t S_t Ai) Bi) B"
    ).by_cong(App_t, "Bi_eq", REFL(p._parse("B")))
    # SK_BULLET_S_REDEX: sk_bullet of S-redex collapses.
    p.have(
        "h_bull_SAB_red: "
        "sk_bullet (App_t (App_t (App_t S_t Ai) Bi) B) = "
        "App_t "
        "  (App_t (sk_bullet Ai) (sk_bullet B)) "
        "  (App_t (sk_bullet Bi) (sk_bullet B))"
    ).by(SK_BULLET_S_REDEX, "Ai", "Bi", "B")
    p.have(
        "h_bull_AB_step1: sk_bullet (App_t A B) = "
        "sk_bullet (App_t (App_t (App_t S_t Ai) Bi) B)"
    ).by_thm(AP_TERM(sk_bullet, p.fact("h_AB_eq")))
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = "
        "App_t "
        "  (App_t (sk_bullet Ai) (sk_bullet B)) "
        "  (App_t (sk_bullet Bi) (sk_bullet B))"
    ).by_trans("h_bull_AB_step1", "h_bull_SAB_red")
    # SYM(h_A1_eq) rewrites App_t (App_t S_t A1_in) B1_in -> A1.
    # SYM(h_bull_AB) rewrites the App-of-Apps RHS -> sk_bullet (App A B).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_S",
        [SYM(p.fact("h_A1_eq")), SYM(p.fact("h_bull_AB"))],
    )


def _triangle_other_case(p):
    """App-other sub-case of _TRIANGLE_APP_CLOSURE.

    Context: ``h_nAisK : ~(?Ai. A = App_t K_t Ai)``,
             ``h_nAisSS : ~(?Ai Bi. A = App_t (App_t S_t Ai) Bi)``.

    App_t A B is then neither a K-redex (would require A = App_t K_t
    _) nor an S-redex (would require A = App_t (App_t S_t _) _).
    SK_BULLET_APP_OTHER + PAR_APP on (h_A_bull, h_B_bull) closes.
    """
    from tactics import (
        CONJ as _CONJ,
        CONJUNCT1 as _C1,
    )

    # Lift the A-shape negations to App_t A B negations.
    with p.have(
        "h_nK_AB: ~(?a b. App_t A B = App_t (App_t K_t a) b)"
    ).proof():
        with p.suppose(
            "ex: ?a b. App_t A B = App_t (App_t K_t a) b"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.have(
                "h_inj: A = App_t K_t a /\\ B = b"
            ).by(
                APP_T_INJ, "A", "B",
                "App_t K_t a", "b", "b_eq",
            )
            p.have("h_A_eq: A = App_t K_t a").by_thm(
                _C1(p.fact("h_inj"))
            )
            p.have(
                "h_ex_Ai: ?Ai:nat0. A = App_t K_t Ai"
            ).by_exists(["a"], "h_A_eq")
            p.absurd().by_conj("h_nAisK", "h_ex_Ai")
    with p.have(
        "h_nS_AB: ~(?a b c. App_t A B = "
        "          App_t (App_t (App_t S_t a) b) c)"
    ).proof():
        with p.suppose(
            "ex: ?a b c. App_t A B = "
            "    App_t (App_t (App_t S_t a) b) c"
        ):
            p.choose("a", from_="ex")
            p.choose("b", from_="a_eq")
            p.choose("c", from_="b_eq")
            p.have(
                "h_inj: A = App_t (App_t S_t a) b /\\ B = c"
            ).by(
                APP_T_INJ, "A", "B",
                "App_t (App_t S_t a) b", "c", "c_eq",
            )
            p.have(
                "h_A_eq: A = App_t (App_t S_t a) b"
            ).by_thm(_C1(p.fact("h_inj")))
            p.have(
                "h_ex_AiBi: "
                "?Ai:nat0. ?Bi:nat0. "
                "A = App_t (App_t S_t Ai) Bi"
            ).by_exists(["a", "b"], "h_A_eq")
            p.absurd().by_conj("h_nAisSS", "h_ex_AiBi")
    p.have(
        "h_nKnS_AB: "
        "~(?a b. App_t A B = App_t (App_t K_t a) b) /\\ "
        "~(?a b c. App_t A B = "
        "  App_t (App_t (App_t S_t a) b) c)"
    ).by_thm(_CONJ(p.fact("h_nK_AB"), p.fact("h_nS_AB")))

    # SK_BULLET_APP_OTHER: sk_bullet (App_t A B) = App_t (sk_bullet
    # A) (sk_bullet B).
    p.have(
        "h_bull_AB: sk_bullet (App_t A B) = "
        "           App_t (sk_bullet A) (sk_bullet B)"
    ).by(SK_BULLET_APP_OTHER, "A", "B", "h_nKnS_AB")
    # PAR_APP combines the two triangle conclusions on the children.
    p.have(
        "h_conj_AB_bull: "
        "sk_par_step A1 (sk_bullet A) /\\ "
        "sk_par_step B1 (sk_bullet B)"
    ).by_thm(_CONJ(p.fact("h_A_bull"), p.fact("h_B_bull")))
    p.have(
        "h_par_PAR_APP: sk_par_step (App_t A1 B1) "
        "                          (App_t (sk_bullet A) (sk_bullet B))"
    ).by(
        PAR_APP,
        "A1", "sk_bullet A", "B1", "sk_bullet B",
        "h_conj_AB_bull",
    )
    # Fold RHS App_t (sk_bullet A) (sk_bullet B) -> sk_bullet (App_t A B).
    p.thus(
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_rewrite_of(
        "h_par_PAR_APP", [SYM(p.fact("h_bull_AB"))]
    )


@proof
def _TRIANGLE_APP_CLOSURE(p):
    """The APP-rule closure conjunct of TRIANGLE's P-instantiation:

    |- !A B A1 B1.
         (sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\
         (sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==>
         sk_par_step (App_t A B) (App_t A1 B1) /\\
         sk_par_step (App_t A1 B1) (sk_bullet (App_t A B)).

    Part 1 (sk_par_step (App_t A B) (App_t A1 B1)) is just PAR_APP on
    the two source par-steps.

    Part 2 is a 3-way LEM split on ``A``'s shape (which determines
    whether ``App_t A B`` is a K-redex, S-redex, or App-other):

      * A = App_t K_t Ai           -> _triangle_K_case
      * A = App_t (App_t S_t Ai) Bi -> _triangle_S_case
      * otherwise                  -> _triangle_other_case
    """
    from classical import EXCLUDED_MIDDLE
    from tactics import CONJ as _CONJ

    p.goal(
        "!A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==> "
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    )
    p.fix("A B A1 B1")
    p.assume(
        "((h_A, h_A_bull), (h_B, h_B_bull)): "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B))"
    )

    # ---- Part 1: sk_par_step (App_t A B) (App_t A1 B1) ---------------
    p.have(
        "h_conj_AB: sk_par_step A A1 /\\ sk_par_step B B1"
    ).by_thm(_CONJ(p.fact("h_A"), p.fact("h_B")))
    p.have(
        "h_part1: sk_par_step (App_t A B) (App_t A1 B1)"
    ).by(
        PAR_APP, "A", "A1", "B", "B1", "h_conj_AB"
    )

    # ---- Part 2: 3-way LEM split on A's shape ------------------------
    with p.have(
        "h_part2: sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).proof():
        with p.cases_on(
            EXCLUDED_MIDDLE, "?Ai:nat0. A = App_t K_t Ai"
        ):
            with p.case("h_AisK: ?Ai:nat0. A = App_t K_t Ai"):
                # cases_on auto-binds Ai; Ai_eq: A = App_t K_t Ai.
                _triangle_K_case(p)
            with p.case(
                "h_nAisK: ~(?Ai:nat0. A = App_t K_t Ai)"
            ):
                with p.cases_on(
                    EXCLUDED_MIDDLE,
                    "?Ai:nat0. ?Bi:nat0. "
                    "A = App_t (App_t S_t Ai) Bi",
                ):
                    with p.case(
                        "h_AisSS: ?Ai:nat0. ?Bi:nat0. "
                        "A = App_t (App_t S_t Ai) Bi"
                    ):
                        # Ai and Bi auto-bound; Bi_eq in scope.
                        _triangle_S_case(p)
                    with p.case(
                        "h_nAisSS: "
                        "~(?Ai:nat0. ?Bi:nat0. "
                        "  A = App_t (App_t S_t Ai) Bi)"
                    ):
                        _triangle_other_case(p)

    p.thus(
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_thm(_CONJ(p.fact("h_part1"), p.fact("h_part2")))


@proof
def SK_BULLET_TRIANGLE(p):
    """|- !A B. sk_par_step A B ==> sk_par_step B (sk_bullet A).

    Takahashi's triangle property.  Proven via impredicative
    P-instantiation with the strengthened invariant:

       P := \\AA BB. sk_par_step AA BB /\\ sk_par_step BB (sk_bullet AA).

    The strengthening (first conjunct preserves the underlying par_step)
    is required by the APP-rule case: to invert source-side redex
    shapes via PAR_STEP_K_APP_INV / PAR_STEP_S_APP_APP_INV, we need
    direct access to ``sk_par_step A A1`` not just the P-version
    ``sk_par_step A1 (sk_bullet A)``.

    Four closure conjuncts:
      REFL Z   -- PAR_REFL + BULLET_REFL.
      K-rule   -- PAR_K (first part) + SK_BULLET_K_REDEX rewrite (second).
      S-rule   -- PAR_S + SK_BULLET_S_REDEX + double PAR_APP composition.
      APP-rule -- delegated to ``_TRIANGLE_APP_CLOSURE``.

    With closures(P) built, SPEC h_AB-unfolded at P, MP, CONJUNCT2.

    DSL friction noted inline at two sites (P-lambda bvar collision,
    K-rule closure bvar collision).
    """
    from tactics import CONJUNCT2

    p.goal(
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (sk_bullet A)"
    )
    p.fix("A B")
    p.assume("h_AB: sk_par_step A B")

    A_t = p._parse("A")
    B_t = p._parse("B")
    h_AB_th = p.fact("h_AB")

    # Unfold sk_par_step A B to !P. closures(P) ==> P A B, then SPEC at
    # the strengthened P via ``by_spec`` (SPECL + BETA_NORM in one shot:
    # the closure form's per-rule lambda applications all reduce in one
    # pass).  DSL friction: P's bvars must not collide with the outer
    # ``A``, ``B`` (fixed) -- use ``AA``, ``BB``.
    sps_unfold = unfold_def_at(SK_PAR_STEP_DEF, A_t, B_t)
    forall_P = EQ_MP(sps_unfold, h_AB_th)
    P_lambda = p._parse(
        "\\AA:nat0. \\BB:nat0. "
        "sk_par_step AA BB /\\ sk_par_step BB (sk_bullet AA)"
    )
    p.have("spec_P_beta:").by_spec(forall_P, P_lambda)
    # spec_P_beta : |- closures_beta ==> sk_par_step A B /\
    #                                    sk_par_step B (sk_bullet A)

    # ---- Build closures_beta as h_cl ------------------------------------

    # REFL conjunct: !Z. sk_par_step Z Z /\ sk_par_step Z (sk_bullet Z).
    with p.have(
        "c_refl: !Z:nat0. sk_par_step Z Z /\\ "
        "                 sk_par_step Z (sk_bullet Z)"
    ).proof():
        p.fix("Z")
        p.have("z_refl: sk_par_step Z Z").by_thm(
            SPEC(p._parse("Z"), PAR_REFL)
        )
        p.have("z_bull: sk_par_step Z (sk_bullet Z)").by_thm(
            SPEC(p._parse("Z"), BULLET_REFL)
        )
        p.thus(
            "sk_par_step Z Z /\\ sk_par_step Z (sk_bullet Z)"
        ).by_thm(CONJ(p.fact("z_refl"), p.fact("z_bull")))

    # K-rule conjunct.  DSL friction: the outer ``fix("A B")`` puts
    # ``A`` and ``B`` in scope, so the inner closure conjuncts can't
    # ``fix("A B ...")`` -- HolError on duplicate fix.  We rename the
    # closure-form's inner bvars to ``U V U1 V1`` (alpha-equivalent to
    # ``A Y A1 Y1``; CONJ + MP go through EQ_MP / alphaorder, so the
    # final closures_th still alpha-matches spec_P_beta's antecedent).
    with p.have(
        "c_K: !U:nat0. !V:nat0. !U1:nat0. !V1:nat0. "
        "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
        "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) ==> "
        "sk_par_step (App_t (App_t K_t U) V) U1 /\\ "
        "sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
    ).proof():
        p.fix("U V U1 V1")
        p.assume(
            "((h_U_step, h_U_bull), (h_V_step, h_V_bull)): "
            "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
            "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V))"
        )
        p.have(
            "k_first: sk_par_step (App_t (App_t K_t U) V) U1"
        ).by(
            PAR_K, "U", "U1", "V", "V1",
            CONJ(p.fact("h_U_step"), p.fact("h_V_step")),
        )
        p.have(
            "bull_K: sk_bullet (App_t (App_t K_t U) V) = sk_bullet U"
        ).by(SK_BULLET_K_REDEX, "U", "V")
        p.have(
            "k_second: sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
        ).by_rewrite_of("h_U_bull", [SYM(p.fact("bull_K"))])
        p.thus(
            "sk_par_step (App_t (App_t K_t U) V) U1 /\\ "
            "sk_par_step U1 (sk_bullet (App_t (App_t K_t U) V))"
        ).by_thm(CONJ(p.fact("k_first"), p.fact("k_second")))

    # S-rule conjunct.  Same bvar rename: U V W U1 V1 W1.
    with p.have(
        "c_S: !U:nat0. !V:nat0. !W:nat0. "
        "!U1:nat0. !V1:nat0. !W1:nat0. "
        "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
        "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) /\\ "
        "(sk_par_step W W1 /\\ sk_par_step W1 (sk_bullet W)) ==> "
        "sk_par_step (App_t (App_t (App_t S_t U) V) W) "
        "            (App_t (App_t U1 W1) (App_t V1 W1)) /\\ "
        "sk_par_step (App_t (App_t U1 W1) (App_t V1 W1)) "
        "            (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
    ).proof():
        p.fix("U V W U1 V1 W1")
        p.assume(
            "((h_U_step, h_U_bull), "
            " (h_V_step, h_V_bull), "
            " (h_W_step, h_W_bull)): "
            "(sk_par_step U U1 /\\ sk_par_step U1 (sk_bullet U)) /\\ "
            "(sk_par_step V V1 /\\ sk_par_step V1 (sk_bullet V)) /\\ "
            "(sk_par_step W W1 /\\ sk_par_step W1 (sk_bullet W))"
        )
        # First conjunct via PAR_S.
        p.have(
            "s_first: sk_par_step (App_t (App_t (App_t S_t U) V) W) "
            "                     (App_t (App_t U1 W1) (App_t V1 W1))"
        ).by(
            PAR_S, "U", "U1", "V", "V1", "W", "W1",
            CONJ(
                p.fact("h_U_step"),
                CONJ(p.fact("h_V_step"), p.fact("h_W_step")),
            ),
        )
        # Second conjunct.  Bullet-unfold of the S-redex.
        p.have(
            "bull_S: sk_bullet (App_t (App_t (App_t S_t U) V) W) = "
            "        App_t (App_t (sk_bullet U) (sk_bullet W)) "
            "              (App_t (sk_bullet V) (sk_bullet W))"
        ).by(SK_BULLET_S_REDEX, "U", "V", "W")
        # Combine three IH-second-parts via PAR_APP twice.
        p.have(
            "h_UW: sk_par_step (App_t U1 W1) "
            "                  (App_t (sk_bullet U) (sk_bullet W))"
        ).by(
            PAR_APP, "U1", "sk_bullet U", "W1", "sk_bullet W",
            CONJ(p.fact("h_U_bull"), p.fact("h_W_bull")),
        )
        p.have(
            "h_VW: sk_par_step (App_t V1 W1) "
            "                  (App_t (sk_bullet V) (sk_bullet W))"
        ).by(
            PAR_APP, "V1", "sk_bullet V", "W1", "sk_bullet W",
            CONJ(p.fact("h_V_bull"), p.fact("h_W_bull")),
        )
        p.have(
            "h_outer: sk_par_step "
            "  (App_t (App_t U1 W1) (App_t V1 W1)) "
            "  (App_t (App_t (sk_bullet U) (sk_bullet W)) "
            "         (App_t (sk_bullet V) (sk_bullet W)))"
        ).by(
            PAR_APP,
            "App_t U1 W1", "App_t (sk_bullet U) (sk_bullet W)",
            "App_t V1 W1", "App_t (sk_bullet V) (sk_bullet W)",
            CONJ(p.fact("h_UW"), p.fact("h_VW")),
        )
        p.have(
            "s_second: sk_par_step "
            "  (App_t (App_t U1 W1) (App_t V1 W1)) "
            "  (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
        ).by_rewrite_of("h_outer", [SYM(p.fact("bull_S"))])
        p.thus(
            "sk_par_step (App_t (App_t (App_t S_t U) V) W) "
            "            (App_t (App_t U1 W1) (App_t V1 W1)) /\\ "
            "sk_par_step (App_t (App_t U1 W1) (App_t V1 W1)) "
            "            (sk_bullet (App_t (App_t (App_t S_t U) V) W))"
        ).by_thm(CONJ(p.fact("s_first"), p.fact("s_second")))

    # APP-rule conjunct: delegated to _TRIANGLE_APP_CLOSURE.  Its bvars
    # (A B A1 B1) do not need renaming -- this is a by_thm with a
    # stand-alone lemma; the inner !A binders stay bound, alpha-equivalent
    # to closures_beta.
    p.have(
        "c_APP: !A:nat0. !B:nat0. !A1:nat0. !B1:nat0. "
        "(sk_par_step A A1 /\\ sk_par_step A1 (sk_bullet A)) /\\ "
        "(sk_par_step B B1 /\\ sk_par_step B1 (sk_bullet B)) ==> "
        "sk_par_step (App_t A B) (App_t A1 B1) /\\ "
        "sk_par_step (App_t A1 B1) (sk_bullet (App_t A B))"
    ).by_thm(_TRIANGLE_APP_CLOSURE)

    # ---- Assemble closures, MP, extract second conjunct ----------------

    closures_th = CONJ(
        p.fact("c_refl"),
        CONJ(p.fact("c_K"), CONJ(p.fact("c_S"), p.fact("c_APP"))),
    )
    result_pair = MP(p.fact("spec_P_beta"), closures_th)
    # result_pair: sk_par_step A B /\ sk_par_step B (sk_bullet A)

    p.thus("sk_par_step B (sk_bullet A)").by_thm(CONJUNCT2(result_pair))


# ---------------------------------------------------------------------------
# Diamond / confluence theorems for ``sk_par_step``, built on
# SK_BULLET_TRIANGLE:
#   * TRIANGLE_EXISTS   -- existential wrapper over sk_bullet + triangle.
#   * PAR_STEP_DIAMOND  -- W := sk_bullet X.
#   * PAR_STEPS_STRIP   -- RTC induction on top of DIAMOND.
#   * PAR_STEPS_CONFLUENT -- second RTC induction on top of STRIP.
# ---------------------------------------------------------------------------


@proof
def TRIANGLE_EXISTS(p):
    """|- ?bullet. !A B. sk_par_step A B ==> sk_par_step B (bullet A).

    Witness: ``sk_bullet`` (the top-level complete-development function).
    Body: ``SK_BULLET_TRIANGLE``.
    """
    p.goal(
        "?bullet:nat0->nat0. "
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (bullet A)"
    )
    p.have(
        "h_tri: !A:nat0. !B:nat0. "
        "       sk_par_step A B ==> sk_par_step B (sk_bullet A)"
    ).by_thm(SK_BULLET_TRIANGLE)
    p.thus(
        "?bullet:nat0->nat0. "
        "!A:nat0. !B:nat0. "
        "sk_par_step A B ==> sk_par_step B (bullet A)"
    ).by_exists(["sk_bullet"], "h_tri")


@proof
def PAR_STEP_DIAMOND(p):
    """|- !X Y Z. sk_par_step X Y /\\ sk_par_step X Z
                   ==> ?W. sk_par_step Y W /\\ sk_par_step Z W.

    Takahashi diamond: from the triangle property at (X, Y) and
    (X, Z), both Y and Z par-step to the common reduct ``bullet X``.
    Witness W := bullet X.
    """
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step X Y /\\ sk_par_step X Z ==> "
        "?W:nat0. sk_par_step Y W /\\ sk_par_step Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_step X Y /\\ sk_par_step X Z"
    )
    p.have(
        "h_te: ?bullet:nat0->nat0. "
        "      !A:nat0. !B:nat0. "
        "      sk_par_step A B ==> sk_par_step B (bullet A)"
    ).by_thm(TRIANGLE_EXISTS)
    p.choose("bullet", from_="h_te")
    # bullet_eq: !A B. sk_par_step A B ==> sk_par_step B (bullet A).
    p.have(
        "h_Y_bull: sk_par_step Y (bullet X)"
    ).by("bullet_eq", "X", "Y", "h_XY")
    p.have(
        "h_Z_bull: sk_par_step Z (bullet X)"
    ).by("bullet_eq", "X", "Z", "h_XZ")
    p.thus(
        "?W:nat0. sk_par_step Y W /\\ sk_par_step Z W"
    ).by_exists(["bullet X"], "h_Y_bull", "h_Z_bull")


@proof
def PAR_STEPS_STRIP(p):
    """|- !X Y Z. sk_par_step X Y /\\ sk_par_steps X Z
                   ==> ?W. sk_par_steps Y W /\\ sk_par_step Z W.

    Strip lemma: combine a one-step par-step with an RTC chain by
    closing the diamond at each joint.  Impredicative induction on the
    RTC chain ``sk_par_steps X Z`` -- instantiate the encoding's P
    with
        \\A B. !V. sk_par_step A V ==>
                   ?W. sk_par_steps V W /\\ sk_par_step B W.
    REFL: take W := V (PAR_STEPS_REFL + the given step).
    STEP: given A→B and IH at B; for V from sk_par_step A V,
          PAR_STEP_DIAMOND on (A→B, A→V) finds U; IH at U yields W;
          chain V→U + U→*W via PAR_STEPS_STEP gives V→*W.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_step X Y /\\ sk_par_steps X Z ==> "
        "?W:nat0. sk_par_steps Y W /\\ sk_par_step Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_step X Y /\\ sk_par_steps X Z"
    )

    spec_XZ = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Z")
    )
    h_forall = EQ_MP(spec_XZ, p.fact("h_XZ"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!V:nat0. sk_par_step A V ==> "
        "?W:nat0. sk_par_steps V W /\\ sk_par_step B W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # REFL closure -- bvar Zb to dodge outer Z.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!V:nat0. sk_par_step Zb V ==> "
        "?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W"
    ).proof():
        p.fix("Zb V")
        p.assume("h_ZbV: sk_par_step Zb V")
        p.have("h_VV: sk_par_steps V V").by(PAR_STEPS_REFL, "V")
        p.thus(
            "?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W"
        ).by_exists(["V"], "h_VV", "h_ZbV")

    # STEP closure -- bvars a b c to dodge outer.
    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!V:nat0. sk_par_step b V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step c W) ==> "
        "(!V:nat0. sk_par_step a V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step c W)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!V. sk_par_step b V ==> "
            "    ?W. sk_par_steps V W /\\ sk_par_step c W)"
        )
        p.fix("V")
        p.assume("h_aV: sk_par_step a V")
        p.have(
            "h_conj_diam: sk_par_step a b /\\ sk_par_step a V"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_aV")))
        p.have(
            "h_diam: ?U. sk_par_step b U /\\ sk_par_step V U"
        ).by(PAR_STEP_DIAMOND, "a", "b", "V", "h_conj_diam")
        p.choose("U", from_="h_diam")
        p.split("U_eq", "(h_bU, h_VU)")
        p.have(
            "h_IH_at: ?W. sk_par_steps U W /\\ sk_par_step c W"
        ).by("h_IH", "U", "h_bU")
        p.choose("W", from_="h_IH_at")
        p.split("W_eq", "(h_UW, h_cW)")
        p.have(
            "h_conj_chain: sk_par_step V U /\\ sk_par_steps U W"
        ).by_thm(CONJ(p.fact("h_VU"), p.fact("h_UW")))
        p.have(
            "h_VW: sk_par_steps V W"
        ).by(PAR_STEPS_STEP, "V", "U", "W", "h_conj_chain")
        p.thus(
            "?W:nat0. sk_par_steps V W /\\ sk_par_step c W"
        ).by_exists(["W"], "h_VW", "h_cW")

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !V:nat0. sk_par_step Zb V ==> "
        "    ?W:nat0. sk_par_steps V W /\\ sk_par_step Zb W) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!V:nat0. sk_par_step b V ==> "
        "        ?W:nat0. sk_par_steps V W /\\ sk_par_step c W) ==> "
        "    (!V:nat0. sk_par_step a V ==> "
        "        ?W:nat0. sk_par_steps V W /\\ sk_par_step c W))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXZ: !V:nat0. sk_par_step X V ==> "
        "       ?W:nat0. sk_par_steps V W /\\ sk_par_step Z W"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus(
        "?W:nat0. sk_par_steps Y W /\\ sk_par_step Z W"
    ).by("h_PXZ", "Y", "h_XY")


@proof
def PAR_STEPS_CONFLUENT(p):
    """|- !X Y Z. sk_par_steps X Y /\\ sk_par_steps X Z
                   ==> ?W. sk_par_steps Y W /\\ sk_par_steps Z W.

    Church-Rosser for the par-step RTC.  Impredicative induction on
    the first chain ``sk_par_steps X Y`` with ``PAR_STEPS_STRIP``
    closing each joint:
        P A B := !V. sk_par_steps A V ==>
                     ?W. sk_par_steps B W /\\ sk_par_steps V W.
    REFL: take W := V (the given chain + PAR_STEPS_REFL on V).
    STEP: a -> b given + IH at b; for V from sk_par_steps a V, STRIP
          on (a->b, a->*V) finds U with sk_par_steps b U /\\ sk_par_step
          V U; IH at U produces W; chain V->U + U->*W via PAR_STEPS_STEP
          gives V->*W.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_steps X Y /\\ sk_par_steps X Z ==> "
        "?W:nat0. sk_par_steps Y W /\\ sk_par_steps Z W"
    )
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_XZ): sk_par_steps X Y /\\ sk_par_steps X Z"
    )

    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!V:nat0. sk_par_steps A V ==> "
        "?W:nat0. sk_par_steps B W /\\ sk_par_steps V W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # REFL closure -- bvar Zb to dodge outer Z.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!V:nat0. sk_par_steps Zb V ==> "
        "?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W"
    ).proof():
        p.fix("Zb V")
        p.assume("h_ZbV: sk_par_steps Zb V")
        p.have("h_VV: sk_par_steps V V").by(PAR_STEPS_REFL, "V")
        p.thus(
            "?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W"
        ).by_exists(["V"], "h_ZbV", "h_VV")

    # STEP closure -- bvars a b c to dodge outer.
    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!V:nat0. sk_par_steps b V ==> "
        "    ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W) ==> "
        "(!V:nat0. sk_par_steps a V ==> "
        "    ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!V. sk_par_steps b V ==> "
            "    ?W. sk_par_steps c W /\\ sk_par_steps V W)"
        )
        p.fix("V")
        p.assume("h_aV: sk_par_steps a V")
        p.have(
            "h_conj_strip: sk_par_step a b /\\ sk_par_steps a V"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_aV")))
        p.have(
            "h_strip: ?U. sk_par_steps b U /\\ sk_par_step V U"
        ).by(PAR_STEPS_STRIP, "a", "b", "V", "h_conj_strip")
        p.choose("U", from_="h_strip")
        p.split("U_eq", "(h_bU, h_VU)")
        p.have(
            "h_IH_at: ?W. sk_par_steps c W /\\ sk_par_steps U W"
        ).by("h_IH", "U", "h_bU")
        p.choose("W", from_="h_IH_at")
        p.split("W_eq", "(h_cW, h_UW)")
        p.have(
            "h_conj_chain: sk_par_step V U /\\ sk_par_steps U W"
        ).by_thm(CONJ(p.fact("h_VU"), p.fact("h_UW")))
        p.have(
            "h_VW: sk_par_steps V W"
        ).by(PAR_STEPS_STEP, "V", "U", "W", "h_conj_chain")
        p.thus(
            "?W:nat0. sk_par_steps c W /\\ sk_par_steps V W"
        ).by_exists(["W"], "h_cW", "h_VW")

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !V:nat0. sk_par_steps Zb V ==> "
        "    ?W:nat0. sk_par_steps Zb W /\\ sk_par_steps V W) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!V:nat0. sk_par_steps b V ==> "
        "        ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W) ==> "
        "    (!V:nat0. sk_par_steps a V ==> "
        "        ?W:nat0. sk_par_steps c W /\\ sk_par_steps V W))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: !V:nat0. sk_par_steps X V ==> "
        "       ?W:nat0. sk_par_steps Y W /\\ sk_par_steps V W"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus(
        "?W:nat0. sk_par_steps Y W /\\ sk_par_steps Z W"
    ).by("h_PXY", "Z", "h_XZ")


# ---------------------------------------------------------------------------
# Generic par-step infrastructure used by HALTS_INVARIANT and the
# par/bullet bridge: PAR_STEPS_TRANS (composition) and
# NORMAL_STABILITY_PAR_STEPS (par-step from a normal goes nowhere).
# ---------------------------------------------------------------------------


@proof
def PAR_STEPS_TRANS(p):
    """|- !X Y Z. sk_par_steps X Y /\\ sk_par_steps Y Z
                   ==> sk_par_steps X Z.

    Transitivity of the par-step RTC.  Impredicative induction on the
    first chain: instantiate the encoding's P with
    ``\\A B. !W. sk_par_steps B W ==> sk_par_steps A W``.  REFL closure
    is the identity, STEP closure prepends one par-step via
    ``PAR_STEPS_STEP``.
    """
    p.goal(
        "!X:nat0. !Y:nat0. !Z:nat0. "
        "sk_par_steps X Y /\\ sk_par_steps Y Z ==> sk_par_steps X Z"
    )
    from tactics import BETA_RULE
    p.fix("X Y Z")
    p.assume(
        "(h_XY, h_YZ): sk_par_steps X Y /\\ sk_par_steps Y Z"
    )

    # Unfold ``sk_par_steps X Y`` to its impredicative universal.
    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    # SPEC at the lifted P; BETA_RULE cleans redexes.
    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. "
        "!W:nat0. sk_par_steps B W ==> sk_par_steps A W"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    # Lifted closures.  Bvars renamed to ``Zb / a b c w`` to dodge the
    # outer ``X Y Z`` fixed names.
    with p.have(
        "lifted_refl: !Zb:nat0. "
        "!w:nat0. sk_par_steps Zb w ==> sk_par_steps Zb w"
    ).proof():
        p.fix("Zb w")
        p.assume("h: sk_par_steps Zb w")
        p.thus("sk_par_steps Zb w").by_thm(p.fact("h"))

    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ "
        "(!w:nat0. sk_par_steps c w ==> sk_par_steps b w) ==> "
        "(!w:nat0. sk_par_steps c w ==> sk_par_steps a w)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ "
            "(!w. sk_par_steps c w ==> sk_par_steps b w)"
        )
        p.fix("w")
        p.assume("h_cw: sk_par_steps c w")
        p.have("h_bw: sk_par_steps b w").by("h_IH", "w", "h_cw")
        p.have(
            "h_conj: sk_par_step a b /\\ sk_par_steps b w"
        ).by_thm(CONJ(p.fact("h_ab"), p.fact("h_bw")))
        p.thus("sk_par_steps a w").by(
            PAR_STEPS_STEP, "a", "b", "w", "h_conj"
        )

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. !w:nat0. sk_par_steps Zb w ==> sk_par_steps Zb w) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ "
        "    (!w. sk_par_steps c w ==> sk_par_steps b w) ==> "
        "    (!w. sk_par_steps c w ==> sk_par_steps a w))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: !w:nat0. sk_par_steps Y w ==> sk_par_steps X w"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus("sk_par_steps X Z").by("h_PXY", "Z", "h_YZ")

@proof
def NORMAL_STABILITY_PAR_STEP(p):
    """|- !X Y. is_normal X /\\ sk_par_step X Y ==> Y = X.

    Direct from IS_NORMAL_DEF: unfold ``is_normal X`` to
    ``!Z. sk_par_step X Z ==> Z = X`` and specialise at Z := Y.
    """
    p.goal(
        "!X:nat0. !Y:nat0. is_normal X /\\ sk_par_step X Y ==> Y = X"
    )
    p.fix("X Y")
    p.assume("(h_normX, h_XY): is_normal X /\\ sk_par_step X Y")
    p.have(
        "h_un: !Z:nat0. sk_par_step X Z ==> Z = X"
    ).by_unfold("h_normX", IS_NORMAL_DEF)
    p.thus("Y = X").by("h_un", "Y", "h_XY")


@proof
def NORMAL_STABILITY_PAR_STEPS(p):
    """|- !X Y. is_normal X /\\ sk_par_steps X Y ==> Y = X.

    Lifts NORMAL_STABILITY_PAR_STEP through the RTC.  Impredicative
    induction with P := ``\\A B. is_normal A ==> B = A``:
      REFL : tautology.
      STEP : a -> b given + IH ``is_normal b ==> c = b``; single-step
             stability at (a, b) gives b = a, which transports
             is_normal a to is_normal b; IH yields c = b; TRANS gives
             c = a.
    """
    from tactics import BETA_RULE
    p.goal(
        "!X:nat0. !Y:nat0. is_normal X /\\ sk_par_steps X Y ==> Y = X"
    )
    p.fix("X Y")
    p.assume(
        "(h_normX, h_XY): is_normal X /\\ sk_par_steps X Y"
    )

    spec_XY = unfold_def_at(
        SK_PAR_STEPS_DEF, p._parse("X"), p._parse("Y")
    )
    h_forall = EQ_MP(spec_XY, p.fact("h_XY"))

    P_lifted = p._parse(
        "\\A:nat0. \\B:nat0. is_normal A ==> B = A"
    )
    inst = SPEC(P_lifted, h_forall)
    inst_beta = BETA_RULE(inst)

    with p.have(
        "lifted_refl: !Zb:nat0. is_normal Zb ==> Zb = Zb"
    ).proof():
        p.fix("Zb")
        p.assume("h: is_normal Zb")
        p.thus("Zb = Zb").by_thm(REFL(p._parse("Zb")))

    with p.have(
        "lifted_step: !a:nat0. !b:nat0. !c:nat0. "
        "sk_par_step a b /\\ (is_normal b ==> c = b) ==> "
        "(is_normal a ==> c = a)"
    ).proof():
        p.fix("a b c")
        p.assume(
            "(h_ab, h_IH): sk_par_step a b /\\ (is_normal b ==> c = b)"
        )
        p.assume("h_norm_a: is_normal a")
        p.have(
            "h_conj: is_normal a /\\ sk_par_step a b"
        ).by_thm(CONJ(p.fact("h_norm_a"), p.fact("h_ab")))
        p.have("h_ba: b = a").by(
            NORMAL_STABILITY_PAR_STEP, "a", "b", "h_conj"
        )
        # is_normal b via a -> b rewrite (rule SYM h_ba = a = b).
        p.have("h_norm_b: is_normal b").by_rewrite_of(
            "h_norm_a", [SYM(p.fact("h_ba"))]
        )
        p.have("h_cb: c = b").by("h_IH", "h_norm_b")
        p.thus("c = a").by_thm(
            TRANS(p.fact("h_cb"), p.fact("h_ba"))
        )

    p.have(
        "lifted_cl: "
        "(!Zb:nat0. is_normal Zb ==> Zb = Zb) /\\ "
        "(!a:nat0. !b:nat0. !c:nat0. "
        "    sk_par_step a b /\\ (is_normal b ==> c = b) ==> "
        "    (is_normal a ==> c = a))"
    ).by_thm(CONJ(p.fact("lifted_refl"), p.fact("lifted_step")))

    p.have(
        "h_PXY: is_normal X ==> Y = X"
    ).by_thm(MP(inst_beta, p.fact("lifted_cl")))

    p.thus("Y = X").by("h_PXY", "h_normX")

