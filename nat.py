"""Formalisation of Landau's *Foundations of Analysis*, Chapter 1.

Module stack:
  ``fusion.py`` -- primitive HOL Light kernel.
  ``axioms.py`` -- bool definitions and the 3 logical axioms (ETA, SELECT, INFINITY).
  ``logic.py``  -- derived bool inference rules + Diaconescu's EM.
  ``num.py``    -- num signature, Peano Axioms 3-5, INDUCT.
  ``nat.py``    -- this file: addition, multiplication, Landau Theorems 1-36.

Each theorem is proved using only the 10 primitive inference rules
(REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP, DEDUCT_ANTISYM_RULE,
INST, INST_TYPE) plus rules imported from ``logic.py`` and ``num.py``.

Run ``python nat.py`` -- the kernel rejects any unsound step, so a clean
finish prints 20 step-confirmation lines and means every theorem is valid.

Coverage:
  #1  All 5 Peano axioms (Axiom 1 by typing; Axiom 2's existence by
      taking SUC as a total function; Axioms 3, 4, 5 as new_axioms in num.py).
  #2  Theorems 1, 2, 3, 5, 6, 7, 8, 9 (both existence and mutual-exclusion
      halves of the trichotomy).  Definition 1 (addition) admitted as
      Landau's recursion equations (the existence-half proof of
      Theorem 4 needs the primitive-recursion principle for num,
      derivable from Axiom 5 but out of scope here).
  #3  Definitions 2, 3, 4, 5 and Theorems 10-17, 18, 19 (a/b/c), 20,
      21, 22 (a/b), 23, 24, 25, 26, 27.
  #4  Definition 6 (multiplication, parallel to Definition 1) and
      Theorems 29, 30, 31, 32 (a/b/c), 33, 34, 35 (a/b), 36.
"""

from fusion import (
    Var, Const, Comb, Abs,
    bool_ty, aty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    mk_type, new_axiom, new_constant, new_type,
    type_of, dest_eq, dest_comb, dest_abs,
    rator, rand, freesl, frees, vfree_in, variant, aconv,
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST, INST_TYPE,
    concl, hyp, HolError, new_basic_definition,
)
from axioms import (
    T, F,
    T_DEF, AND_DEF, IMP_DEF, FORALL_DEF, EXISTS_DEF, F_DEF, NOT_DEF,
    SELECT_AX,
    mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)
from logic import (
    pp, pp_thm,
    AP_TERM, AP_THM, BETA_CONV, BETA_NORM, SYM, TRUTH, EQT_ELIM, EQT_INTRO,
    SPEC, GEN, CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP, UNDISCH,
    CONTR, NOT_ELIM, NOT_INTRO, EQF_INTRO, EQF_ELIM,
    OR_DEF, mk_or, DISJ1, DISJ2, DISJ_CASES,
    MK_EQ, NE_SYM, REWRITE_NE, EXISTS,
    EXCLUDED_MIDDLE, NOT_NOT_ELIM, NOT_EX_TO_FORALL_NOT, NOT_FORALL_TO_EX_NOT,
    PROVE_HYP, ELIM_EX,
    _INFIX,
)
from num import (
    num_ty, ONE, SUC, mk_suc,
    x, y, z, u, v, w, P,
    AXIOM_3, AXIOM_4, INDUCTION, INDUCT, NUM_RECURSION,
)


# ---------------------------------------------------------------------------
# Theorem 1.   |- !x y. ~(x = y) ==> ~(x' = y')
# Proof (Landau): "Otherwise x' = y' would hold, hence by Axiom 4 x = y."
# Formally: contrapositive of Axiom 4.
# ---------------------------------------------------------------------------

def _prove_satz_1():
    hyp_neq  = mk_not(mk_eq(x, y))           # ~(x = y)
    hyp_eq_s = mk_eq(mk_suc(x), mk_suc(y))   # x' = y'
    # Axiom 4 specialised to x, y:  |- x' = y' ==> x = y
    ax4_xy = SPEC(y, SPEC(x, AXIOM_4))
    th_xy  = MP(ax4_xy, ASSUME(hyp_eq_s))                         # {x'=y'} |- x = y
    th_F   = MP(NOT_ELIM(ASSUME(hyp_neq)), th_xy)                 # {~(x=y), x'=y'} |- F
    th_imp = DISCH(hyp_eq_s, th_F)                                # {~(x=y)} |- x'=y' ==> F
    th_not = NOT_INTRO(th_imp)                                    # {~(x=y)} |- ~(x'=y')
    th_imp2 = DISCH(hyp_neq, th_not)                              # |- ~(x=y) ==> ~(x'=y')
    return GEN(x, GEN(y, th_imp2))

SATZ_1 = _prove_satz_1()


# ---------------------------------------------------------------------------
# Theorem 2.   |- !x. ~(x' = x)
# Proof (Landau): induction on x.
#   I)  1' != 1 by Axiom 3.
#   II) From x' != x, Theorem 1 gives (x')' != x'.
# ---------------------------------------------------------------------------

def _prove_satz_2():
    pred = mk_abs(x, mk_not(mk_eq(mk_suc(x), x)))               # \x. ~(x' = x)
    # Base: |- ~(1' = 1)  by Axiom 3 specialised to 1.
    base = SPEC(ONE, AXIOM_3)
    # Step: |- !x. ~(x' = x) ==> ~((x')' = x')   from Theorem 1 with x:=x', y:=x.
    step_inst = SPEC(x, SPEC(mk_suc(x), SATZ_1))
    step = GEN(x, step_inst)
    return INDUCT(pred, base, step)

SATZ_2 = _prove_satz_2()


# ---------------------------------------------------------------------------
# Theorem 3.   |- !x. ~(x = 1) ==> ?u. x = u'
# Proof (Landau): induction.  Trivial at x = 1 (the hypothesis is
#                 contradictory); in the step: at x' take u = x.
# ---------------------------------------------------------------------------

def _prove_satz_3():
    body_x = mk_imp(mk_not(mk_eq(x, ONE)),
                    mk_exists(u, mk_eq(x, mk_suc(u))))
    pred = mk_abs(x, body_x)

    # Base: |- ~(1 = 1) ==> ?u. 1 = u'.  The hypothesis is false (REFL contradicts it).
    not_1_1 = mk_not(mk_eq(ONE, ONE))
    th_F = MP(NOT_ELIM(ASSUME(not_1_1)), REFL(ONE))           # {~(1=1)} |- F
    ex_1 = mk_exists(u, mk_eq(ONE, mk_suc(u)))
    base = DISCH(not_1_1, CONTR(ex_1, th_F))                  # |- ~(1=1) ==> ?u. 1 = u'

    # Step:  body[x] ==> body[x'].   The IH is unused -- at x' we always have u = x as witness.
    not_xs_1 = mk_not(mk_eq(mk_suc(x), ONE))
    pred_u = mk_abs(u, mk_eq(mk_suc(x), mk_suc(u)))
    th_ex = EXISTS(pred_u, x, REFL(mk_suc(x)))                # |- ?u. SUC x = SUC u
    body_xs_th = DISCH(not_xs_1, th_ex)                       # |- ~(SUC x = 1) ==> ?u. SUC x = SUC u
    step = GEN(x, DISCH(body_x, body_xs_th))                  # |- !x. body[x] ==> body[x']

    return INDUCT(pred, base, step)

SATZ_3 = _prove_satz_3()


# ---------------------------------------------------------------------------
# Theorem 4 / Definition 1.
#
# Landau proves: there is exactly one operation + : num x num -> num with
#   x + 1 = x'    and    x + y' = (x + y)'.
#
# Uniqueness follows by routine induction.  For existence, we use the
# primitive-recursion principle `NUM_RECURSION` proved in num.py:
#   |- !c h. ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
# Specialising at  c := SUC x,  h := \k a. SUC a,  yields a function fn
# with fn 1 = SUC x and fn (SUC y) = SUC (fn y).  Define
#   x + y := (@fn. fn 1 = SUC x /\ !n. fn (SUC n) = SUC (fn n)) y.
# Then ADD_1 and ADD_SUC become *theorems*.
# ---------------------------------------------------------------------------

# The predicate selecting the recursive `+ x` function.
_add_fn = Var("fn", mk_fun_ty(num_ty, num_ty))
_add_n  = Var("n", num_ty)

def _add_pred_term(x_t):
    """\\fn. fn 1 = SUC x_t /\\ !n. fn (SUC n) = SUC (fn n)."""
    fn_1 = mk_comb(_add_fn, ONE)
    fn_n = mk_comb(_add_fn, _add_n)
    fn_sn = mk_comb(_add_fn, mk_suc(_add_n))
    body = mk_and(mk_eq(fn_1, mk_suc(x_t)),
                   mk_forall(_add_n,
                       mk_eq(fn_sn, mk_suc(fn_n))))
    return mk_abs(_add_fn, body)

_select_add = mk_const("@", [(mk_fun_ty(num_ty, num_ty), aty)])

# Define  +  =  \x y. (@fn. fn 1 = SUC x /\ !n. fn (SUC n) = SUC (fn n)) y.
_x_d = Var("x", num_ty)
_y_d = Var("y", num_ty)
_add_def_rhs = mk_abs(_x_d, mk_abs(_y_d,
    mk_comb(mk_comb(_select_add, _add_pred_term(_x_d)), _y_d)))

ADD_DEF = new_basic_definition(
    mk_eq(Var("+", mk_fun_ty(num_ty, mk_fun_ty(num_ty, num_ty))),
          _add_def_rhs))
PLUS = mk_const("+", [])

def mk_add(a, b):
    return mk_comb(mk_comb(PLUS, a), b)

# Make the pretty-printer aware of "+".
_INFIX.add("+")


def _prove_add_eqs():
    """Derive ADD_1 = |- !x. x + 1 = SUC x  and  ADD_SUC = |- !x y. x + SUC y = SUC (x + y)."""
    # Specialise NUM_RECURSION at A := num, c := SUC x, h := \k a. SUC a.
    NR_num = INST_TYPE([(num_ty, aty)], NUM_RECURSION)        # |- !c h. ?fn. fn 1 = c /\ ...   (over num->num)
    h_var_loc = Var("h", mk_fun_ty(num_ty, mk_fun_ty(num_ty, num_ty)))
    # h := \k:num. \a:num. SUC a.
    k_v = Var("k", num_ty)
    a_v = Var("a", num_ty)
    h_const = mk_abs(k_v, mk_abs(a_v, mk_suc(a_v)))
    spec_c = SPEC(mk_suc(x), NR_num)                            # |- !h. ?fn. fn 1 = SUC x /\ !n. fn (SUC n) = h n (fn n)
    spec_ch = SPEC(h_const, spec_c)
    # spec_ch : |- ?fn. fn 1 = SUC x /\ !n. fn (SUC n) = (\k a. SUC a) n (fn n).
    # The RHS still has the lambda; we'll need to BETA-reduce.

    # Apply SELECT_AX: |- !P x. P x ==> P (@P).
    # The predicate here is _add_pred_term(x) but with `(\k a. SUC a) n (fn n)` rather
    # than `SUC (fn n)`.  Let's call the literal predicate from spec_ch `pred_raw`.
    # spec_ch._concl = ?fn. body_raw[fn].   Predicate = \fn. body_raw[fn].
    # Extract via exists-def of EXISTS: spec_ch is mk_exists(_, pred_raw_body) so
    # the exists-predicate is the lambda inside the existential.  Equivalent:
    pred_raw = spec_ch._concl.arg   # the lambda inside  ?fn. body_raw
    # That is, pred_raw = Abs(fn, body_raw[fn]).
    fn_var_raw = pred_raw.bvar      # `fn` variable (num -> num)

    # Use ELIM_EX to extract  body_raw[witness]  where witness = @pred_raw.
    # We then convert body_raw[witness] to "the" form (by beta-reducing the inner h).
    sel_at_pred = mk_comb(_select_add, pred_raw)   # @fn. body_raw[fn]
    # body_raw[witness] is body_raw with fn := sel_at_pred.

    # Build the cleaned predicate (beta-reduced): _add_pred_term(x).
    pred_clean = _add_pred_term(x)
    sel_at_pred_clean = mk_comb(_select_add, pred_clean)   # @fn. clean body[fn]

    # PROOF STRATEGY:
    # Show pred_raw = pred_clean as terms (alpha-equivalent up to beta).  Actually
    # they're not alpha-equal; pred_raw has `(\k a. SUC a) n (fn n)` and pred_clean
    # has `SUC (fn n)`.  We need a theorem  |- pred_raw fn = pred_clean fn  for any
    # fn, or pointwise equality lifted via FUN_EXT, or just operate at the level of
    # the body once instantiated.

    # Simpler approach: extract the witness body from spec_ch (which has the raw form)
    # and then prove the cleaned form by transforming each piece.

    def body_fn(th_raw):
        # th_raw : {body_raw[witness]} |- body_raw[witness] where witness = @pred_raw.
        return th_raw

    body_raw_at_w = ELIM_EX(pred_raw, spec_ch._concl, body_fn)   # {?fn. body_raw} |- body_raw[witness]
    body_raw_th   = PROVE_HYP(spec_ch, body_raw_at_w)             # |- body_raw[witness]
    # body_raw[witness] = (witness 1 = SUC x) /\ (!n. witness (SUC n) = (\k a. SUC a) n (witness n)).

    # Project conjuncts.
    raw_conj1 = CONJUNCT1(body_raw_th)   # |- witness 1 = SUC x
    raw_conj2 = CONJUNCT2(body_raw_th)   # |- !n. witness (SUC n) = (\k a. SUC a) n (witness n)

    # `witness` here = sel_at_pred (the @ over pred_raw, which is the literal raw lambda).
    # But our definition used pred_clean (the literal beta-reduced version).
    # So sel_at_pred is NOT literally sel_at_pred_clean: they differ in the embedded h.
    # We need to relate the two @-witnesses.
    # Approach: prove pred_raw = pred_clean (as functions), then sel_at_pred = sel_at_pred_clean
    # via AP_TERM on the @ constant.

    # Step a: |- pred_raw = pred_clean  (as Abs(fn, ...) terms with same body modulo beta).
    # Build via ABS over the body equality.
    fn_x = mk_comb(_add_fn, mk_suc(_add_n))
    h_n_fnn_raw = mk_comb(mk_comb(h_const, _add_n), mk_comb(_add_fn, _add_n))
    # |- (\k a. SUC a) n (fn n) = SUC (fn n)
    # Step: BETA on (\k a. SUC a) n: |- (\k a. SUC a) n = (\a. SUC a).
    h_at_n = BETA_CONV(mk_comb(h_const, _add_n))               # |- (\k a. SUC a) n = (\a. SUC a)
    # Then AP_THM at (fn n): |- ((\k a. SUC a) n) (fn n) = (\a. SUC a) (fn n).
    h_at_n_fnn = AP_THM(h_at_n, mk_comb(_add_fn, _add_n))      # |- ... = (\a. SUC a) (fn n)
    # BETA again: (\a. SUC a) (fn n) = SUC (fn n).
    final_beta = BETA_CONV(mk_comb(mk_abs(a_v, mk_suc(a_v)), mk_comb(_add_fn, _add_n)))
    # Combine:
    h_red = TRANS(h_at_n_fnn, final_beta)                       # |- (\k a. SUC a) n (fn n) = SUC (fn n)

    # Now show raw_body = clean_body where bodies live under the same fn binder.
    # raw_inner_eq: |- witness (SUC n) = (\k a. SUC a) n (witness n).  We derived spec for arbitrary n.
    # We want: !n. witness (SUC n) = SUC (witness n).
    # Use raw_conj2 spec'ed at _add_n and chain with h_red[fn := witness].
    raw_at_n = SPEC(_add_n, raw_conj2)   # |- witness (SUC n) = (\k a. SUC a) n (witness n)
    # Now apply h_red, but h_red is over fn variable. We need to instantiate fn to witness.
    h_red_at_w = INST([(sel_at_pred, _add_fn)], h_red)   # |- (\k a. SUC a) n (witness n) = SUC (witness n)
    raw_clean_n = TRANS(raw_at_n, h_red_at_w)             # |- witness (SUC n) = SUC (witness n)
    raw_clean_forall = GEN(_add_n, raw_clean_n)            # |- !n. witness (SUC n) = SUC (witness n)

    # Now combine into clean predicate body:  P_clean witness =
    #   (witness 1 = SUC x) /\ (!n. witness (SUC n) = SUC (witness n)).
    P_clean_at_w = CONJ(raw_conj1, raw_clean_forall)       # |- witness 1 = SUC x /\ !n. witness (SUC n) = SUC (witness n)
    # That is: |- pred_clean witness  (after BETA).  Build:
    pred_clean_at_w = mk_comb(pred_clean, sel_at_pred)
    pred_clean_at_w_eq = BETA_CONV(pred_clean_at_w)        # |- pred_clean witness = (clean body)
    pred_clean_witness = EQ_MP(SYM(pred_clean_at_w_eq), P_clean_at_w)   # |- pred_clean witness

    # Now apply SELECT_AX:  |- pred_clean witness ==> pred_clean (@pred_clean).
    sel_inst = INST_TYPE([(mk_fun_ty(num_ty, num_ty), aty)], SELECT_AX)
    sel_imp = SPEC(sel_at_pred, SPEC(pred_clean, sel_inst))   # |- pred_clean witness ==> pred_clean (@pred_clean)
    pred_clean_at_select = MP(sel_imp, pred_clean_witness)     # |- pred_clean (@pred_clean)
    # i.e. |- (@fn. ...) 1 = SUC x  /\  !n. (@fn. ...) (SUC n) = SUC ((@fn. ...) n)
    sel_pred_clean = sel_at_pred_clean                         # @fn. pred_clean fn
    select_at_clean_eq = BETA_CONV(mk_comb(pred_clean, sel_pred_clean))
    select_at_clean_body = EQ_MP(select_at_clean_eq, pred_clean_at_select)
    # Now project the two conjuncts.
    sel_at_1_eq_sx = CONJUNCT1(select_at_clean_body)   # |- (@fn. ...) 1 = SUC x
    sel_at_sn_eq   = CONJUNCT2(select_at_clean_body)   # |- !n. (@fn. ...) (SUC n) = SUC ((@fn. ...) n)

    # ADD_1: |- !x. x + 1 = SUC x.   x + 1 = (\x y. (@fn. ...) y) x 1 = (@fn. ...) 1 = SUC x.
    plus_x = mk_comb(PLUS, x)
    # First, PLUS = _add_def_rhs.  Apply each side at x, 1.
    add_def_th = ADD_DEF                                # |- + = \x y. (@fn. ...) y
    plus_at_x = AP_THM(add_def_th, x)                    # |- + x = (\x y. (@fn. ...) y) x
    plus_at_x_beta = TRANS(plus_at_x, BETA_CONV(rand(plus_at_x._concl)))
    # |- + x = \y. (@fn[x]. ...) y
    plus_at_x_at_1 = AP_THM(plus_at_x_beta, ONE)         # |- + x 1 = (\y. ...) 1
    plus_at_x_at_1_beta = TRANS(plus_at_x_at_1, BETA_CONV(rand(plus_at_x_at_1._concl)))
    # |- + x 1 = (@fn. ...) 1
    add1_eq = TRANS(plus_at_x_at_1_beta, sel_at_1_eq_sx)   # |- x + 1 = SUC x
    ADD_1_th = GEN(x, add1_eq)

    # ADD_SUC: |- !x y. x + SUC y = SUC (x + y).
    plus_at_x_at_sy = AP_THM(plus_at_x_beta, mk_suc(y))    # |- + x (SUC y) = (\y. ...) (SUC y)
    plus_at_x_at_sy_beta = TRANS(plus_at_x_at_sy,
                                  BETA_CONV(rand(plus_at_x_at_sy._concl)))
    # |- + x (SUC y) = (@fn. ...) (SUC y)
    sel_at_sy = SPEC(y, sel_at_sn_eq)                       # |- (@fn. ...) (SUC y) = SUC ((@fn. ...) y)
    # SUC ((@fn. ...) y) = SUC (x + y).  Need to rewrite (@fn. ...) y back to + x y.
    plus_at_x_at_y = AP_THM(plus_at_x_beta, y)              # |- + x y = (\y. ...) y
    plus_at_x_at_y_beta = TRANS(plus_at_x_at_y,
                                 BETA_CONV(rand(plus_at_x_at_y._concl)))
    # |- + x y = (@fn. ...) y
    suc_eq = AP_TERM(SUC, SYM(plus_at_x_at_y_beta))          # |- SUC ((@fn. ...) y) = SUC (x + y)
    add_suc_eq = TRANS(plus_at_x_at_sy_beta, TRANS(sel_at_sy, suc_eq))   # |- x + SUC y = SUC (x + y)
    ADD_SUC_th = GEN(x, GEN(y, add_suc_eq))

    return ADD_1_th, ADD_SUC_th


ADD_1, ADD_SUC = _prove_add_eqs()


# ---------------------------------------------------------------------------
# Theorem 5 (associative law of addition):
#   |- !x y z. (x + y) + z = x + (y + z).
# Proof (Landau): induction on z.
# ---------------------------------------------------------------------------

def _prove_satz_5():
    body_z = mk_eq(mk_add(mk_add(x, y), z), mk_add(x, mk_add(y, z)))
    pred = mk_abs(z, body_z)
    x_plus = mk_comb(PLUS, x)

    # Base z = 1:  (x+y)+1 = SUC(x+y) = x + SUC y = x + (y+1).
    a = SPEC(mk_add(x, y), ADD_1)                     # |- (x+y)+1 = SUC(x+y)
    b = SPEC(y, SPEC(x, ADD_SUC))                     # |- x+(SUC y) = SUC(x+y)
    c = SPEC(y, ADD_1)                                # |- y+1 = SUC y
    base = TRANS(a, TRANS(SYM(b), AP_TERM(x_plus, SYM(c))))   # |- (x+y)+1 = x+(y+1)

    # Step: assume IH body_z, prove body_z[z'].
    body_zs = mk_eq(mk_add(mk_add(x, y), mk_suc(z)),
                    mk_add(x, mk_add(y, mk_suc(z))))
    IH = ASSUME(body_z)
    s1 = SPEC(z, SPEC(mk_add(x, y), ADD_SUC))         # |- (x+y)+SUC z = SUC((x+y)+z)
    s2 = AP_TERM(SUC, IH)                              # |- SUC((x+y)+z) = SUC(x+(y+z))
    s3 = SYM(SPEC(mk_add(y, z), SPEC(x, ADD_SUC)))     # |- SUC(x+(y+z)) = x + SUC(y+z)
    s4 = AP_TERM(x_plus, SYM(SPEC(z, SPEC(y, ADD_SUC))))  # |- x+SUC(y+z) = x+(y+SUC z)
    step_inner = TRANS(s1, TRANS(s2, TRANS(s3, s4)))
    step = GEN(z, DISCH(body_z, step_inner))           # |- !z. body_z ==> body_z'

    forall_z = INDUCT(pred, base, step)                # |- !z. body_z
    return GEN(x, GEN(y, forall_z))

SATZ_5 = _prove_satz_5()


# ---------------------------------------------------------------------------
# Helpers from "the construction in the proof of Theorem 4" -- facts about
# addition on the LEFT argument that are not part of Definition 1 directly.
#
# ONE_PLUS :  |- !y.    1 + y = SUC y
# SUC_PLUS :  |- !x y.  SUC x + y = SUC (x + y)
# ---------------------------------------------------------------------------

def _prove_one_plus():
    pred = mk_abs(y, mk_eq(mk_add(ONE, y), mk_suc(y)))
    base = SPEC(ONE, ADD_1)                                   # |- 1 + 1 = SUC 1
    body_y = mk_eq(mk_add(ONE, y), mk_suc(y))
    IH = ASSUME(body_y)
    s1 = SPEC(y, SPEC(ONE, ADD_SUC))                          # |- 1 + SUC y = SUC(1 + y)
    s2 = AP_TERM(SUC, IH)                                     # |- SUC(1+y) = SUC(SUC y)
    step_inner = TRANS(s1, s2)
    step = GEN(y, DISCH(body_y, step_inner))
    return INDUCT(pred, base, step)

ONE_PLUS = _prove_one_plus()

def _prove_suc_plus():
    body_y = mk_eq(mk_add(mk_suc(x), y), mk_suc(mk_add(x, y)))
    pred = mk_abs(y, body_y)
    a = SPEC(mk_suc(x), ADD_1)                                # |- SUC x + 1 = SUC(SUC x)
    b = AP_TERM(SUC, SYM(SPEC(x, ADD_1)))                     # |- SUC(SUC x) = SUC(x + 1)
    base = TRANS(a, b)
    IH = ASSUME(body_y)
    s1 = SPEC(y, SPEC(mk_suc(x), ADD_SUC))                    # |- SUC x + SUC y = SUC(SUC x + y)
    s2 = AP_TERM(SUC, IH)                                     # |- SUC(SUC x + y) = SUC(SUC(x+y))
    s3 = AP_TERM(SUC, SYM(SPEC(y, SPEC(x, ADD_SUC))))         # |- SUC(SUC(x+y)) = SUC(x + SUC y)
    step_inner = TRANS(s1, TRANS(s2, s3))
    step = GEN(y, DISCH(body_y, step_inner))
    return GEN(x, INDUCT(pred, base, step))

SUC_PLUS = _prove_suc_plus()


# ---------------------------------------------------------------------------
# Theorem 6 (commutative law of addition):
#   |- !x y. x + y = y + x.
# Proof (Landau): induction on x with y fixed.
# ---------------------------------------------------------------------------

def _prove_satz_6():
    body_x = mk_eq(mk_add(x, y), mk_add(y, x))
    pred = mk_abs(x, body_x)
    base = TRANS(SPEC(y, ONE_PLUS), SYM(SPEC(y, ADD_1)))      # |- 1 + y = y + 1
    IH = ASSUME(body_x)
    s1 = SPEC(y, SPEC(x, SUC_PLUS))                           # |- SUC x + y = SUC(x + y)
    s2 = AP_TERM(SUC, IH)                                     # |- SUC(x+y) = SUC(y+x)
    s3 = SYM(SPEC(x, SPEC(y, ADD_SUC)))                       # |- SUC(y+x) = y + SUC x
    step_inner = TRANS(s1, TRANS(s2, s3))
    step = GEN(x, DISCH(body_x, step_inner))
    forall_x = INDUCT(pred, base, step)
    # Reorder quantifiers: prove !x !y.  (currently y free, induction on x)
    return GEN(x, GEN(y, SPEC(x, forall_x)))

SATZ_6 = _prove_satz_6()


# ---------------------------------------------------------------------------
# Theorem 7.   |- !x y. ~(y = x + y).
# Proof (Landau): induction on y with x fixed.
#   I)  1 != x + 1, since x + 1 = x' and 1 != x'.
#   II) From y != x + y: y' != (x+y)' = x + y'  by Theorem 1 and ADD_SUC.
# ---------------------------------------------------------------------------

def _prove_satz_7():
    body_y = mk_not(mk_eq(y, mk_add(x, y)))
    pred = mk_abs(y, body_y)

    # Base: |- ~(1 = x + 1).
    sx_neq_1 = SPEC(x, AXIOM_3)                              # |- ~(SUC x = 1)
    one_neq_sx = NE_SYM(sx_neq_1)                            # |- ~(1 = SUC x)
    base = REWRITE_NE(one_neq_sx, REFL(ONE), SYM(SPEC(x, ADD_1)))   # |- ~(1 = x + 1)

    # Step.
    IH = ASSUME(body_y)                                      # {body_y} |- ~(y = x+y)
    s1_imp = SPEC(mk_add(x, y), SPEC(y, SATZ_1))             # |- ~(y=x+y) ==> ~(SUC y = SUC(x+y))
    th_ne_succ = MP(s1_imp, IH)                              # {body_y} |- ~(SUC y = SUC(x+y))
    eq_rhs = SYM(SPEC(y, SPEC(x, ADD_SUC)))                  # |- SUC(x+y) = x + SUC y
    step_inner = REWRITE_NE(th_ne_succ, REFL(mk_suc(y)), eq_rhs)   # {body_y} |- ~(SUC y = x + SUC y)
    step = GEN(y, DISCH(body_y, step_inner))

    forall_y = INDUCT(pred, base, step)
    return GEN(x, forall_y)

SATZ_7 = _prove_satz_7()


# ---------------------------------------------------------------------------
# Theorem 8.   |- !x y z. ~(y = z) ==> ~(x + y = x + z).
# Proof (Landau): induction on x with y, z fixed and y != z.
# ---------------------------------------------------------------------------

def _prove_satz_8():
    hyp_yz = mk_not(mk_eq(y, z))
    body_x = mk_not(mk_eq(mk_add(x, y), mk_add(x, z)))
    pred = mk_abs(x, body_x)

    # Base:  {hyp_yz} |- ~(1 + y = 1 + z).
    s1_yz = SPEC(z, SPEC(y, SATZ_1))                            # |- ~(y=z) ==> ~(SUC y = SUC z)
    th_ne_suc = MP(s1_yz, ASSUME(hyp_yz))                       # {hyp_yz} |- ~(SUC y = SUC z)
    base = REWRITE_NE(th_ne_suc,
                      SYM(SPEC(y, ONE_PLUS)),
                      SYM(SPEC(z, ONE_PLUS)))                   # {hyp_yz} |- ~(1+y = 1+z)

    # Step:  body[x] ==> body[x'].
    IH = ASSUME(body_x)
    s1_xy = SPEC(mk_add(x, z), SPEC(mk_add(x, y), SATZ_1))      # |- ~(x+y=x+z) ==> ~(SUC(x+y)=SUC(x+z))
    th_ne_sum = MP(s1_xy, IH)
    step_inner = REWRITE_NE(th_ne_sum,
                            SYM(SPEC(y, SPEC(x, SUC_PLUS))),
                            SYM(SPEC(z, SPEC(x, SUC_PLUS))))    # {body_x} |- ~(SUC x + y = SUC x + z)
    step = GEN(x, DISCH(body_x, step_inner))

    forall_x = INDUCT(pred, base, step)                          # {hyp_yz} |- !x. body_x
    spec_x = SPEC(x, forall_x)                                   # {hyp_yz} |- body_x
    return GEN(x, GEN(y, GEN(z, DISCH(hyp_yz, spec_x))))

SATZ_8 = _prove_satz_8()


# ---------------------------------------------------------------------------
# Helper:  |- !x. (x = 1) \/ (?u. x = u').
# Every natural number is either 1 or the successor of some natural number.
# This is the "M = {1} u {x : ?u. x = u'}" lemma underpinning Landau's
# proof of Theorem 3 -- restated as a clean disjunction for use in Theorem 9.
# ---------------------------------------------------------------------------

def _prove_lemma_pred():
    body_x = mk_or(mk_eq(x, ONE), mk_exists(u, mk_eq(x, mk_suc(u))))
    pred = mk_abs(x, body_x)
    base = DISJ1(REFL(ONE), mk_exists(u, mk_eq(ONE, mk_suc(u))))
    pred_u = mk_abs(u, mk_eq(mk_suc(x), mk_suc(u)))
    th_ex = EXISTS(pred_u, x, REFL(mk_suc(x)))
    body_xs_th = DISJ2(mk_eq(mk_suc(x), ONE), th_ex)
    step = GEN(x, DISCH(body_x, body_xs_th))
    return INDUCT(pred, base, step)

LEMMA_PRED = _prove_lemma_pred()


# ---------------------------------------------------------------------------
# Theorem 9.   |- !x y. (x = y) \/ (?u. x = y + u) \/ (?v. y = x + v).
#
# Landau states "exactly one"; part B (existence of at least one case)
# is proved here.  Part A (mutual exclusion) is left unproved.
# Together they would give the trichotomy in full strength.
#
# Proof B (Landau): induction on y with x fixed.
# ---------------------------------------------------------------------------

def _build_satz9_body(x_t, y_t):
    """`(x = y) \\/ (?u. x = y + u) \\/ (?v. y = x + v)` as a term."""
    case1 = mk_eq(x_t, y_t)
    case2 = mk_exists(u, mk_eq(x_t, mk_add(y_t, u)))
    case3 = mk_exists(v, mk_eq(y_t, mk_add(x_t, v)))
    return mk_or(case1, mk_or(case2, case3))

def _prove_satz_9_exist():
    body_y = _build_satz9_body(x, y)
    pred = mk_abs(y, body_y)
    case2_y = mk_exists(u, mk_eq(x, mk_add(y, u)))
    case3_y = mk_exists(v, mk_eq(y, mk_add(x, v)))

    # === Base y = 1 ===
    body_1 = _build_satz9_body(x, ONE)
    case1_1 = mk_eq(x, ONE)
    case2_1 = mk_exists(u, mk_eq(x, mk_add(ONE, u)))
    case3_1 = mk_exists(v, mk_eq(ONE, mk_add(x, v)))
    rest_1  = mk_or(case2_1, case3_1)

    # From LEMMA_PRED: x = 1 \/ ?u. x = u'. Case-split.
    lem_x = SPEC(x, LEMMA_PRED)        # |- (x = 1) \/ (?u. x = u')
    # Case x = 1: apply DISJ1 of body_1.
    case_x1_to_body = DISJ1(ASSUME(case1_1), rest_1)        # {x=1} |- body_1
    branch_x1 = DISCH(case1_1, case_x1_to_body)             # |- (x=1) ==> body_1
    # Case ?u. x = u': from witness u with x = u' = 1 + u, derive case2_1.
    pred_u_for_lem = mk_abs(u, mk_eq(x, mk_suc(u)))
    hyp_ex_u = mk_exists(u, mk_eq(x, mk_suc(u)))
    # Inside the existential, we need to extract u. Use SELECT_AX to choose a witness.
    # From {hyp_ex_u} build {hyp_ex_u} |- ?u. x = 1 + u. Use SELECT.
    # Strategy: from `?u. x = u'` and `1 + u = u'` (ONE_PLUS), derive `?u. x = 1 + u`.
    # We'll use SELECT-based CHOOSE: extract u via @ operator.
    sel_const = mk_const("@", [(num_ty, aty)])
    sel_u = mk_comb(sel_const, pred_u_for_lem)              # @u. x = u'
    # SELECT_AX specialised: !P x. P x ==> P (@P).  At type num.
    sel_ax_inst = INST_TYPE([(num_ty, aty)], SELECT_AX)
    sel_ax_pred = SPEC(u, SPEC(pred_u_for_lem, sel_ax_inst))
    # sel_ax_pred : |- pred_u_for_lem u ==> pred_u_for_lem (@pred_u_for_lem)
    # i.e., |- (x = u') ==> (x = (@u. x = u')')   modulo BETA.
    # Easier: we just need to use existing existential infrastructure.
    # Alternative: from `?u. x = u'`, work under the existential by introducing
    # ASSUME of `x = u'`, deriving `?u. x = 1 + u`, then DISCH. The CHOOSE-style
    # rule that uses SELECT.
    # Rather than rolling our own CHOOSE here, take a constructive shortcut:
    # use the helper ELIM_EX defined below.
    # (defined immediately before this function ↓)
    th_x_eq_1pu = ELIM_EX(pred_u_for_lem, hyp_ex_u, _existq_witness_to_case2(x))
    # th_x_eq_1pu : {hyp_ex_u} |- ?u. x = 1 + u
    case_xs_to_body = DISJ2(case1_1, DISJ1(th_x_eq_1pu, case3_1))   # {hyp_ex_u} |- body_1
    branch_xs = DISCH(hyp_ex_u, case_xs_to_body)
    base = DISJ_CASES(lem_x, branch_x1, branch_xs)          # |- body_1

    # === Step  body[y] ==> body[y'] ===
    IH = ASSUME(body_y)                       # {body_y} |- body_y
    body_ys = _build_satz9_body(x, mk_suc(y))
    case1_ys = mk_eq(x, mk_suc(y))
    case2_ys = mk_exists(u, mk_eq(x, mk_add(mk_suc(y), u)))
    case3_ys = mk_exists(v, mk_eq(mk_suc(y), mk_add(x, v)))
    rest_ys  = mk_or(case2_ys, case3_ys)

    # Case 1) at y: x = y. Then y' = y + 1 = x + 1, so case 3) at y'.
    case1_y = mk_eq(x, y)
    th_xy = ASSUME(case1_y)                                     # {x=y} |- x=y
    th_yy_1 = SPEC(y, ADD_1)                                    # |- y+1 = SUC y
    th_xy_1 = TRANS(SYM(th_yy_1),                               # |- SUC y = y+1 = x+1
                    AP_TERM(mk_comb(_eq_const_for(num_ty), ONE) if False else
                            None, None) ) if False else None
    # Build SUC y = x + 1: from y = x and ADD_1, y+1 = SUC y, so SUC y = y+1 = x+1.
    th_y_eq_x = SYM(th_xy)                                     # {x=y} |- y = x
    # SUC y = y + 1
    th_sy_eq_y1 = SYM(th_yy_1)                                 # |- SUC y = y + 1
    # y + 1 = x + 1   (from y = x, AP_THM: (y+) = (x+); then AP_THM again on 1)
    plus_y = mk_comb(PLUS, y)
    plus_x = mk_comb(PLUS, x)
    th_plus_eq = AP_THM(AP_TERM(PLUS, th_y_eq_x), ONE)         # {x=y} |- y+1 = x+1
    th_sy_eq_x1 = TRANS(th_sy_eq_y1, th_plus_eq)               # {x=y} |- SUC y = x + 1
    # Build ?v. SUC y = x + v with witness v=1.
    pred_v_case3 = mk_abs(v, mk_eq(mk_suc(y), mk_add(x, v)))
    th_case3_ys = EXISTS(pred_v_case3, ONE, th_sy_eq_x1)
    branch_case1 = DISCH(case1_y,
                         DISJ2(case1_ys, DISJ2(case2_ys, th_case3_ys)))

    # Case 2) at y: ?u. x = y + u. Sub-cases u = 1 vs u ≠ 1.
    case2_y = mk_exists(u, mk_eq(x, mk_add(y, u)))
    branch_case2 = _satz9_step_case2(x, y, body_ys, case1_ys, case2_ys, case3_ys, rest_ys)

    # Case 3) at y: ?v. y = x + v. Then y' = (x+v)' = x + v', so case 3) at y'.
    case3_y = mk_exists(v, mk_eq(y, mk_add(x, v)))
    branch_case3 = _satz9_step_case3(x, y, body_ys, case1_ys, case2_ys, case3_ys, rest_ys)

    # Combine: body_y = case1_y \/ (case2_y \/ case3_y).
    inner_or_y = mk_or(case2_y, case3_y)
    inner_branches = DISJ_CASES(ASSUME(inner_or_y), branch_case2, branch_case3)
    inner_disch = DISCH(inner_or_y, inner_branches)            # |- (case2 \/ case3) ==> body_ys
    step_inner = DISJ_CASES(IH, branch_case1, inner_disch)     # {body_y} |- body_ys
    step = GEN(y, DISCH(body_y, step_inner))

    forall_y = INDUCT(pred, base, step)
    return GEN(x, GEN(y, SPEC(y, forall_y)))


# Helpers used inside _prove_satz_9_exist.  They depend only on what's
# already defined above this function in the file.

def _existq_witness_to_case2(x_t):
    """Given a SELECT-extracted witness u with x = u', returns a function
    that, when applied to a hypothesis `{x = u'} |- x = u'`, yields
    `|- ?u. x = 1 + u` (using ONE_PLUS to rewrite u' as 1+u)."""
    def _go(witness_eq):
        # witness_eq : {x = w'} |- x = w'   for some chosen w
        # Rewrite RHS: w' = 1 + w (SYM ONE_PLUS spec w).
        _, rhs = dest_eq(witness_eq._concl)        # rhs = SUC w
        w_t = rand(rhs)                            # = w
        eq_w = SYM(SPEC(w_t, ONE_PLUS))            # |- SUC w = 1 + w
        x_eq_1pw = TRANS(witness_eq, eq_w)         # {...} |- x = 1 + w
        pred_u = mk_abs(u, mk_eq(x_t, mk_add(ONE, u)))
        return EXISTS(pred_u, w_t, x_eq_1pw)
    return _go


# Step branches for Theorem 9 (Cases 2 and 3 at y).

def _satz9_step_case2(x_t, y_t, body_ys, case1_ys, case2_ys, case3_ys, rest_ys):
    # Hypothesis: ?u. x = y + u.
    case2_y = mk_exists(u, mk_eq(x_t, mk_add(y_t, u)))
    pred_u_2 = mk_abs(u, mk_eq(x_t, mk_add(y_t, u)))

    def _from_witness(witness_eq):
        # witness_eq : {x = y + w} |- x = y + w   for w = the SELECT witness.
        _, rhs = dest_eq(witness_eq._concl)        # rhs = y + w
        w_t = rand(rhs)                            # = w
        # Sub-case A: w = 1.  Then x = y + 1 = SUC y, so case1_ys.
        # Sub-case B: w != 1.  By Theorem 3, w = w0' = 1 + w0.  Then
        #   x = y + (1 + w0) = (y + 1) + w0 = SUC y + w0   →  case2_ys with witness w0.
        from_lemma_pred = SPEC(w_t, LEMMA_PRED)    # |- (w = 1) \/ (?u. w = u')

        # Sub-A: w = 1
        th_w_eq_1 = ASSUME(mk_eq(w_t, ONE))
        # x = y + w.  AP_TERM (y +) on w=1: y + w = y + 1.  Combined with witness_eq.
        th_x_eq_y1 = TRANS(witness_eq,
                           AP_TERM(mk_comb(PLUS, y_t), th_w_eq_1))   # {witness, w=1} |- x = y + 1
        th_x_eq_sy = TRANS(th_x_eq_y1, SPEC(y_t, ADD_1))             # {...} |- x = SUC y
        # That's case1_ys.  Build body_ys via DISJ1.
        sub_A = DISJ1(th_x_eq_sy, mk_or(case2_ys, case3_ys))         # {...} |- body_ys
        branch_A = DISCH(mk_eq(w_t, ONE), sub_A)

        # Sub-B: ?u. w = u'.
        sub_B_hyp = mk_exists(u, mk_eq(w_t, mk_suc(u)))
        pred_u_for_w = mk_abs(u, mk_eq(w_t, mk_suc(u)))

        def _from_w0_witness(w0_eq):
            # w0_eq : {w = w0'} |- w = w0'.
            _, rhs2 = dest_eq(w0_eq._concl)
            w0_t = rand(rhs2)                                      # = w0
            # x = y + w = y + (1 + w0) = (y + 1) + w0 = SUC y + w0.
            eq_w0 = SYM(SPEC(w0_t, ONE_PLUS))                      # |- SUC w0 = 1 + w0
            th_w_eq_1pw0 = TRANS(w0_eq, eq_w0)                     # {...} |- w = 1 + w0
            th_x_eq_y1w0 = TRANS(witness_eq,
                                  AP_TERM(mk_comb(PLUS, y_t), th_w_eq_1pw0))   # x = y + (1 + w0)
            # y + (1 + w0) = (y + 1) + w0   by SYM Theorem 5
            assoc = SPEC(w0_t, SPEC(ONE, SPEC(y_t, SATZ_5)))       # |- (y+1)+w0 = y+(1+w0)
            th_x_eq_y1pw0 = TRANS(th_x_eq_y1w0, SYM(assoc))        # x = (y+1) + w0
            # y + 1 = SUC y
            ya = SPEC(y_t, ADD_1)                                  # |- y + 1 = SUC y
            ap_w0 = AP_THM(AP_TERM(PLUS, ya), w0_t)                # |- (y+1)+w0 = (SUC y)+w0
            th_x_eq_syw0 = TRANS(th_x_eq_y1pw0, ap_w0)             # x = SUC y + w0
            pred_u_case2_ys = mk_abs(u, mk_eq(x_t, mk_add(mk_suc(y_t), u)))
            return EXISTS(pred_u_case2_ys, w0_t, th_x_eq_syw0)     # ?u. x = SUC y + u
        # Apply ELIM_EX to extract w0 and complete sub-B.
        th_case2_ys = ELIM_EX(pred_u_for_w, sub_B_hyp, _from_w0_witness)
        # th_case2_ys : {sub_B_hyp, witness} |- ?u. x = SUC y + u  (= case2_ys)
        sub_B = DISJ2(case1_ys, DISJ1(th_case2_ys, case3_ys))      # body_ys
        branch_B = DISCH(sub_B_hyp, sub_B)

        # Combine sub-cases via DISJ_CASES on LEMMA_PRED for w.
        return DISJ_CASES(from_lemma_pred, branch_A, branch_B)
    th_body_ys = ELIM_EX(pred_u_2, case2_y, _from_witness)
    return DISCH(case2_y, th_body_ys)


def _satz9_step_case3(x_t, y_t, body_ys, case1_ys, case2_ys, case3_ys, rest_ys):
    # Hypothesis: ?v. y = x + v.   At y' we get y' = (x + v)' = x + v', so case3_ys.
    case3_y = mk_exists(v, mk_eq(y_t, mk_add(x_t, v)))
    pred_v_3 = mk_abs(v, mk_eq(y_t, mk_add(x_t, v)))

    def _from_witness(witness_eq):
        # witness_eq : {y = x + w} |- y = x + w.
        _, rhs = dest_eq(witness_eq._concl)
        w_t = rand(rhs)        # = w
        # SUC y = SUC(x + w) = x + SUC w.
        th_succ = AP_TERM(SUC, witness_eq)                         # |- SUC y = SUC(x + w)
        th_split = SYM(SPEC(w_t, SPEC(x_t, ADD_SUC)))              # |- SUC(x+w) = x + SUC w
        th_sy = TRANS(th_succ, th_split)                           # |- SUC y = x + SUC w
        pred_v_case3_ys = mk_abs(v, mk_eq(mk_suc(y_t), mk_add(x_t, v)))
        th_case3_ys = EXISTS(pred_v_case3_ys, mk_suc(w_t), th_sy)  # ?v. SUC y = x + v
        return DISJ2(case1_ys, DISJ2(case2_ys, th_case3_ys))       # body_ys

    th_body_ys = ELIM_EX(pred_v_3, case3_y, _from_witness)
    return DISCH(case3_y, th_body_ys)


SATZ_9 = _prove_satz_9_exist()


# ---------------------------------------------------------------------------
# #3 -- Ordnung
# ---------------------------------------------------------------------------

# Definition 2:  x > y  ≡  ?u. x = y + u
# Definition 3:  x < y  ≡  ?v. y = x + v
# ---------------------------------------------------------------------------

_nnb = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))

GT_DEF = new_basic_definition(
    mk_eq(Var(">", _nnb),
          mk_abs(x, mk_abs(y, mk_exists(u, mk_eq(x, mk_add(y, u)))))))

LT_DEF = new_basic_definition(
    mk_eq(Var("<", _nnb),
          mk_abs(x, mk_abs(y, mk_exists(v, mk_eq(y, mk_add(x, v)))))))

GT = mk_const(">", [])
LT = mk_const("<", [])
_INFIX.add(">"); _INFIX.add("<")

def mk_gt(a, b): return mk_comb(mk_comb(GT, a), b)
def mk_lt(a, b): return mk_comb(mk_comb(LT, a), b)

def _binop_unfold(def_th, op_const, a, b):
    """ |- (op a b) = (\\x y. body) a b   -- delivers the beta-reduced equality. """
    eq1 = AP_THM(def_th, a)
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))
    eq3 = AP_THM(eq2, b)
    return TRANS(eq3, BETA_CONV(rand(eq3._concl)))

def UNFOLD_GT(a, b):
    """ |- (a > b) = (?u. a = b + u) """
    return _binop_unfold(GT_DEF, GT, a, b)

def UNFOLD_LT(a, b):
    """ |- (a < b) = (?v. b = a + v) """
    return _binop_unfold(LT_DEF, LT, a, b)


# Theorem 10:  |- !x y. (x = y) \/ (x > y) \/ (x < y).    By Theorem 9 + Definitions 2, 3.

def _prove_satz_10():
    body9 = _build_satz9_body(x, y)
    th9 = SPEC(y, SPEC(x, SATZ_9))             # |- body9
    case2 = mk_exists(u, mk_eq(x, mk_add(y, u)))
    case3 = mk_exists(v, mk_eq(y, mk_add(x, v)))
    # Rewrite case2 -> (x > y), case3 -> (x < y).
    eq_gt = SYM(UNFOLD_GT(x, y))               # |- ?u. x = y + u   = (x > y)
    eq_lt = SYM(UNFOLD_LT(x, y))               # |- ?v. y = x + v   = (x < y)
    # body9 = (x=y) \/ (case2 \/ case3); rewrite to (x=y) \/ (x>y \/ x<y).
    inner_eq = MK_COMB(AP_TERM(mk_const("\\/", []), eq_gt), eq_lt)
    # |- (case2 \/ case3) = (x > y \/ x < y)
    outer_eq = AP_TERM(mk_comb(mk_const("\\/", []), mk_eq(x, y)), inner_eq)
    return GEN(x, GEN(y, EQ_MP(outer_eq, th9)))

SATZ_10 = _prove_satz_10()


# Theorem 11:  |- !x y. (x > y) ==> (y < x).   Both sides unfold to ?u. x = y + u.
# Theorem 12:  |- !x y. (x < y) ==> (y > x).   Symmetric.

def _prove_satz_11():
    th_assume = ASSUME(mk_gt(x, y))                      # {x > y} |- x > y
    th_unfold = EQ_MP(UNFOLD_GT(x, y), th_assume)        # {x > y} |- ?u. x = y + u
    # ?u. x = y + u  =  ?v. x = y + v  (alpha-equiv).  But UNFOLD_LT(y, x) gives ?v. x = y + v.
    th_lt = EQ_MP(SYM(UNFOLD_LT(y, x)), th_unfold)       # {x > y} |- y < x
    return GEN(x, GEN(y, DISCH(mk_gt(x, y), th_lt)))

SATZ_11 = _prove_satz_11()

def _prove_satz_12():
    th_assume = ASSUME(mk_lt(x, y))
    th_unfold = EQ_MP(UNFOLD_LT(x, y), th_assume)        # {x < y} |- ?v. y = x + v
    th_gt = EQ_MP(SYM(UNFOLD_GT(y, x)), th_unfold)       # {x < y} |- y > x
    return GEN(x, GEN(y, DISCH(mk_lt(x, y), th_gt)))

SATZ_12 = _prove_satz_12()


# Definition 4:  x >= y  ≡  x > y \/ x = y.
# Definition 5:  x <= y  ≡  x < y \/ x = y.

GE_DEF = new_basic_definition(
    mk_eq(Var(">=", _nnb),
          mk_abs(x, mk_abs(y, mk_or(mk_gt(x, y), mk_eq(x, y))))))
LE_DEF = new_basic_definition(
    mk_eq(Var("<=", _nnb),
          mk_abs(x, mk_abs(y, mk_or(mk_lt(x, y), mk_eq(x, y))))))

GE = mk_const(">=", []); LE = mk_const("<=", [])
_INFIX.add(">="); _INFIX.add("<=")

def mk_ge(a, b): return mk_comb(mk_comb(GE, a), b)
def mk_le(a, b): return mk_comb(mk_comb(LE, a), b)

def UNFOLD_GE(a, b): return _binop_unfold(GE_DEF, GE, a, b)
def UNFOLD_LE(a, b): return _binop_unfold(LE_DEF, LE, a, b)


# Theorem 13:  |- !x y. (x >= y) ==> (y <= x).
# Theorem 14:  |- !x y. (x <= y) ==> (y >= x).

def _prove_satz_13():
    th_assume = ASSUME(mk_ge(x, y))
    th_unfold = EQ_MP(UNFOLD_GE(x, y), th_assume)            # {x>=y} |- (x>y) \/ (x=y)
    # Map (x > y) to (y < x) via Theorem 11; (x = y) to (y = x) via SYM.
    s11_xy = SPEC(y, SPEC(x, SATZ_11))                       # |- (x > y) ==> (y < x)
    branch_gt = DISCH(mk_gt(x, y),
                      DISJ1(MP(s11_xy, ASSUME(mk_gt(x, y))),
                            mk_eq(y, x)))
    branch_eq = DISCH(mk_eq(x, y),
                      DISJ2(mk_lt(y, x),
                            SYM(ASSUME(mk_eq(x, y)))))
    th_disj = DISJ_CASES(th_unfold, branch_gt, branch_eq)    # {x>=y} |- (y<x) \/ (y=x)
    th_le = EQ_MP(SYM(UNFOLD_LE(y, x)), th_disj)
    return GEN(x, GEN(y, DISCH(mk_ge(x, y), th_le)))

SATZ_13 = _prove_satz_13()

def _prove_satz_14():
    th_assume = ASSUME(mk_le(x, y))
    th_unfold = EQ_MP(UNFOLD_LE(x, y), th_assume)            # {x<=y} |- (x<y) \/ (x=y)
    s12_xy = SPEC(y, SPEC(x, SATZ_12))                       # |- (x < y) ==> (y > x)
    branch_lt = DISCH(mk_lt(x, y),
                      DISJ1(MP(s12_xy, ASSUME(mk_lt(x, y))),
                            mk_eq(y, x)))
    branch_eq = DISCH(mk_eq(x, y),
                      DISJ2(mk_gt(y, x),
                            SYM(ASSUME(mk_eq(x, y)))))
    th_disj = DISJ_CASES(th_unfold, branch_lt, branch_eq)
    th_ge = EQ_MP(SYM(UNFOLD_GE(y, x)), th_disj)
    return GEN(x, GEN(y, DISCH(mk_le(x, y), th_ge)))

SATZ_14 = _prove_satz_14()


# Theorem 15 (transitivity of order):  |- !x y z. x < y ==> y < z ==> x < z.

def _prove_satz_15():
    pred_v_def = mk_abs(v, mk_eq(y, mk_add(x, v)))
    pred_w_def = mk_abs(w, mk_eq(z, mk_add(y, w)))
    ex_v = EQ_MP(UNFOLD_LT(x, y), ASSUME(mk_lt(x, y)))     # {x<y} |- ?v. y = x + v
    ex_w = EQ_MP(UNFOLD_LT(y, z), ASSUME(mk_lt(y, z)))     # {y<z} |- ?w. z = y + w

    def _from_v(eq_y):
        _, rhs_y = dest_eq(eq_y._concl)
        v0 = rand(rhs_y)
        def _from_w(eq_z):
            _, rhs_z = dest_eq(eq_z._concl)
            w0 = rand(rhs_z)
            sub_y = AP_THM(AP_TERM(PLUS, eq_y), w0)            # |- y + w0 = (x+v0) + w0
            z_eq1 = TRANS(eq_z, sub_y)                         # |- z = (x+v0) + w0
            assoc = SPEC(w0, SPEC(v0, SPEC(x, SATZ_5)))        # |- (x+v0)+w0 = x+(v0+w0)
            z_eq2 = TRANS(z_eq1, assoc)                        # |- z = x + (v0+w0)
            pred_final = mk_abs(v, mk_eq(z, mk_add(x, v)))
            return EXISTS(pred_final, mk_add(v0, w0), z_eq2)
        return ELIM_EX(pred_w_def, ex_w._concl, _from_w)
    th_chain1 = ELIM_EX(pred_v_def, ex_v._concl, _from_v)
    # th_chain1 : {ex_v._concl, ex_w._concl} |- ?v. z = x + v
    th_chain2 = PROVE_HYP(ex_v, PROVE_HYP(ex_w, th_chain1))    # {x<y, y<z} |- ?v. z = x + v
    th_lt = EQ_MP(SYM(UNFOLD_LT(x, z)), th_chain2)             # {x<y, y<z} |- x < z
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_lt(x, y), DISCH(mk_lt(y, z), th_lt)))))

SATZ_15 = _prove_satz_15()


# Helpers turning < / = into <= and the analogues, used pervasively in #3.

def LT_TO_LE(th_lt):
    a = rand(rator(th_lt._concl)); b = rand(th_lt._concl)
    return EQ_MP(SYM(UNFOLD_LE(a, b)), DISJ1(th_lt, mk_eq(a, b)))

def EQ_TO_LE(th_eq):
    a, b = dest_eq(th_eq._concl)
    return EQ_MP(SYM(UNFOLD_LE(a, b)), DISJ2(mk_lt(a, b), th_eq))

def GT_TO_GE(th_gt):
    a = rand(rator(th_gt._concl)); b = rand(th_gt._concl)
    return EQ_MP(SYM(UNFOLD_GE(a, b)), DISJ1(th_gt, mk_eq(a, b)))

def EQ_TO_GE(th_eq):
    a, b = dest_eq(th_eq._concl)
    return EQ_MP(SYM(UNFOLD_GE(a, b)), DISJ2(mk_gt(a, b), th_eq))


# Theorem 16:   x <= y, y < z  =>  x < z   ;   x < y, y <= z  =>  x < z.
# We prove both forms (Landau's "or" is a disjunctive hypothesis).

def _prove_satz_16a():
    """ x <= y, y < z ==> x < z """
    h_le = ASSUME(mk_le(x, y))
    h_lt = ASSUME(mk_lt(y, z))
    u = EQ_MP(UNFOLD_LE(x, y), h_le)                                  # (x<y) \/ (x=y)
    branch_lt = DISCH(mk_lt(x, y),
                      MP(MP(SPEC(z, SPEC(y, SPEC(x, SATZ_15))),
                            ASSUME(mk_lt(x, y))), h_lt))
    eq_xy = ASSUME(mk_eq(x, y))
    rewrite = AP_THM(AP_TERM(LT, SYM(eq_xy)), z)                      # {x=y} |- (y<z) = (x<z)
    branch_eq = DISCH(mk_eq(x, y), EQ_MP(rewrite, h_lt))
    th_xz = DISJ_CASES(u, branch_lt, branch_eq)
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_le(x, y), DISCH(mk_lt(y, z), th_xz)))))

def _prove_satz_16b():
    """ x < y, y <= z ==> x < z """
    h_lt = ASSUME(mk_lt(x, y))
    h_le = ASSUME(mk_le(y, z))
    u = EQ_MP(UNFOLD_LE(y, z), h_le)
    branch_lt = DISCH(mk_lt(y, z),
                      MP(MP(SPEC(z, SPEC(y, SPEC(x, SATZ_15))), h_lt),
                         ASSUME(mk_lt(y, z))))
    eq_yz = ASSUME(mk_eq(y, z))
    rewrite = MK_COMB(REFL(mk_comb(LT, x)), eq_yz)         # {y=z} |- (x<y) = (x<z)
    branch_eq = DISCH(mk_eq(y, z), EQ_MP(rewrite, h_lt))
    th_xz = DISJ_CASES(u, branch_lt, branch_eq)
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_lt(x, y), DISCH(mk_le(y, z), th_xz)))))

SATZ_16A = _prove_satz_16a()
SATZ_16B = _prove_satz_16b()


# Theorem 17:   x <= y, y <= z  =>  x <= z.

def _prove_satz_17():
    h_xy = ASSUME(mk_le(x, y))
    h_yz = ASSUME(mk_le(y, z))
    s16a = SPEC(z, SPEC(y, SPEC(x, SATZ_16A)))         # |- x<=y ==> y<z ==> x<z
    u = EQ_MP(UNFOLD_LE(y, z), h_yz)                   # (y<z) \/ (y=z)
    # Case y < z:  use Theorem 16A.
    branch_lt = DISCH(mk_lt(y, z),
                      LT_TO_LE(MP(MP(s16a, h_xy), ASSUME(mk_lt(y, z)))))
    # Case y = z:  rewrite x<=y to x<=z.
    eq_yz = ASSUME(mk_eq(y, z))
    rewrite = MK_COMB(REFL(mk_comb(LE, x)), eq_yz)     # {y=z} |- (x<=y) = (x<=z)
    branch_eq = DISCH(mk_eq(y, z), EQ_MP(rewrite, h_xy))
    th_xz = DISJ_CASES(u, branch_lt, branch_eq)
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_le(x, y), DISCH(mk_le(y, z), th_xz)))))

SATZ_17 = _prove_satz_17()


# Theorem 18:  |- !x y. x + y > x.    Witness y in ?u. x+y = x+u.

def _prove_satz_18():
    pred_u = mk_abs(u, mk_eq(mk_add(x, y), mk_add(x, u)))
    th_ex = EXISTS(pred_u, y, REFL(mk_add(x, y)))
    th_gt = EQ_MP(SYM(UNFOLD_GT(mk_add(x, y), x)), th_ex)
    return GEN(x, GEN(y, th_gt))

SATZ_18 = _prove_satz_18()


# Theorem 19 (in three pieces -- Landau states it via "respectively"):
#   19a:  x > y      ==>  x + z > y + z
#   19b:  x = y      ==>  x + z = y + z
#   19c:  x < y      ==>  x + z < y + z

def _prove_satz_19a():
    h = ASSUME(mk_gt(x, y))
    ex_u = EQ_MP(UNFOLD_GT(x, y), h)                        # ?u. x = y + u
    pred_u = mk_abs(u, mk_eq(x, mk_add(y, u)))
    def _from(eq_x):
        u0 = rand(rand(eq_x._concl))
        # x + z = (y + u0) + z = y + (u0 + z) = y + (z + u0) = (y + z) + u0
        step1 = AP_THM(AP_TERM(PLUS, eq_x), z)               # |- x+z = (y+u0)+z
        step2 = SPEC(z, SPEC(u0, SPEC(y, SATZ_5)))           # |- (y+u0)+z = y+(u0+z)
        step3 = AP_TERM(mk_comb(PLUS, y), SPEC(z, SPEC(u0, SATZ_6)))   # |- y+(u0+z) = y+(z+u0)
        step4 = SYM(SPEC(u0, SPEC(z, SPEC(y, SATZ_5))))      # |- y+(z+u0) = (y+z)+u0
        path  = TRANS(step1, TRANS(step2, TRANS(step3, step4)))
        pred_final = mk_abs(u, mk_eq(mk_add(x, z), mk_add(mk_add(y, z), u)))
        return EXISTS(pred_final, u0, path)
    th_inner = ELIM_EX(pred_u, ex_u._concl, _from)
    th_full  = PROVE_HYP(ex_u, th_inner)
    th_gt = EQ_MP(SYM(UNFOLD_GT(mk_add(x, z), mk_add(y, z))), th_full)
    return GEN(x, GEN(y, GEN(z, DISCH(mk_gt(x, y), th_gt))))

SATZ_19A = _prove_satz_19a()

def _prove_satz_19b():
    h = ASSUME(mk_eq(x, y))
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_eq(x, y), AP_THM(AP_TERM(PLUS, h), z)))))

SATZ_19B = _prove_satz_19b()

def _prove_satz_19c():
    # By Theorem 12, x < y => y > x.  Then Theorem 19a: y + z > x + z.  Then Theorem 11: x + z < y + z.
    h = ASSUME(mk_lt(x, y))
    th_yx_gt = MP(SPEC(y, SPEC(x, SATZ_12)), h)                # {x<y} |- y > x
    s19a = SPEC(z, SPEC(x, SPEC(y, SATZ_19A)))                  # |- y > x ==> y+z > x+z
    th_yz_gt_xz = MP(s19a, th_yx_gt)                            # {x<y} |- y+z > x+z
    th_lt = MP(SPEC(mk_add(x, z), SPEC(mk_add(y, z), SATZ_11)), th_yz_gt_xz)
    return GEN(x, GEN(y, GEN(z, DISCH(mk_lt(x, y), th_lt))))

SATZ_19C = _prove_satz_19c()


# Theorem 21:   x > y, z > u  ==>  x + z > y + u.
# Proof: x+z > y+z (Theorem 19a) and y+z > y+u (Theorem 19a w/ commutativity).

def _prove_satz_21():
    h_xy = ASSUME(mk_gt(x, y))
    h_zu = ASSUME(mk_gt(z, u))
    s19a_xy = MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19A))), h_xy)     # x+z > y+z
    s19a_zu = MP(SPEC(y, SPEC(u, SPEC(z, SATZ_19A))), h_zu)     # z+y > u+y
    # Convert  z + y > u + y   to   y + z > y + u   using commutativity (Theorem 6).
    comm_zy = SPEC(y, SPEC(z, SATZ_6))                          # |- z + y = y + z
    comm_uy = SPEC(y, SPEC(u, SATZ_6))                          # |- u + y = y + u
    rewrite = MK_COMB(AP_TERM(GT, comm_zy), comm_uy)            # |- (z+y > u+y) = (y+z > y+u)
    th_yz_gt_yu = EQ_MP(rewrite, s19a_zu)                       # y+z > y+u
    # Convert > to <, chain via Theorem 15, then back to >.
    th_yu_lt_yz = MP(SPEC(mk_add(y, u), SPEC(mk_add(y, z), SATZ_11)), th_yz_gt_yu)
    th_yz_lt_xz = MP(SPEC(mk_add(y, z), SPEC(mk_add(x, z), SATZ_11)), s19a_xy)
    s15 = SPEC(mk_add(x, z), SPEC(mk_add(y, z), SPEC(mk_add(y, u), SATZ_15)))
    th_lt = MP(MP(s15, th_yu_lt_yz), th_yz_lt_xz)               # y+u < x+z
    th_gt = MP(SPEC(mk_add(x, z), SPEC(mk_add(y, u), SATZ_12)), th_lt)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_gt(x, y), DISCH(mk_gt(z, u), th_gt))))))

SATZ_21 = _prove_satz_21()


# Theorem 22:   x >= y, z > u  ==>  x + z > y + u   (and the other "or" form).

def _prove_satz_22a():
    h_ge = ASSUME(mk_ge(x, y))
    h_gt = ASSUME(mk_gt(z, u))
    u_ge = EQ_MP(UNFOLD_GE(x, y), h_ge)                         # (x>y) \/ (x=y)
    s21 = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_21))))           # |- x>y ==> z>u ==> x+z > y+u
    branch_gt = DISCH(mk_gt(x, y), MP(MP(s21, ASSUME(mk_gt(x, y))), h_gt))
    # Branch x = y: x+z > y+u becomes y+z > y+u, follow from z>u via Theorem 19a + comm.
    eq_xy = ASSUME(mk_eq(x, y))
    s19a_zu = MP(SPEC(y, SPEC(u, SPEC(z, SATZ_19A))), h_gt)     # z+y > u+y
    comm_zy = SPEC(y, SPEC(z, SATZ_6))
    comm_uy = SPEC(y, SPEC(u, SATZ_6))
    th_yzgt = EQ_MP(MK_COMB(AP_TERM(GT, comm_zy), comm_uy), s19a_zu)   # y+z > y+u
    # rewrite y+z to x+z using SYM eq_xy:
    rewrite = MK_COMB(AP_TERM(GT,
                              AP_THM(AP_TERM(PLUS, SYM(eq_xy)), z)),
                      AP_THM(AP_TERM(PLUS, SYM(eq_xy)), u))     # |- (y+z > y+u) = (x+z > x+u)?
    # wait we want y -> x but on the y side. Hmm let me redo.
    # We want x+z > y+u.  We have y+z > y+u.  Need to show y+z = x+z (using y = x ↔ x = y SYM).
    # Specifically: SYM(eq_xy) gives y = x.  AP_TERM(PLUS, |- y = x): |- (PLUS y) = (PLUS x).
    # AP_THM with z: |- y+z = x+z.
    # Then MK_COMB(AP_TERM(GT, |- y+z = x+z), REFL(y+u)): |- (y+z > y+u) = (x+z > y+u).
    yz_eq_xz = AP_THM(AP_TERM(PLUS, SYM(eq_xy)), z)             # |- y+z = x+z
    rewrite = MK_COMB(AP_TERM(GT, yz_eq_xz), REFL(mk_add(y, u))) # |- (y+z > y+u) = (x+z > y+u)
    branch_eq = DISCH(mk_eq(x, y), EQ_MP(rewrite, th_yzgt))
    th_xzgt = DISJ_CASES(u_ge, branch_gt, branch_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_ge(x, y), DISCH(mk_gt(z, u), th_xzgt))))))

SATZ_22A = _prove_satz_22a()

# Theorem 22 second form: x > y, z >= u ==> x + z > y + u. By symmetric argument.
def _prove_satz_22b():
    h_gt = ASSUME(mk_gt(x, y))
    h_ge = ASSUME(mk_ge(z, u))
    u_ge = EQ_MP(UNFOLD_GE(z, u), h_ge)                         # (z>u) \/ (z=u)
    s21 = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_21))))
    branch_gt = DISCH(mk_gt(z, u), MP(MP(s21, h_gt), ASSUME(mk_gt(z, u))))
    eq_zu = ASSUME(mk_eq(z, u))
    s19a_xy = MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19A))), h_gt)     # x+z > y+z
    yz_eq_yu = AP_TERM(mk_comb(PLUS, y), eq_zu)                 # |- y+z = y+u
    rewrite = MK_COMB(AP_TERM(GT, REFL(mk_add(x, z))), yz_eq_yu)
    branch_eq = DISCH(mk_eq(z, u), EQ_MP(rewrite, s19a_xy))
    th = DISJ_CASES(u_ge, branch_gt, branch_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_gt(x, y), DISCH(mk_ge(z, u), th))))))

SATZ_22B = _prove_satz_22b()


# Theorem 23:   x >= y, z >= u  ==>  x + z >= y + u.

def _prove_satz_23():
    h_xy = ASSUME(mk_ge(x, y))
    h_zu = ASSUME(mk_ge(z, u))
    ux  = EQ_MP(UNFOLD_GE(x, y), h_xy)                          # (x>y) \/ (x=y)
    uz  = EQ_MP(UNFOLD_GE(z, u), h_zu)                          # (z>u) \/ (z=u)
    s22a = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_22A))))
    s22b = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_22B))))
    # Case x>y or z>u: get strict, lift to >=.
    branch_x_gt = DISCH(mk_gt(x, y),
                        GT_TO_GE(MP(MP(s22b, ASSUME(mk_gt(x, y))), h_zu)))
    # Case x=y: case-split on z.
    eq_xy = ASSUME(mk_eq(x, y))
    branch_z_gt = DISCH(mk_gt(z, u),
                        GT_TO_GE(MP(MP(s22a, h_xy), ASSUME(mk_gt(z, u)))))
    # x=y, z=u  =>  x+z = y+u  (apply both equalities) → >= via EQ_TO_GE.
    eq_zu = ASSUME(mk_eq(z, u))
    eq_sum = MK_COMB(AP_TERM(PLUS, eq_xy), eq_zu)               # |- x+z = y+u
    branch_z_eq = DISCH(mk_eq(z, u), EQ_TO_GE(eq_sum))
    branch_x_eq = DISCH(mk_eq(x, y), DISJ_CASES(uz, branch_z_gt, branch_z_eq))
    th = DISJ_CASES(ux, branch_x_gt, branch_x_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_ge(x, y), DISCH(mk_ge(z, u), th))))))

SATZ_23 = _prove_satz_23()


# Theorem 24:  |- !x. x >= 1.    Either x = 1 or x = u' = u + 1 > 1.

def _prove_satz_24():
    lp = SPEC(x, LEMMA_PRED)                                    # |- (x = 1) \/ ?u. x = u'
    # Branch x = 1: x >= 1 via EQ_TO_GE.
    branch1 = DISCH(mk_eq(x, ONE), EQ_TO_GE(ASSUME(mk_eq(x, ONE))))
    # Branch ?u. x = u': witness w with x = w' = w + 1 = 1 + w (commutativity).  Then x > 1.
    pred_u = mk_abs(u, mk_eq(x, mk_suc(u)))
    hyp_ex = mk_exists(u, mk_eq(x, mk_suc(u)))
    def _from(eq_x):     # {x = w'} |- x = w'
        w = rand(rand(eq_x._concl))
        x_eq_w1  = TRANS(eq_x, SYM(SPEC(w, ADD_1)))                 # |- x = w + 1
        x_eq_1w  = TRANS(x_eq_w1, SYM(SPEC(w, SPEC(ONE, SATZ_6))))  # |- x = 1 + w
        pred_gt = mk_abs(u, mk_eq(x, mk_add(ONE, u)))
        th_gt = EQ_MP(SYM(UNFOLD_GT(x, ONE)), EXISTS(pred_gt, w, x_eq_1w))
        return GT_TO_GE(th_gt)
    branch2 = DISCH(hyp_ex, ELIM_EX(pred_u, hyp_ex, _from))
    return GEN(x, DISJ_CASES(lp, branch1, branch2))

SATZ_24 = _prove_satz_24()


# Theorem 25:   y > x  ==>  y >= x + 1.
# Proof: y = x + u, u >= 1, so y = x + u >= x + 1 (Theorem 23).

def _prove_satz_25():
    h = ASSUME(mk_gt(y, x))
    ex_u = EQ_MP(UNFOLD_GT(y, x), h)                            # ?u. y = x + u
    pred_u = mk_abs(u, mk_eq(y, mk_add(x, u)))
    def _from(eq_y):
        u0 = rand(rand(eq_y._concl))
        # u0 >= 1
        u_ge_1 = SPEC(u0, SATZ_24)                              # |- u0 >= 1
        # x + u0 >= x + 1 by Theorem 23 with REFL(x).
        s23 = SPEC(ONE, SPEC(u0, SPEC(x, SPEC(x, SATZ_23))))    # |- x>=x ==> u0>=1 ==> x+u0 >= x+1
        x_ge_x = EQ_TO_GE(REFL(x))
        sum_ge = MP(MP(s23, x_ge_x), u_ge_1)                    # |- x+u0 >= x+1
        # y = x + u0, so y >= x + 1.
        rewrite = MK_COMB(AP_TERM(GE, SYM(eq_y)), REFL(mk_add(x, ONE)))
        # |- (x+u0 >= x+1) = (y >= x+1)
        return EQ_MP(rewrite, sum_ge)
    th_inner = ELIM_EX(pred_u, ex_u._concl, _from)
    th_full = PROVE_HYP(ex_u, th_inner)                         # {y>x} |- y >= x+1
    return GEN(x, GEN(y, DISCH(mk_gt(y, x), th_full)))

SATZ_25 = _prove_satz_25()


# Theorem 26:   y < x + 1  ==>  y <= x.    Contrapositive of Theorem 25.
# Landau: "Otherwise we'd have y > x, hence by Theorem 25 y >= x + 1."
# We prove it via Theorem 9 (trichotomy): if y > x, then y >= x + 1, contradicting y < x + 1.
# Otherwise y = x or y < x, both giving y <= x.

def _prove_satz_26():
    h = ASSUME(mk_lt(y, mk_add(x, ONE)))
    s10 = SPEC(x, SPEC(y, SATZ_10))                             # (y=x) \/ (y>x \/ y<x)
    # Branch y = x  =>  y <= x.
    branch_eq = DISCH(mk_eq(y, x), EQ_TO_LE(ASSUME(mk_eq(y, x))))
    # Branch y > x  =>  contradiction with h.
    eq_yx_gt = ASSUME(mk_gt(y, x))
    s25_yx = MP(SPEC(y, SPEC(x, SATZ_25)), eq_yx_gt)            # {y>x} |- y >= x+1
    # y >= x+1  is  y > x+1 \/ y = x+1.   Combined with y < x+1: contradiction.
    u_ge = EQ_MP(UNFOLD_GE(y, mk_add(x, ONE)), s25_yx)          # (y > x+1) \/ (y = x+1)
    # Branch y > x + 1: contradict y < x + 1 via SATZ_7 substitute.
    # Easiest: use Theorem 9 again -- but that's circular.  Use Theorem 7 directly:
    # y > x+1  means ?u. y = (x+1) + u.   y < x+1 means ?v. x+1 = y + v.
    # Combining: x+1 = y + v = ((x+1) + u) + v = (x+1) + (u + v), so x+1 = (x+1) + (u+v), ⊥ via Theorem 7.
    branch_gt = DISCH(mk_gt(y, mk_add(x, ONE)),
                      CONTR(mk_le(y, x),
                            CONTRA_LT_GT(y, mk_add(x, ONE), h, ASSUME(mk_gt(y, mk_add(x, ONE))))))
    # Branch y = x + 1: contradicts y < x + 1 (via Theorem 7).
    branch_eq2 = DISCH(mk_eq(y, mk_add(x, ONE)),
                       CONTR(mk_le(y, x),
                             CONTRA_LT_EQ(y, mk_add(x, ONE), h, ASSUME(mk_eq(y, mk_add(x, ONE))))))
    branch_gtcase = DISCH(mk_gt(y, x), DISJ_CASES(u_ge, branch_gt, branch_eq2))
    # Branch y < x: y < x  =>  y <= x via DISJ1.
    branch_lt = DISCH(mk_lt(y, x), LT_TO_LE(ASSUME(mk_lt(y, x))))
    # Combine y > x \/ y < x cases.
    inner = DISCH(mk_or(mk_gt(y, x), mk_lt(y, x)),
                  DISJ_CASES(ASSUME(mk_or(mk_gt(y, x), mk_lt(y, x))),
                             branch_gtcase, branch_lt))
    th = DISJ_CASES(s10, branch_eq, inner)
    return GEN(x, GEN(y, DISCH(mk_lt(y, mk_add(x, ONE)), th)))


def CONTRA_LT_GT(a_t, b_t, h_lt, h_gt):
    """ |- a < b,  |- a > b   =>   {a<b, a>b} |- F.   (Mutual exclusion of < and >.)
        a < b unfolds to ?v. b = a + v;  a > b unfolds to ?u. a = b + u.
        Combined: b = a + v = (b + u) + v = b + (u + v), contradicts Theorem 7. """
    ex_v = EQ_MP(UNFOLD_LT(a_t, b_t), h_lt)
    ex_u = EQ_MP(UNFOLD_GT(a_t, b_t), h_gt)
    pred_v = mk_abs(v, mk_eq(b_t, mk_add(a_t, v)))
    pred_u = mk_abs(u, mk_eq(a_t, mk_add(b_t, u)))
    def _inner_v(eq_v):
        v0 = rand(rand(eq_v._concl))
        def _inner_u(eq_u):
            u0 = rand(rand(eq_u._concl))
            sub_a = AP_THM(AP_TERM(PLUS, eq_u), v0)              # |- a + v0 = (b+u0) + v0
            assoc = SPEC(v0, SPEC(u0, SPEC(b_t, SATZ_5)))        # |- (b+u0)+v0 = b+(u0+v0)
            chain = TRANS(eq_v, TRANS(sub_a, assoc))             # |- b = b + (u0+v0)
            comm  = SPEC(b_t, SPEC(mk_add(u0, v0), SATZ_6))      # |- (u0+v0)+b = b+(u0+v0)
            ne    = SPEC(b_t, SPEC(mk_add(u0, v0), SATZ_7))      # |- ~(b = (u0+v0)+b)
            ne_f  = REWRITE_NE(ne, REFL(b_t), comm)              # |- ~(b = b+(u0+v0))
            return MP(NOT_ELIM(ne_f), chain)                     # |- F
        return ELIM_EX(pred_u, ex_u._concl, _inner_u)
    th = ELIM_EX(pred_v, ex_v._concl, _inner_v)
    return PROVE_HYP(ex_v, PROVE_HYP(ex_u, th))


def CONTRA_LT_EQ(a_t, b_t, h_lt, h_eq):
    """ |- a < b,  |- a = b   =>   F.   Sub a=b into a<b gives b<b, contradicting Theorem 7. """
    rewrite = MK_COMB(AP_TERM(LT, h_eq), REFL(b_t))              # |- (a<b) = (b<b)
    th_bb = EQ_MP(rewrite, h_lt)                                 # |- b < b
    ex_v = EQ_MP(UNFOLD_LT(b_t, b_t), th_bb)                     # ?v. b = b + v
    pred_v = mk_abs(v, mk_eq(b_t, mk_add(b_t, v)))
    def _inner(eq):
        v0   = rand(rand(eq._concl))
        comm = SPEC(b_t, SPEC(v0, SATZ_6))                       # |- v0+b = b+v0
        ne   = SPEC(b_t, SPEC(v0, SATZ_7))                       # |- ~(b = v0+b)
        ne_f = REWRITE_NE(ne, REFL(b_t), comm)                   # |- ~(b = b+v0)
        return MP(NOT_ELIM(ne_f), eq)
    th = ELIM_EX(pred_v, ex_v._concl, _inner)
    return PROVE_HYP(ex_v, th)


def CONTRA_GT_EQ(a_t, b_t, h_gt, h_eq):
    """ |- a > b,  |- a = b   =>   F.   a > b means ?u. a = b + u; sub a = b gives b = b + u. """
    ex_u = EQ_MP(UNFOLD_GT(a_t, b_t), h_gt)
    pred_u = mk_abs(u, mk_eq(a_t, mk_add(b_t, u)))
    def _inner(eq_a):
        u0    = rand(rand(eq_a._concl))
        chain = TRANS(SYM(h_eq), eq_a)                            # |- b = b + u0
        comm  = SPEC(b_t, SPEC(u0, SATZ_6))
        ne    = SPEC(b_t, SPEC(u0, SATZ_7))
        ne_f  = REWRITE_NE(ne, REFL(b_t), comm)
        return MP(NOT_ELIM(ne_f), chain)
    th = ELIM_EX(pred_u, ex_u._concl, _inner)
    return PROVE_HYP(ex_u, th)


SATZ_26 = _prove_satz_26()


# ---------------------------------------------------------------------------
# Theorem 27 (well-ordering).
#   |- !N. (?n. N n) ==> ?m. N m /\ (!k. N k ==> m <= k).
#
# Proof (Landau): let M(x) := !n. N n ==> x <= n.  Then 1 ∈ M (Theorem 24).
# For y ∈ N, y+1 ∉ M (since y+1 > y by Theorem 18).  Hence not every x ∈ M;
# so by Axiom 5 there is some m ∈ M with m+1 ∉ M.  Such m is ≤ every n ∈ N
# (since m ∈ M); and m ∈ N (else m < n for all n ∈ N, hence m+1 ≤ n by
# Theorem 25, hence m+1 ∈ M).  Both clauses of the conclusion follow.
# ---------------------------------------------------------------------------

def _prove_satz_27():
    N_var = Var("N", mk_fun_ty(num_ty, bool_ty))
    n_var = Var("n", num_ty)
    k_var = Var("k", num_ty)
    m_var = Var("m", num_ty)

    hyp_nonempty = mk_exists(n_var, mk_comb(N_var, n_var))
    M_body_x = mk_forall(n_var, mk_imp(mk_comb(N_var, n_var), mk_le(x, n_var)))
    M_pred = mk_abs(x, M_body_x)

    def M_at(t):
        return mk_comb(M_pred, t)

    conclusion = mk_exists(m_var,
                           mk_and(mk_comb(N_var, m_var),
                                   mk_forall(k_var,
                                             mk_imp(mk_comb(N_var, k_var),
                                                    mk_le(m_var, k_var)))))

    # === Step 1: M(1). ===
    s24_n = SPEC(n_var, SATZ_24)
    one_le_n = MP(SPEC(ONE, SPEC(n_var, SATZ_13)), s24_n)
    M1_inner = GEN(n_var, DISCH(mk_comb(N_var, n_var), one_le_n))
    M1 = EQ_MP(SYM(BETA_CONV(M_at(ONE))), M1_inner)

    # === Step 2: !y. N y ==> ~M(y+1). ===
    h_Ny = ASSUME(mk_comb(N_var, y))
    h_M_yp1 = ASSUME(M_at(mk_add(y, ONE)))
    M_unfolded = EQ_MP(BETA_CONV(M_at(mk_add(y, ONE))), h_M_yp1)
    spec_y = SPEC(y, M_unfolded)
    le_y1_y = MP(spec_y, h_Ny)
    s18_y1 = SPEC(ONE, SPEC(y, SATZ_18))
    le_unfold = EQ_MP(UNFOLD_LE(mk_add(y, ONE), y), le_y1_y)
    branch_lt = DISCH(mk_lt(mk_add(y, ONE), y),
                      CONTRA_LT_GT(mk_add(y, ONE), y,
                                   ASSUME(mk_lt(mk_add(y, ONE), y)), s18_y1))
    branch_eq = DISCH(mk_eq(mk_add(y, ONE), y),
                      CONTRA_GT_EQ(mk_add(y, ONE), y, s18_y1,
                                   ASSUME(mk_eq(mk_add(y, ONE), y))))
    th_F = DISJ_CASES(le_unfold, branch_lt, branch_eq)
    th_imp_F = DISCH(M_at(mk_add(y, ONE)), th_F)
    not_M_yp1 = NOT_INTRO(th_imp_F)
    Ny_imp_notM = DISCH(mk_comb(N_var, y), not_M_yp1)        # {} |- N y ==> ~M(y+1)

    # === Step 3: ?m. M(m) /\ ~M(m+1). ===
    Q_body = mk_and(M_at(x), mk_not(M_at(mk_add(x, ONE))))
    Q_pred = mk_abs(x, Q_body)
    target_3 = mk_exists(x, Q_body)
    not_target_3 = mk_not(target_3)

    # Under not_target_3, derive contradiction using non-emptiness of N.
    # First: !x. ~Q(x).
    forall_not_Q = NOT_EX_TO_FORALL_NOT(ASSUME(not_target_3), Q_pred)
    # Next: !x. M(x) ==> M(x+1).
    # Pick x.  Goal: M(x) ==> M(x+1).
    # From not_Q(x) = ~(M(x) /\ ~M(x+1)), and EM on M(x+1):
    #   if M(x+1): trivially M(x) ==> M(x+1).
    #   if ~M(x+1): then ~M(x) (else contradiction with not_Q(x)).  So M(x) ==> M(x+1) trivially.
    spec_not_Q = SPEC(x, forall_not_Q)
    not_Q_x_unfold_eq = BETA_CONV(mk_comb(Q_pred, x))     # |- Q_pred x = (M(x) /\ ~M(x+1))
    not_Q_x_term = mk_not(rand(not_Q_x_unfold_eq._concl))  # ~(M(x) /\ ~M(x+1))
    # Hmm spec_not_Q._concl is ~Q_pred(x) but after SPEC's beta it should be ~(M(x)/\~M(x+1)).
    # Let me rely on that.
    em_Mxp1 = SPEC(M_at(mk_add(x, ONE)), EXCLUDED_MIDDLE)   # |- M(x+1) \/ ~M(x+1)
    branch_M = DISCH(M_at(mk_add(x, ONE)),
                     DISCH(M_at(x), ASSUME(M_at(mk_add(x, ONE)))))
    # Sub-branch ~M(x+1): show M(x) ==> M(x+1).  Approach: show ~M(x), then M(x) ==> anything.
    h_notM_xp1 = ASSUME(mk_not(M_at(mk_add(x, ONE))))
    h_M_x = ASSUME(M_at(x))
    conj_x = CONJ(h_M_x, h_notM_xp1)            # {M(x), ~M(x+1)} |- M(x) /\ ~M(x+1)
    th_F_inner = MP(NOT_ELIM(spec_not_Q), conj_x)        # {..., ~target_3} |- F
    branch_NM_inner = CONTR(M_at(mk_add(x, ONE)), th_F_inner)   # {..., ~target_3} |- M(x+1)
    branch_NM = DISCH(mk_not(M_at(mk_add(x, ONE))),
                       DISCH(M_at(x), branch_NM_inner))
    M_imp_M_succ = DISJ_CASES(em_Mxp1, branch_M, branch_NM)
    forall_M_succ = GEN(x, M_imp_M_succ)                  # {~target_3} |- !x. M(x) ==> M(x+1)

    # Apply Axiom 5 to M_pred.
    ind_inst = SPEC(M_pred, INDUCTION)                    # |- (M_pred 1 /\ !x. M_pred x ==> M_pred x') ==> !x. M_pred x
    # Convert forall_M_succ to use M_pred form (currently written as M_at).
    # M_at(x) IS M_pred x = (\x. body) x — same as in INDUCT.
    # We need:  !x. M_pred x ==> M_pred x'.   M_at(x) = M_pred x already (literally same term).
    forall_step_pred = forall_M_succ                       # already in pred form: M(x) ==> M(x+1)
    # Build conjunction.
    conj_for_ind = CONJ(M1, forall_step_pred)              # {~target_3} |- M_pred 1 /\ !x. M_pred x ==> M_pred x'
    # Wait, the step in Axiom 5 uses x' = SUC x, not x+1.
    # M_at(x+1) versus M_pred (SUC x) — they differ by ADD_1.  Need to convert.
    # SUC x and x+1 are equal by ADD_1: |- !x. x + 1 = SUC x.  So SUC x = x + 1, and
    # M_at(SUC x) = M_at(x+1) as terms after substitution... but they are NOT syntactically equal.
    # We need to bridge.
    # Build !x. M_pred x ==> M_pred (SUC x)   from   !x. M_pred x ==> M_pred (x+1).
    # via AP_TERM(M_pred, ADD_1 spec): |- M_pred (x+1) = M_pred (SUC x).
    add_1_x = SPEC(x, ADD_1)                              # |- x + 1 = SUC x
    M_eq = AP_TERM(M_pred, add_1_x)                       # |- M_pred (x+1) = M_pred (SUC x)
    # Take spec of forall_step_pred at x: M_pred x ==> M_pred (x+1).
    spec_step = SPEC(x, forall_step_pred)
    # Convert RHS via M_eq.
    # spec_step : |- M_pred x ==> M_pred (x+1).  We want |- M_pred x ==> M_pred (SUC x).
    h_M_x2 = ASSUME(M_at(x))
    th_M_xp1 = MP(spec_step, h_M_x2)                       # {M(x)} |- M_pred (x+1)
    th_M_sx = EQ_MP(M_eq, th_M_xp1)                        # {M(x)} |- M_pred (SUC x)
    spec_step_suc = DISCH(M_at(x), th_M_sx)                # |- M_pred x ==> M_pred (SUC x)
    forall_step_suc = GEN(x, spec_step_suc)                # {~target_3} |- !x. M_pred x ==> M_pred (SUC x)
    conj_for_ind2 = CONJ(M1, forall_step_suc)
    forall_M_all = MP(ind_inst, conj_for_ind2)             # {~target_3} |- !x. M_pred x

    # Now derive contradiction with hyp_nonempty.
    # Pick n ∈ N (witness of hyp_nonempty), apply forall_M_all to n+1 to get M(n+1),
    # then by Step 2 (Ny_imp_notM specialised), ~M(n+1).
    n_pred = mk_abs(n_var, mk_comb(N_var, n_var))
    def _from_n(eq_Nn):     # eq_Nn : {N w} |- N w  for w = SELECT witness
        # Get witness w
        Nw = eq_Nn._concl
        # We don't know w from this — but ELIM_EX gives us the SELECT term.
        # Actually w = (@n. N n).  Let's derive from that.
        w_t = rand(eq_Nn._concl)
        # M(w+1) from forall_M_all (at w+1):
        spec_M = SPEC(mk_add(w_t, ONE), forall_M_all)         # |- M_pred (w+1)  (well, M_at(w+1))
        # ~M(w+1) from Ny_imp_notM (with y := w):
        ny_imp = INST([(w_t, y)], Ny_imp_notM)                 # |- N w ==> ~M(w+1)
        not_M_w1 = MP(ny_imp, eq_Nn)                           # |- ~M(w+1)
        return MP(NOT_ELIM(not_M_w1), spec_M)                  # |- F
    th_F_step3 = ELIM_EX(n_pred, hyp_nonempty, _from_n)
    th_F_step3 = PROVE_HYP(ASSUME(hyp_nonempty), th_F_step3)
    # th_F_step3 : {~target_3, hyp_nonempty} |- F
    th_target3 = NOT_NOT_ELIM(NOT_INTRO(DISCH(not_target_3, th_F_step3)))
    # th_target3 : {hyp_nonempty} |- target_3   (= ?m. M(m) /\ ~M(m+1))

    # === Step 4: from m with M(m) /\ ~M(m+1), conclude m ∈ N and m ≤ k for all k ∈ N. ===
    def _from_m(eq_Q):
        # eq_Q : {Q_pred m_witness}  i.e., we have body[m_witness/x]  =  M(m) /\ ~M(m+1).
        # m_witness comes from BETA-form, which is m_witness term.
        # Actually the ELIM_EX body_fn receives ASSUME(body_at_w_outer) where body_at_w = body[w/x].
        # body of Q_pred = M(x) /\ ~M(x+1).  So body[w/x] = M(w) /\ ~M(w+1).
        m_t_w = rand(rator(eq_Q._concl).arg if False else eq_Q._concl)
        # Easier: we have eq_Q : {body[w/x]} |- body[w/x] = M(w) /\ ~M(w+1).  Extract w.
        # body[w/x] is Comb(/\, M(w), ~M(w+1)).  CONJUNCT1(eq_Q) gives M(w);
        # we extract w from M(w) = M_pred(w) = (\x. ...) w; rand gives w.
        Mm_w = CONJUNCT1(eq_Q)                                 # |- M(w)
        notM_w1 = CONJUNCT2(eq_Q)                              # |- ~M(w+1)
        w_t = rand(Mm_w._concl)                                # the m witness
        # Sub-claim a: !k. N k ==> w <= k.   (Direct from M(w).)
        Mm_unfold = EQ_MP(BETA_CONV(M_at(w_t)), Mm_w)          # |- !k. N k ==> w <= k
        sub_a = INST([(w_t, x)],
                     GEN(k_var, DISCH(mk_comb(N_var, k_var),
                                      INST([(k_var, n_var)],
                                           SPEC(k_var, Mm_unfold)))))
        # Hmm, simpler: just rename n_var to k_var in the conclusion:
        sub_a_alt = GEN(k_var,
                        DISCH(mk_comb(N_var, k_var),
                              MP(SPEC(k_var, Mm_unfold), ASSUME(mk_comb(N_var, k_var)))))
        # sub_a_alt : |- !k. N k ==> w <= k.
        # Sub-claim b: N w.   By contradiction.
        # Suppose ~N w.  Then for any n ∈ N, w != n (else N w via sub).
        # Combined with w <= n (from M(w)): w < n.
        # By Theorem 25: w < n ==> n >= w + 1.  So n >= w + 1 for all n ∈ N.
        # That means M(w+1) by definition.  But we have ~M(w+1).  ⊥.
        # So N w.
        h_not_Nw = ASSUME(mk_not(mk_comb(N_var, w_t)))
        # Build  !n. N n ==> w+1 <= n.
        # Pick n ∈ N.  Goal: w+1 <= n.
        h_Nn2 = ASSUME(mk_comb(N_var, n_var))
        # w <= n from M(w).
        w_le_n = MP(SPEC(n_var, Mm_unfold), h_Nn2)             # {N n} |- w <= n
        # w != n  (else N w from N n via substitution, contradicting ~N w).
        # By contradiction: assume w = n.  Substitute in N n: N w.  Contradicts ~N w.
        h_w_eq_n = ASSUME(mk_eq(w_t, n_var))
        Nw_th = EQ_MP(AP_TERM(N_var, SYM(h_w_eq_n)), h_Nn2)    # {N n, w=n} |- N w
        # contradict h_not_Nw:
        th_F_b = MP(NOT_ELIM(h_not_Nw), Nw_th)                 # {N n, w=n, ~N w} |- F
        not_w_eq_n = NOT_INTRO(DISCH(mk_eq(w_t, n_var), th_F_b))   # {N n, ~N w} |- ~(w=n)
        # w <= n and w != n => w < n.  via UNFOLD_LE: w <= n = (w < n) \/ (w = n).
        w_le_unfold = EQ_MP(UNFOLD_LE(w_t, n_var), w_le_n)     # (w<n) \/ (w=n)
        branch_lt_b = DISCH(mk_lt(w_t, n_var), ASSUME(mk_lt(w_t, n_var)))
        branch_eq_b = DISCH(mk_eq(w_t, n_var),
                            CONTR(mk_lt(w_t, n_var),
                                  MP(NOT_ELIM(not_w_eq_n), ASSUME(mk_eq(w_t, n_var)))))
        w_lt_n = DISJ_CASES(w_le_unfold, branch_lt_b, branch_eq_b)   # |- w < n
        # By Theorem 25 with x:=w, y:=n: n > w ==> n >= w + 1.
        # We have w < n; convert to n > w via Theorem 12.
        n_gt_w = MP(SPEC(n_var, SPEC(w_t, SATZ_12)), w_lt_n)
        s25_inst = SPEC(n_var, SPEC(w_t, SATZ_25))             # |- n > w ==> n >= w + 1
        n_ge_wp1 = MP(s25_inst, n_gt_w)                        # |- n >= w + 1
        # Convert n >= w+1 to w+1 <= n via Theorem 13.
        wp1_le_n = MP(SPEC(mk_add(w_t, ONE), SPEC(n_var, SATZ_13)), n_ge_wp1)
        forall_wp1_le = GEN(n_var,
                             DISCH(mk_comb(N_var, n_var), wp1_le_n))   # {~N w} |- !n. N n ==> w+1 <= n
        # That's M(w+1).
        M_wp1 = EQ_MP(SYM(BETA_CONV(M_at(mk_add(w_t, ONE)))), forall_wp1_le)
        # Contradicts ~M(w+1):
        th_F_b2 = MP(NOT_ELIM(notM_w1), M_wp1)                 # {~N w} |- F
        Nw_th_final = NOT_NOT_ELIM(NOT_INTRO(DISCH(mk_not(mk_comb(N_var, w_t)),
                                                     th_F_b2)))    # |- N w
        # Combine: N w /\ !k. N k ==> w <= k.
        conj_final = CONJ(Nw_th_final, sub_a_alt)
        # EXISTS over m.
        m_pred_concl = mk_abs(m_var,
                               mk_and(mk_comb(N_var, m_var),
                                       mk_forall(k_var,
                                                 mk_imp(mk_comb(N_var, k_var),
                                                        mk_le(m_var, k_var)))))
        return EXISTS(m_pred_concl, w_t, conj_final)
    th_concl_inner = ELIM_EX(Q_pred, target_3, _from_m)
    # Discharge target_3 using th_target3:
    th_concl = PROVE_HYP(th_target3, th_concl_inner)
    # th_concl : {hyp_nonempty} |- conclusion
    return GEN(N_var, DISCH(hyp_nonempty, th_concl))


SATZ_27 = _prove_satz_27()


# ---------------------------------------------------------------------------
# #4 -- Multiplikation
# ---------------------------------------------------------------------------
#
# Following Definition 6 (justified by Theorem 28 in Landau, the existence
# half of which is admitted as we did for + in Definition 1).
# ---------------------------------------------------------------------------

# Multiplication is defined analogously, via NUM_RECURSION at  c := x, h := \k a. a + x.
# Then:  x * 1 = x  and  x * (SUC y) = x * y + x.

_mul_fn = Var("fn", mk_fun_ty(num_ty, num_ty))
_mul_n  = Var("n", num_ty)

def _mul_pred_term(x_t):
    """\\fn. fn 1 = x_t /\\ !n. fn (SUC n) = (fn n) + x_t."""
    fn_1  = mk_comb(_mul_fn, ONE)
    fn_n  = mk_comb(_mul_fn, _mul_n)
    fn_sn = mk_comb(_mul_fn, mk_suc(_mul_n))
    body  = mk_and(mk_eq(fn_1, x_t),
                    mk_forall(_mul_n,
                        mk_eq(fn_sn, mk_add(fn_n, x_t))))
    return mk_abs(_mul_fn, body)

_select_mul = mk_const("@", [(mk_fun_ty(num_ty, num_ty), aty)])

_mul_def_rhs = mk_abs(_x_d, mk_abs(_y_d,
    mk_comb(mk_comb(_select_mul, _mul_pred_term(_x_d)), _y_d)))

MUL_DEF = new_basic_definition(
    mk_eq(Var("*", mk_fun_ty(num_ty, mk_fun_ty(num_ty, num_ty))),
          _mul_def_rhs))
TIMES = mk_const("*", [])
_INFIX.add("*")

def mk_mul(a, b):
    return mk_comb(mk_comb(TIMES, a), b)


def _prove_mul_eqs():
    """Derive MUL_1 = |- !x. x * 1 = x  and  MUL_SUC = |- !x y. x * SUC y = x * y + x."""
    NR_num = INST_TYPE([(num_ty, aty)], NUM_RECURSION)
    k_v = Var("k", num_ty)
    a_v = Var("a", num_ty)
    h_const = mk_abs(k_v, mk_abs(a_v, mk_add(a_v, x)))   # \k a. a + x
    spec_c = SPEC(x, NR_num)                              # |- !h. ?fn. fn 1 = x /\ !n. fn (SUC n) = h n (fn n)
    spec_ch = SPEC(h_const, spec_c)                       # |- ?fn. fn 1 = x /\ !n. fn (SUC n) = (\k a. a+x) n (fn n)

    pred_raw = spec_ch._concl.arg
    sel_at_pred = mk_comb(_select_mul, pred_raw)

    pred_clean = _mul_pred_term(x)
    sel_at_pred_clean = mk_comb(_select_mul, pred_clean)

    body_raw_at_w = ELIM_EX(pred_raw, spec_ch._concl, lambda th: th)
    body_raw_th   = PROVE_HYP(spec_ch, body_raw_at_w)

    raw_conj1 = CONJUNCT1(body_raw_th)   # |- witness 1 = x
    raw_conj2 = CONJUNCT2(body_raw_th)   # |- !n. witness (SUC n) = (\k a. a+x) n (witness n)

    # Reduce (\k a. a+x) n (fn n) = (fn n) + x.
    h_at_n = BETA_CONV(mk_comb(h_const, _mul_n))                   # |- (\k a. a+x) n = \a. a + x
    h_at_n_fnn = AP_THM(h_at_n, mk_comb(_mul_fn, _mul_n))           # |- ((\k a. a+x) n) (fn n) = (\a. a+x) (fn n)
    final_beta = BETA_CONV(mk_comb(mk_abs(a_v, mk_add(a_v, x)),
                                     mk_comb(_mul_fn, _mul_n)))     # |- (\a. a+x) (fn n) = (fn n) + x
    h_red = TRANS(h_at_n_fnn, final_beta)                            # |- (\k a. a+x) n (fn n) = (fn n) + x

    raw_at_n = SPEC(_mul_n, raw_conj2)                                # |- witness (SUC n) = (\k a. a+x) n (witness n)
    h_red_at_w = INST([(sel_at_pred, _mul_fn)], h_red)                # |- (\k a. a+x) n (witness n) = (witness n) + x
    raw_clean_n = TRANS(raw_at_n, h_red_at_w)                          # |- witness (SUC n) = (witness n) + x
    raw_clean_forall = GEN(_mul_n, raw_clean_n)

    P_clean_at_w = CONJ(raw_conj1, raw_clean_forall)
    pred_clean_at_w = mk_comb(pred_clean, sel_at_pred)
    pred_clean_at_w_eq = BETA_CONV(pred_clean_at_w)
    pred_clean_witness = EQ_MP(SYM(pred_clean_at_w_eq), P_clean_at_w)

    sel_inst = INST_TYPE([(mk_fun_ty(num_ty, num_ty), aty)], SELECT_AX)
    sel_imp = SPEC(sel_at_pred, SPEC(pred_clean, sel_inst))
    pred_clean_at_select = MP(sel_imp, pred_clean_witness)
    sel_pred_clean = sel_at_pred_clean
    select_at_clean_eq = BETA_CONV(mk_comb(pred_clean, sel_pred_clean))
    select_at_clean_body = EQ_MP(select_at_clean_eq, pred_clean_at_select)
    sel_at_1_eq_x = CONJUNCT1(select_at_clean_body)   # |- (@fn. ...) 1 = x
    sel_at_sn_eq  = CONJUNCT2(select_at_clean_body)   # |- !n. (@fn. ...) (SUC n) = (@fn. ...) n + x

    times_at_x = AP_THM(MUL_DEF, x)
    times_at_x_beta = TRANS(times_at_x, BETA_CONV(rand(times_at_x._concl)))
    times_at_x_at_1 = AP_THM(times_at_x_beta, ONE)
    times_at_x_at_1_beta = TRANS(times_at_x_at_1,
                                   BETA_CONV(rand(times_at_x_at_1._concl)))
    mul1_eq = TRANS(times_at_x_at_1_beta, sel_at_1_eq_x)   # |- x * 1 = x
    MUL_1_th = GEN(x, mul1_eq)

    times_at_x_at_sy = AP_THM(times_at_x_beta, mk_suc(y))
    times_at_x_at_sy_beta = TRANS(times_at_x_at_sy,
                                    BETA_CONV(rand(times_at_x_at_sy._concl)))
    sel_at_sy = SPEC(y, sel_at_sn_eq)                       # |- (@fn. ...) (SUC y) = (@fn. ...) y + x
    times_at_x_at_y = AP_THM(times_at_x_beta, y)
    times_at_x_at_y_beta = TRANS(times_at_x_at_y,
                                   BETA_CONV(rand(times_at_x_at_y._concl)))
    # Need to rewrite (@fn. ...) y back to x * y. Note: we have x * y = (@fn. ...) y.
    # SUC's analogue: ((@fn. ...) y + x) = (x*y + x) via AP_THM(AP_TERM(PLUS, SYM(times_at_x_at_y_beta)), x).
    rewrite_lhs = AP_THM(AP_TERM(PLUS, SYM(times_at_x_at_y_beta)), x)   # |- (@fn. ...) y + x = x*y + x
    mul_suc_eq = TRANS(times_at_x_at_sy_beta, TRANS(sel_at_sy, rewrite_lhs))   # |- x * SUC y = x*y + x
    MUL_SUC_th = GEN(x, GEN(y, mul_suc_eq))

    return MUL_1_th, MUL_SUC_th


MUL_1, MUL_SUC = _prove_mul_eqs()


# Helpers (from Landau's "construction in the proof of Theorem 28"):
# ONE_MUL :  |- !y. 1 * y = y.
# SUC_MUL :  |- !x y. (SUC x) * y = x * y + y.

def _prove_one_mul():
    pred = mk_abs(y, mk_eq(mk_mul(ONE, y), y))
    base = SPEC(ONE, MUL_1)                              # |- 1 * 1 = 1
    body_y = mk_eq(mk_mul(ONE, y), y)
    IH = ASSUME(body_y)
    s1 = SPEC(y, SPEC(ONE, MUL_SUC))                     # |- 1 * SUC y = 1 * y + 1
    s2 = AP_THM(AP_TERM(PLUS, IH), ONE)                  # |- 1 * y + 1 = y + 1
    s3 = SPEC(y, ADD_1)                                  # |- y + 1 = SUC y
    step_inner = TRANS(s1, TRANS(s2, s3))
    step = GEN(y, DISCH(body_y, step_inner))
    return INDUCT(pred, base, step)

ONE_MUL = _prove_one_mul()

def _prove_suc_mul():
    body_y = mk_eq(mk_mul(mk_suc(x), y), mk_add(mk_mul(x, y), y))
    pred = mk_abs(y, body_y)
    # base y=1: (SUC x)*1 = SUC x = x+1 = x*1 + 1.
    a = SPEC(mk_suc(x), MUL_1)                           # |- SUC x * 1 = SUC x
    b = SYM(SPEC(x, ADD_1))                              # |- SUC x = x + 1
    c = AP_THM(AP_TERM(PLUS, SYM(SPEC(x, MUL_1))), ONE)  # |- x + 1 = x*1 + 1
    base = TRANS(a, TRANS(b, c))
    IH = ASSUME(body_y)
    # step: (SUC x)*SUC y = (SUC x)*y + (SUC x) [MUL_SUC]
    #     = (x*y + y) + SUC x [IH applied via AP_THM]
    #     = x*y + (y + SUC x) [SATZ_5]
    #     = x*y + (SUC y + x) [comm of inner]
    #     = x*y + (SUC(y + x)) [SUC_PLUS reversed... wait, SUC y + x = SUC(y+x)]
    # Hmm let me be careful.
    # We want: (SUC x)*SUC y = x*SUC y + SUC y.
    # x*SUC y = x*y + x [MUL_SUC].  So x*SUC y + SUC y = (x*y + x) + SUC y = x*y + (x + SUC y).
    # And LHS = (SUC x)*SUC y = (SUC x)*y + SUC x = (x*y + y) + SUC x = x*y + (y + SUC x).
    # We need (y + SUC x) = (x + SUC y).
    # y + SUC x = SUC(y + x) = SUC(x + y) = x + SUC y. ✓
    s1 = SPEC(y, SPEC(mk_suc(x), MUL_SUC))               # |- (SUC x)*SUC y = (SUC x)*y + SUC x
    s2 = AP_THM(AP_TERM(PLUS, IH), mk_suc(x))            # |- (SUC x)*y + SUC x = (x*y+y) + SUC x
    s3 = SPEC(mk_suc(x), SPEC(y, SPEC(mk_mul(x, y), SATZ_5)))   # |- (x*y+y)+SUC x = x*y + (y+SUC x)
    # y + SUC x = SUC y + x  via comm (Theorem 6) of (y, SUC x) NO wait.
    # Want: y + SUC x = x + SUC y.   y + SUC x = SUC(y+x) [ADD_SUC] = SUC(x+y) [comm] = x + SUC y [SYM ADD_SUC].
    a1 = SPEC(x, SPEC(y, ADD_SUC))                       # |- y + SUC x = SUC(y+x)
    a2 = AP_TERM(SUC, SPEC(x, SPEC(y, SATZ_6)))          # |- SUC(y+x) = SUC(x+y)
    a3 = SYM(SPEC(y, SPEC(x, ADD_SUC)))                  # |- SUC(x+y) = x + SUC y
    inner_chain = TRANS(a1, TRANS(a2, a3))               # |- y + SUC x = x + SUC y
    s4 = AP_TERM(mk_comb(PLUS, mk_mul(x, y)), inner_chain)   # |- x*y + (y+SUC x) = x*y + (x+SUC y)
    # And x*y + (x + SUC y) = (x*y + x) + SUC y [SYM SATZ_5]
    s5 = SYM(SPEC(mk_suc(y), SPEC(x, SPEC(mk_mul(x, y), SATZ_5))))  # |- x*y + (x+SUC y) = (x*y+x)+SUC y
    # And (x*y + x) = x*SUC y [SYM MUL_SUC]
    s6 = AP_THM(AP_TERM(PLUS, SYM(SPEC(y, SPEC(x, MUL_SUC)))), mk_suc(y))  # |- (x*y+x)+SUC y = x*SUC y + SUC y
    step_inner = TRANS(s1, TRANS(s2, TRANS(s3, TRANS(s4, TRANS(s5, s6)))))
    step = GEN(y, DISCH(body_y, step_inner))
    return GEN(x, INDUCT(pred, base, step))

SUC_MUL = _prove_suc_mul()


# Theorem 29 (commutative law of multiplication):  |- !x y. x * y = y * x.

def _prove_satz_29():
    body_x = mk_eq(mk_mul(x, y), mk_mul(y, x))
    pred = mk_abs(x, body_x)
    # base x = 1:  1*y = y = y*1.
    base = TRANS(SPEC(y, ONE_MUL), SYM(SPEC(y, MUL_1)))
    IH = ASSUME(body_x)
    # SUC x * y = x*y + y [SUC_MUL] = y*x + y [AP_THM IH] = y*SUC x [SYM MUL_SUC].
    s1 = SPEC(y, SPEC(x, SUC_MUL))                        # |- SUC x * y = x*y + y
    s2 = AP_THM(AP_TERM(PLUS, IH), y)                     # |- x*y + y = y*x + y
    s3 = SYM(SPEC(x, SPEC(y, MUL_SUC)))                   # |- y*x + y = y * SUC x
    step_inner = TRANS(s1, TRANS(s2, s3))
    step = GEN(x, DISCH(body_x, step_inner))
    forall_x = INDUCT(pred, base, step)
    return GEN(x, GEN(y, SPEC(x, forall_x)))

SATZ_29 = _prove_satz_29()


# Theorem 30 (distributive):  |- !x y z. x * (y + z) = x*y + x*z.   Induction on z.

def _prove_satz_30():
    body_z = mk_eq(mk_mul(x, mk_add(y, z)), mk_add(mk_mul(x, y), mk_mul(x, z)))
    pred = mk_abs(z, body_z)
    # base z=1: x*(y+1) = x*SUC y = x*y + x = x*y + x*1.
    a = AP_TERM(mk_comb(TIMES, x), SPEC(y, ADD_1))        # |- x*(y+1) = x*SUC y
    b = SPEC(y, SPEC(x, MUL_SUC))                         # |- x*SUC y = x*y + x
    c = AP_TERM(mk_comb(PLUS, mk_mul(x, y)),              # |- x*y + x = x*y + x*1
                SYM(SPEC(x, MUL_1)))
    base = TRANS(a, TRANS(b, c))
    IH = ASSUME(body_z)
    # x*(y+SUC z) = x*SUC(y+z) [AP_TERM x*, ADD_SUC]
    #             = x*(y+z) + x [MUL_SUC]
    #             = (x*y + x*z) + x [IH applied via AP_THM]
    #             = x*y + (x*z + x) [SATZ_5]
    #             = x*y + x*SUC z [SYM MUL_SUC]
    s1 = AP_TERM(mk_comb(TIMES, x),
                  SPEC(z, SPEC(y, ADD_SUC)))               # |- x*(y+SUC z) = x*SUC(y+z)
    s2 = SPEC(mk_add(y, z), SPEC(x, MUL_SUC))             # |- x*SUC(y+z) = x*(y+z) + x
    s3 = AP_THM(AP_TERM(PLUS, IH), x)                      # |- x*(y+z) + x = (x*y + x*z) + x
    s4 = SPEC(x, SPEC(mk_mul(x, z), SPEC(mk_mul(x, y), SATZ_5)))   # |- (x*y+x*z)+x = x*y + (x*z + x)
    s5 = AP_TERM(mk_comb(PLUS, mk_mul(x, y)),
                  SYM(SPEC(z, SPEC(x, MUL_SUC))))          # |- x*y + (x*z + x) = x*y + x*SUC z
    step_inner = TRANS(s1, TRANS(s2, TRANS(s3, TRANS(s4, s5))))
    step = GEN(z, DISCH(body_z, step_inner))
    return GEN(x, GEN(y, INDUCT(pred, base, step)))

SATZ_30 = _prove_satz_30()


# Theorem 31 (associative law of multiplication):  |- !x y z. (x*y) * z = x * (y*z).   Induction on z.

def _prove_satz_31():
    body_z = mk_eq(mk_mul(mk_mul(x, y), z), mk_mul(x, mk_mul(y, z)))
    pred = mk_abs(z, body_z)
    # base z = 1: (x*y) * 1 = x*y = x*(y*1).
    a = SPEC(mk_mul(x, y), MUL_1)                         # |- (x*y)*1 = x*y
    b = AP_TERM(mk_comb(TIMES, x), SYM(SPEC(y, MUL_1)))   # |- x*y = x*(y*1)
    base = TRANS(a, b)
    IH = ASSUME(body_z)
    # (x*y)*SUC z = (x*y)*z + (x*y) [MUL_SUC]
    #             = x*(y*z) + x*y [IH applied]
    #             = x*(y*z + y) [SATZ_30 SYM]
    #             = x*(y*SUC z) [SYM MUL_SUC]
    s1 = SPEC(z, SPEC(mk_mul(x, y), MUL_SUC))             # |- (x*y)*SUC z = (x*y)*z + (x*y)
    s2 = AP_THM(AP_TERM(PLUS, IH), mk_mul(x, y))           # |- (x*y)*z + x*y = x*(y*z) + x*y
    s3 = SYM(SPEC(y, SPEC(mk_mul(y, z), SPEC(x, SATZ_30))))   # |- x*(y*z) + x*y = x*(y*z + y)
    s4 = AP_TERM(mk_comb(TIMES, x),
                  SYM(SPEC(z, SPEC(y, MUL_SUC))))         # |- x*(y*z + y) = x*(y*SUC z)
    step_inner = TRANS(s1, TRANS(s2, TRANS(s3, s4)))
    step = GEN(z, DISCH(body_z, step_inner))
    return GEN(x, GEN(y, INDUCT(pred, base, step)))

SATZ_31 = _prove_satz_31()


# Theorem 32 (3-fold "respectively"):  From  x>y / x=y / x<y  it follows  xz > yz / xz = yz / xz < yz.
# We prove the three pieces; same template as Theorem 19.

def _prove_satz_32a():
    h = ASSUME(mk_gt(x, y))
    ex_u = EQ_MP(UNFOLD_GT(x, y), h)                      # ?u. x = y + u
    pred_u = mk_abs(u, mk_eq(x, mk_add(y, u)))
    def _from(eq_x):
        u0 = rand(rand(eq_x._concl))
        # x*z = (y+u0)*z = y*z + u0*z.    By SATZ_29 + SATZ_30:
        # (y+u0)*z = z*(y+u0) [SATZ_29] = z*y + z*u0 [SATZ_30] = y*z + u0*z [SATZ_29 twice].
        ap = AP_THM(AP_TERM(TIMES, eq_x), z)                # |- x*z = (y+u0)*z
        comm1 = SPEC(z, SPEC(mk_add(y, u0), SATZ_29))       # |- (y+u0)*z = z*(y+u0)
        dist = SPEC(u0, SPEC(y, SPEC(z, SATZ_30)))           # |- z*(y+u0) = z*y + z*u0
        comm2 = AP_THM(AP_TERM(PLUS, SPEC(y, SPEC(z, SATZ_29))),
                        mk_mul(z, u0))                       # |- z*y + z*u0 = y*z + z*u0
        comm3 = AP_TERM(mk_comb(PLUS, mk_mul(y, z)),
                         SPEC(u0, SPEC(z, SATZ_29)))         # |- y*z + z*u0 = y*z + u0*z
        path = TRANS(ap, TRANS(comm1, TRANS(dist, TRANS(comm2, comm3))))
        # path : |- x*z = y*z + u0*z.   Witness u0*z for ?u. x*z = y*z + u.
        pred_final = mk_abs(u, mk_eq(mk_mul(x, z), mk_add(mk_mul(y, z), u)))
        return EXISTS(pred_final, mk_mul(u0, z), path)
    th_inner = ELIM_EX(pred_u, ex_u._concl, _from)
    th_full = PROVE_HYP(ex_u, th_inner)
    th_gt = EQ_MP(SYM(UNFOLD_GT(mk_mul(x, z), mk_mul(y, z))), th_full)
    return GEN(x, GEN(y, GEN(z, DISCH(mk_gt(x, y), th_gt))))

SATZ_32A = _prove_satz_32a()

def _prove_satz_32b():
    h = ASSUME(mk_eq(x, y))
    return GEN(x, GEN(y, GEN(z,
              DISCH(mk_eq(x, y), AP_THM(AP_TERM(TIMES, h), z)))))

SATZ_32B = _prove_satz_32b()

def _prove_satz_32c():
    h = ASSUME(mk_lt(x, y))
    th_yx = MP(SPEC(y, SPEC(x, SATZ_12)), h)               # y > x
    s32a = SPEC(z, SPEC(x, SPEC(y, SATZ_32A)))             # |- y > x ==> y*z > x*z
    th_yz_gt = MP(s32a, th_yx)
    th_lt = MP(SPEC(mk_mul(x, z), SPEC(mk_mul(y, z), SATZ_11)), th_yz_gt)
    return GEN(x, GEN(y, GEN(z, DISCH(mk_lt(x, y), th_lt))))

SATZ_32C = _prove_satz_32c()


# Theorem 34:  x>y, z>u  ==>  x*z > y*u.   Mirror of Theorem 21.

def _prove_satz_34():
    h_xy = ASSUME(mk_gt(x, y))
    h_zu = ASSUME(mk_gt(z, u))
    s32a_xy = MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32A))), h_xy)    # x*z > y*z
    s32a_zu = MP(SPEC(y, SPEC(u, SPEC(z, SATZ_32A))), h_zu)    # z*y > u*y
    comm_zy = SPEC(y, SPEC(z, SATZ_29))                         # |- z*y = y*z
    comm_uy = SPEC(y, SPEC(u, SATZ_29))                         # |- u*y = y*u
    rewrite = MK_COMB(AP_TERM(GT, comm_zy), comm_uy)
    th_yz_gt_yu = EQ_MP(rewrite, s32a_zu)                       # y*z > y*u
    th_yu_lt_yz = MP(SPEC(mk_mul(y, u), SPEC(mk_mul(y, z), SATZ_11)), th_yz_gt_yu)
    th_yz_lt_xz = MP(SPEC(mk_mul(y, z), SPEC(mk_mul(x, z), SATZ_11)), s32a_xy)
    s15 = SPEC(mk_mul(x, z), SPEC(mk_mul(y, z), SPEC(mk_mul(y, u), SATZ_15)))
    th_lt = MP(MP(s15, th_yu_lt_yz), th_yz_lt_xz)
    th_gt = MP(SPEC(mk_mul(x, z), SPEC(mk_mul(y, u), SATZ_12)), th_lt)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_gt(x, y), DISCH(mk_gt(z, u), th_gt))))))

SATZ_34 = _prove_satz_34()


# Theorem 35:  x>=y, z>u (or x>y, z>=u)  ==>  x*z > y*u.

def _prove_satz_35a():
    h_ge = ASSUME(mk_ge(x, y))
    h_gt = ASSUME(mk_gt(z, u))
    u_ge = EQ_MP(UNFOLD_GE(x, y), h_ge)
    s34 = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_34))))
    branch_gt = DISCH(mk_gt(x, y), MP(MP(s34, ASSUME(mk_gt(x, y))), h_gt))
    eq_xy = ASSUME(mk_eq(x, y))
    s32a_zu = MP(SPEC(y, SPEC(u, SPEC(z, SATZ_32A))), h_gt)     # z*y > u*y
    comm_zy = SPEC(y, SPEC(z, SATZ_29))
    comm_uy = SPEC(y, SPEC(u, SATZ_29))
    th_yzgt = EQ_MP(MK_COMB(AP_TERM(GT, comm_zy), comm_uy), s32a_zu)   # y*z > y*u
    yz_eq_xz = AP_THM(AP_TERM(TIMES, SYM(eq_xy)), z)             # |- y*z = x*z
    rewrite = MK_COMB(AP_TERM(GT, yz_eq_xz), REFL(mk_mul(y, u))) # |- (y*z>y*u) = (x*z>y*u)
    branch_eq = DISCH(mk_eq(x, y), EQ_MP(rewrite, th_yzgt))
    th = DISJ_CASES(u_ge, branch_gt, branch_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_ge(x, y), DISCH(mk_gt(z, u), th))))))

SATZ_35A = _prove_satz_35a()

def _prove_satz_35b():
    h_gt = ASSUME(mk_gt(x, y))
    h_ge = ASSUME(mk_ge(z, u))
    u_ge = EQ_MP(UNFOLD_GE(z, u), h_ge)
    s34 = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_34))))
    branch_gt = DISCH(mk_gt(z, u), MP(MP(s34, h_gt), ASSUME(mk_gt(z, u))))
    eq_zu = ASSUME(mk_eq(z, u))
    s32a_xy = MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32A))), h_gt)     # x*z > y*z
    yz_eq_yu = AP_TERM(mk_comb(TIMES, y), eq_zu)                 # |- y*z = y*u
    rewrite = MK_COMB(AP_TERM(GT, REFL(mk_mul(x, z))), yz_eq_yu)
    branch_eq = DISCH(mk_eq(z, u), EQ_MP(rewrite, s32a_xy))
    th = DISJ_CASES(u_ge, branch_gt, branch_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_gt(x, y), DISCH(mk_ge(z, u), th))))))

SATZ_35B = _prove_satz_35b()


# Theorem 36:  x>=y, z>=u  ==>  x*z >= y*u.

def _prove_satz_36():
    h_xy = ASSUME(mk_ge(x, y))
    h_zu = ASSUME(mk_ge(z, u))
    ux  = EQ_MP(UNFOLD_GE(x, y), h_xy)
    uz  = EQ_MP(UNFOLD_GE(z, u), h_zu)
    s35a = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_35A))))
    s35b = SPEC(u, SPEC(z, SPEC(y, SPEC(x, SATZ_35B))))
    branch_x_gt = DISCH(mk_gt(x, y),
                        GT_TO_GE(MP(MP(s35b, ASSUME(mk_gt(x, y))), h_zu)))
    eq_xy = ASSUME(mk_eq(x, y))
    branch_z_gt = DISCH(mk_gt(z, u),
                        GT_TO_GE(MP(MP(s35a, h_xy), ASSUME(mk_gt(z, u)))))
    eq_zu = ASSUME(mk_eq(z, u))
    eq_prod = MK_COMB(AP_TERM(TIMES, eq_xy), eq_zu)         # |- x*z = y*u
    branch_z_eq = DISCH(mk_eq(z, u), EQ_TO_GE(eq_prod))
    branch_x_eq = DISCH(mk_eq(x, y), DISJ_CASES(uz, branch_z_gt, branch_z_eq))
    th = DISJ_CASES(ux, branch_x_gt, branch_x_eq)
    return GEN(x, GEN(y, GEN(z, GEN(u,
              DISCH(mk_ge(x, y), DISCH(mk_ge(z, u), th))))))

SATZ_36 = _prove_satz_36()


# ---------------------------------------------------------------------------
# Theorem 9, part A (mutual exclusion of trichotomy):
#   |- !x y. ~(x = y     /\  ?u. x = y + u)
#         /\ ~(x = y     /\  ?v. y = x + v)
#         /\ ~((?u. x = y + u) /\ (?v. y = x + v))
# ---------------------------------------------------------------------------

def _prove_satz_9_excl():
    case2 = mk_exists(u, mk_eq(x, mk_add(y, u)))
    case3 = mk_exists(v, mk_eq(y, mk_add(x, v)))

    # Pair 1: x = y AND case2 are inconsistent.
    h_xy = ASSUME(mk_eq(x, y))
    h_c2 = ASSUME(case2)
    pred_u = mk_abs(u, mk_eq(x, mk_add(y, u)))
    def _from_c2(eq_x):
        u0 = rand(rand(eq_x._concl))
        chain = TRANS(SYM(h_xy), eq_x)                       # |- y = y + u0
        comm  = SPEC(y, SPEC(u0, SATZ_6))
        ne    = SPEC(y, SPEC(u0, SATZ_7))
        ne_f  = REWRITE_NE(ne, REFL(y), comm)
        return MP(NOT_ELIM(ne_f), chain)
    th_F1 = PROVE_HYP(h_c2, ELIM_EX(pred_u, case2, _from_c2))   # {x=y, case2} |- F
    excl_12 = NOT_INTRO(DISCH(mk_and(mk_eq(x, y), case2),
                              MP(NOT_ELIM(NOT_INTRO(DISCH(case2,
                                  PROVE_HYP(CONJUNCT2(ASSUME(mk_and(mk_eq(x, y), case2))),
                                            PROVE_HYP(CONJUNCT1(ASSUME(mk_and(mk_eq(x, y), case2))),
                                                      th_F1))))),
                                 ASSUME(case2))))
    # The above is getting tangled.  Cleaner: just build {(x=y) /\ case2} |- F directly.
    h_conj_12 = ASSUME(mk_and(mk_eq(x, y), case2))
    th_F1b = PROVE_HYP(CONJUNCT2(h_conj_12),
                       PROVE_HYP(CONJUNCT1(h_conj_12), th_F1))
    excl_12 = NOT_INTRO(DISCH(mk_and(mk_eq(x, y), case2), th_F1b))

    # Pair 2: x = y AND case3 are inconsistent.
    h_c3 = ASSUME(case3)
    pred_v = mk_abs(v, mk_eq(y, mk_add(x, v)))
    def _from_c3(eq_y):
        v0 = rand(rand(eq_y._concl))
        chain = TRANS(h_xy, eq_y)                            # {x=y} |- x = x + v0  (using y = x + v0 via x=y)
        # Actually: from x = y and y = x + v0, we get x = x + v0.  Wait, eq_y is `y = x + v0`. We want chain = `x = x + v0`.
        # x = y (h_xy), y = x + v0 (eq_y), so x = x + v0 by TRANS.
        # That contradicts SATZ_7 (~ (x = v0 + x)) modulo comm.
        chain2 = TRANS(h_xy, eq_y)                           # {x=y, eq_y hyp} |- x = x + v0
        comm   = SPEC(x, SPEC(v0, SATZ_6))                   # |- v0+x = x+v0
        ne     = SPEC(x, SPEC(v0, SATZ_7))                   # |- ~(x = v0+x)
        ne_f   = REWRITE_NE(ne, REFL(x), comm)               # |- ~(x = x+v0)
        return MP(NOT_ELIM(ne_f), chain2)
    th_F2 = PROVE_HYP(h_c3, ELIM_EX(pred_v, case3, _from_c3))
    h_conj_13 = ASSUME(mk_and(mk_eq(x, y), case3))
    th_F2b = PROVE_HYP(CONJUNCT2(h_conj_13),
                       PROVE_HYP(CONJUNCT1(h_conj_13), th_F2))
    excl_13 = NOT_INTRO(DISCH(mk_and(mk_eq(x, y), case3), th_F2b))

    # Pair 3: case2 AND case3 are inconsistent.
    def _from_c2_outer(eq_x):
        u0 = rand(rand(eq_x._concl))
        def _from_c3_inner(eq_y):
            v0 = rand(rand(eq_y._concl))
            # x = y + u0; y = x + v0; so x = (x+v0) + u0 = x + (v0+u0)
            sub_y = AP_THM(AP_TERM(PLUS, eq_y), u0)          # |- y + u0 = (x+v0) + u0
            chain = TRANS(eq_x, sub_y)                        # |- x = (x+v0) + u0
            assoc = SPEC(u0, SPEC(v0, SPEC(x, SATZ_5)))       # |- (x+v0)+u0 = x+(v0+u0)
            chain2 = TRANS(chain, assoc)                      # |- x = x + (v0+u0)
            comm = SPEC(x, SPEC(mk_add(v0, u0), SATZ_6))     # |- (v0+u0)+x = x+(v0+u0)
            ne   = SPEC(x, SPEC(mk_add(v0, u0), SATZ_7))     # |- ~(x = (v0+u0)+x)
            ne_f = REWRITE_NE(ne, REFL(x), comm)             # |- ~(x = x+(v0+u0))
            return MP(NOT_ELIM(ne_f), chain2)
        return ELIM_EX(pred_v, case3, _from_c3_inner)
    th_F3_inner = ELIM_EX(pred_u, case2, _from_c2_outer)
    th_F3 = PROVE_HYP(h_c3, PROVE_HYP(h_c2, th_F3_inner))
    h_conj_23 = ASSUME(mk_and(case2, case3))
    th_F3b = PROVE_HYP(CONJUNCT2(h_conj_23),
                       PROVE_HYP(CONJUNCT1(h_conj_23), th_F3))
    excl_23 = NOT_INTRO(DISCH(mk_and(case2, case3), th_F3b))

    th_all = CONJ(excl_12, CONJ(excl_13, excl_23))
    return GEN(x, GEN(y, th_all))

SATZ_9_EXCL = _prove_satz_9_excl()


# ---------------------------------------------------------------------------
# Theorem 20.   |- !x y z. (x+z > y+z ==> x > y)
#                       /\ (x+z = y+z ==> x = y)
#                       /\ (x+z < y+z ==> x < y).
# Proof (Landau): from Theorem 19 + trichotomy, since the three cases of
# trichotomy mutually exclude each other.
# ---------------------------------------------------------------------------

def _prove_satz_20():
    s10 = SPEC(y, SPEC(x, SATZ_10))                          # (x=y) \/ (x>y \/ x<y)

    # Goal A: x+z > y+z ==> x > y.
    h_a = ASSUME(mk_gt(mk_add(x, z), mk_add(y, z)))
    branch_eq_A = DISCH(mk_eq(x, y),
                        CONTR(mk_gt(x, y),
                              CONTRA_GT_EQ(mk_add(x, z), mk_add(y, z),
                                           h_a,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19B))),
                                              ASSUME(mk_eq(x, y))))))
    branch_gt_A = DISCH(mk_gt(x, y), ASSUME(mk_gt(x, y)))
    branch_lt_A = DISCH(mk_lt(x, y),
                        CONTR(mk_gt(x, y),
                              CONTRA_LT_GT(mk_add(x, z), mk_add(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19C))),
                                              ASSUME(mk_lt(x, y))),
                                           h_a)))
    inner_or_A = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_A, branch_lt_A)
    inner_disch_A = DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_A)
    th_A = DISJ_CASES(s10, branch_eq_A, inner_disch_A)
    goal_A = DISCH(mk_gt(mk_add(x, z), mk_add(y, z)), th_A)

    # Goal B: x+z = y+z ==> x = y.
    h_b = ASSUME(mk_eq(mk_add(x, z), mk_add(y, z)))
    branch_eq_B = DISCH(mk_eq(x, y), ASSUME(mk_eq(x, y)))
    branch_gt_B = DISCH(mk_gt(x, y),
                        CONTR(mk_eq(x, y),
                              CONTRA_GT_EQ(mk_add(x, z), mk_add(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19A))),
                                              ASSUME(mk_gt(x, y))),
                                           h_b)))
    branch_lt_B = DISCH(mk_lt(x, y),
                        CONTR(mk_eq(x, y),
                              CONTRA_LT_EQ(mk_add(x, z), mk_add(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19C))),
                                              ASSUME(mk_lt(x, y))),
                                           h_b)))
    inner_or_B = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_B, branch_lt_B)
    inner_disch_B = DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_B)
    th_B = DISJ_CASES(s10, branch_eq_B, inner_disch_B)
    goal_B = DISCH(mk_eq(mk_add(x, z), mk_add(y, z)), th_B)

    # Goal C: x+z < y+z ==> x < y.
    h_c = ASSUME(mk_lt(mk_add(x, z), mk_add(y, z)))
    branch_eq_C = DISCH(mk_eq(x, y),
                        CONTR(mk_lt(x, y),
                              CONTRA_LT_EQ(mk_add(x, z), mk_add(y, z),
                                           h_c,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19B))),
                                              ASSUME(mk_eq(x, y))))))
    branch_gt_C = DISCH(mk_gt(x, y),
                        CONTR(mk_lt(x, y),
                              CONTRA_LT_GT(mk_add(x, z), mk_add(y, z),
                                           h_c,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_19A))),
                                              ASSUME(mk_gt(x, y))))))
    branch_lt_C = DISCH(mk_lt(x, y), ASSUME(mk_lt(x, y)))
    inner_or_C = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_C, branch_lt_C)
    inner_disch_C = DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_C)
    th_C = DISJ_CASES(s10, branch_eq_C, inner_disch_C)
    goal_C = DISCH(mk_lt(mk_add(x, z), mk_add(y, z)), th_C)

    return GEN(x, GEN(y, GEN(z, CONJ(goal_A, CONJ(goal_B, goal_C)))))

SATZ_20 = _prove_satz_20()


# ---------------------------------------------------------------------------
# Theorem 33.   Same template as Theorem 20, with multiplication.
#   |- !x y z. (xz > yz ==> x > y) /\ (xz = yz ==> x = y) /\ (xz < yz ==> x < y).
# ---------------------------------------------------------------------------

def _prove_satz_33():
    s10 = SPEC(y, SPEC(x, SATZ_10))

    # Reusing the same skeleton with SATZ_32A/B/C in place of SATZ_19A/B/C.
    h_a = ASSUME(mk_gt(mk_mul(x, z), mk_mul(y, z)))
    branch_eq_A = DISCH(mk_eq(x, y),
                        CONTR(mk_gt(x, y),
                              CONTRA_GT_EQ(mk_mul(x, z), mk_mul(y, z), h_a,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32B))),
                                              ASSUME(mk_eq(x, y))))))
    branch_gt_A = DISCH(mk_gt(x, y), ASSUME(mk_gt(x, y)))
    branch_lt_A = DISCH(mk_lt(x, y),
                        CONTR(mk_gt(x, y),
                              CONTRA_LT_GT(mk_mul(x, z), mk_mul(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32C))),
                                              ASSUME(mk_lt(x, y))),
                                           h_a)))
    inner_or_A = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_A, branch_lt_A)
    th_A = DISJ_CASES(s10, branch_eq_A,
                       DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_A))
    goal_A = DISCH(mk_gt(mk_mul(x, z), mk_mul(y, z)), th_A)

    h_b = ASSUME(mk_eq(mk_mul(x, z), mk_mul(y, z)))
    branch_eq_B = DISCH(mk_eq(x, y), ASSUME(mk_eq(x, y)))
    branch_gt_B = DISCH(mk_gt(x, y),
                        CONTR(mk_eq(x, y),
                              CONTRA_GT_EQ(mk_mul(x, z), mk_mul(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32A))),
                                              ASSUME(mk_gt(x, y))), h_b)))
    branch_lt_B = DISCH(mk_lt(x, y),
                        CONTR(mk_eq(x, y),
                              CONTRA_LT_EQ(mk_mul(x, z), mk_mul(y, z),
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32C))),
                                              ASSUME(mk_lt(x, y))), h_b)))
    inner_or_B = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_B, branch_lt_B)
    th_B = DISJ_CASES(s10, branch_eq_B,
                       DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_B))
    goal_B = DISCH(mk_eq(mk_mul(x, z), mk_mul(y, z)), th_B)

    h_c = ASSUME(mk_lt(mk_mul(x, z), mk_mul(y, z)))
    branch_eq_C = DISCH(mk_eq(x, y),
                        CONTR(mk_lt(x, y),
                              CONTRA_LT_EQ(mk_mul(x, z), mk_mul(y, z), h_c,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32B))),
                                              ASSUME(mk_eq(x, y))))))
    branch_gt_C = DISCH(mk_gt(x, y),
                        CONTR(mk_lt(x, y),
                              CONTRA_LT_GT(mk_mul(x, z), mk_mul(y, z), h_c,
                                           MP(SPEC(z, SPEC(y, SPEC(x, SATZ_32A))),
                                              ASSUME(mk_gt(x, y))))))
    branch_lt_C = DISCH(mk_lt(x, y), ASSUME(mk_lt(x, y)))
    inner_or_C = DISJ_CASES(ASSUME(mk_or(mk_gt(x, y), mk_lt(x, y))),
                             branch_gt_C, branch_lt_C)
    th_C = DISJ_CASES(s10, branch_eq_C,
                       DISCH(mk_or(mk_gt(x, y), mk_lt(x, y)), inner_or_C))
    goal_C = DISCH(mk_lt(mk_mul(x, z), mk_mul(y, z)), th_C)

    return GEN(x, GEN(y, GEN(z, CONJ(goal_A, CONJ(goal_B, goal_C)))))

SATZ_33 = _prove_satz_33()


if __name__ == "__main__":
    print("Step 1 OK -- Peano signature and Axioms 2–5 installed.")
    print("  AXIOM_3   :", pp_thm(AXIOM_3))
    print("  AXIOM_4   :", pp_thm(AXIOM_4))
    print("  INDUCTION :", pp_thm(INDUCTION))
    print("Step 2 OK -- derived inference rules verified by self-tests.")
    print("Step 3 OK -- Theorem 1 proved.")
    print("  SATZ_1    :", pp_thm(SATZ_1))
    print("Step 4 OK -- Theorem 2 proved.")
    print("  SATZ_2    :", pp_thm(SATZ_2))
    print("Step 5 OK -- Theorem 3 proved.")
    print("  SATZ_3    :", pp_thm(SATZ_3))
    print("Step 6 OK -- Definition 1 (addition) installed.")
    print("  ADD_1     :", pp_thm(ADD_1))
    print("  ADD_SUC   :", pp_thm(ADD_SUC))
    print("Step 7 OK -- Theorem 5 (associativity of addition) proved.")
    print("  SATZ_5    :", pp_thm(SATZ_5))
    print("Step 8 OK -- Theorem 6 (commutativity of addition) proved.")
    print("  ONE_PLUS  :", pp_thm(ONE_PLUS))
    print("  SUC_PLUS  :", pp_thm(SUC_PLUS))
    print("  SATZ_6    :", pp_thm(SATZ_6))
    print("Step 9 OK -- Theorem 7 proved.")
    print("  SATZ_7    :", pp_thm(SATZ_7))
    print("Step 10 OK -- Theorem 8 proved.")
    print("  SATZ_8    :", pp_thm(SATZ_8))
    print("Step 11 OK -- Theorem 9 (existence half of trichotomy) proved.")
    print("  LEMMA_PRED:", pp_thm(LEMMA_PRED))
    print("  SATZ_9    :", pp_thm(SATZ_9))
    print("Step 12 OK -- Definitions 2-3 + Theorems 10, 11, 12 proved.")
    print("  SATZ_10   :", pp_thm(SATZ_10))
    print("  SATZ_11   :", pp_thm(SATZ_11))
    print("  SATZ_12   :", pp_thm(SATZ_12))
    print("Step 13 OK -- Definitions 4-5 + Theorems 13, 14 proved.")
    print("  SATZ_13   :", pp_thm(SATZ_13))
    print("  SATZ_14   :", pp_thm(SATZ_14))
    print("Step 14 OK -- Theorem 15 (Transitivity).")
    print("  SATZ_15   :", pp_thm(SATZ_15))
    print("Step 15 OK -- Theorems 16, 17 proved.")
    print("  SATZ_16A  :", pp_thm(SATZ_16A))
    print("  SATZ_16B  :", pp_thm(SATZ_16B))
    print("  SATZ_17   :", pp_thm(SATZ_17))
    print("Step 16 OK -- Theorems 18, 19, 21, 22, 23 proved.")
    print("  SATZ_18   :", pp_thm(SATZ_18))
    print("  SATZ_19A  :", pp_thm(SATZ_19A))
    print("  SATZ_19B  :", pp_thm(SATZ_19B))
    print("  SATZ_19C  :", pp_thm(SATZ_19C))
    print("  SATZ_21   :", pp_thm(SATZ_21))
    print("  SATZ_22A  :", pp_thm(SATZ_22A))
    print("  SATZ_22B  :", pp_thm(SATZ_22B))
    print("  SATZ_23   :", pp_thm(SATZ_23))
    print("Step 17 OK -- Theorems 24, 25, 26 proved.")
    print("  SATZ_24   :", pp_thm(SATZ_24))
    print("  SATZ_25   :", pp_thm(SATZ_25))
    print("  SATZ_26   :", pp_thm(SATZ_26))
    print("Step 18 OK -- Definition 6 + Theorems 29-36 proved (Theorem 28 = Definition 6).")
    print("  ONE_MUL   :", pp_thm(ONE_MUL))
    print("  SUC_MUL   :", pp_thm(SUC_MUL))
    print("  SATZ_29   :", pp_thm(SATZ_29))
    print("  SATZ_30   :", pp_thm(SATZ_30))
    print("  SATZ_31   :", pp_thm(SATZ_31))
    print("  SATZ_32A  :", pp_thm(SATZ_32A))
    print("  SATZ_32B  :", pp_thm(SATZ_32B))
    print("  SATZ_32C  :", pp_thm(SATZ_32C))
    print("  SATZ_34   :", pp_thm(SATZ_34))
    print("  SATZ_35A  :", pp_thm(SATZ_35A))
    print("  SATZ_35B  :", pp_thm(SATZ_35B))
    print("  SATZ_36   :", pp_thm(SATZ_36))
    print("Step 19 OK -- mutual exclusion (Theorem 9 part A) and Theorems 20, 33.")
    print("  SATZ_9_EXCL:", pp_thm(SATZ_9_EXCL))
    print("  SATZ_20    :", pp_thm(SATZ_20))
    print("  SATZ_33    :", pp_thm(SATZ_33))
    print("Step 20 OK -- excluded middle + Theorem 27 (well-ordering).")
    print("  SATZ_27    :", pp_thm(SATZ_27))
