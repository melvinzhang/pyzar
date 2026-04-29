"""Peano signature and induction.

Defines the natural-number type `num` as the inductive subset of `ind`
generated from a fixed base point IND_1 closed under a fixed one-to-one
non-onto function IND_SUC (carved out of `ind` via INFINITY_AX).  From this
construction the three Peano axioms (distinctness of successors, injectivity,
induction) are *derived* as theorems, not admitted.  The convenience rule
`INDUCT` (which packages Axiom 5 for Landau-style proofs) and the primitive
recursion theorem `NUM_RECURSION` follow.

Mirrors `nums.ml` from HOL Light.
"""

from fusion import (
    Var, Abs, Comb,
    aty, bty, bool_ty, mk_abs, mk_comb, mk_const, mk_eq, mk_fun_ty,
    mk_type, new_constant, new_type,
    new_basic_definition, new_basic_type_definition,
    rator, rand, dest_eq, type_of,
    REFL, TRANS, MK_COMB, ABS, ASSUME, EQ_MP, INST, INST_TYPE, HolError,
)
from axioms import (
    SELECT_AX, INFINITY_AX, ONE_ONE_DEF, ONTO_DEF,
    ind_ty,
    mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)
from logic import (
    AP_TERM, AP_THM, BETA_CONV, BETA_NORM, SYM, SPEC, GEN,
    CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP, EXISTS,
    PROVE_HYP, ELIM_EX, NOT_ELIM, NOT_INTRO, CONTR,
    NOT_FORALL_TO_EX_NOT, NOT_EX_TO_FORALL_NOT, NE_SYM,
)


# ---------------------------------------------------------------------------
# Step 1.  Extract IND_SUC : ind->ind from INFINITY_AX.
#
#   INFINITY_AX : |- ?f. ONE_ONE f /\ ~(ONTO f).
#   IND_SUC := @f. ONE_ONE f /\ ~(ONTO f).
# ---------------------------------------------------------------------------

_ind_ind = mk_fun_ty(ind_ty, ind_ty)
_one_one_ind = mk_const("ONE_ONE", [(ind_ty, aty), (ind_ty, bty)])
_onto_ind    = mk_const("ONTO",    [(ind_ty, aty), (ind_ty, bty)])

_f_ii = Var("f", _ind_ind)
_INFTY_PRED = mk_abs(_f_ii,
    mk_and(mk_comb(_one_one_ind, _f_ii),
           mk_not(mk_comb(_onto_ind, _f_ii))))   # \f. ONE_ONE f /\ ~(ONTO f)

_select_ii = mk_const("@", [(_ind_ind, aty)])

IND_SUC_DEF = new_basic_definition(
    mk_eq(Var("IND_SUC", _ind_ind),
          mk_comb(_select_ii, _INFTY_PRED)))     # |- IND_SUC = @(\f. ONE_ONE f /\ ~ONTO f)
IND_SUC = mk_const("IND_SUC", [])


def _prove_ind_suc_props():
    """ Returns (ONE_ONE IND_SUC, ~(ONTO IND_SUC)). """
    # SELECT_AX[ind->ind, with predicate _INFTY_PRED, witnessed by INFINITY_AX]
    # First unfold the existential of INFINITY_AX into its predicate form.
    # INFINITY_AX : ?f. ONE_ONE f /\ ~(ONTO f).
    # Use ELIM_EX to obtain {INFINITY_AX_concl} |- ONE_ONE w /\ ~(ONTO w)
    # where w = @(\f. ...).  But the witness emitted by ELIM_EX is exactly
    # @(\f. ONE_ONE f /\ ~ONTO f) = IND_SUC (after unfolding IND_SUC_DEF).
    pred = _INFTY_PRED
    hyp_ex = INFINITY_AX._concl

    def body_fn(th_at_w):
        # th_at_w : {body_at_w} |- ONE_ONE w /\ ~(ONTO w)   where w = @pred
        return th_at_w

    th_at_w = ELIM_EX(pred, hyp_ex, body_fn)         # {hyp_ex} |- ONE_ONE w /\ ~(ONTO w)
    th_at_w = PROVE_HYP(INFINITY_AX, th_at_w)        # |- ONE_ONE w /\ ~(ONTO w)

    # Now rewrite w (= @pred) into IND_SUC using SYM(IND_SUC_DEF).
    # th_at_w mentions w syntactically as `Comb(@, pred)`. SYM(IND_SUC_DEF)
    # is `|- @pred = IND_SUC`. We rewrite by AP_TERM through both conjuncts.
    sel_eq_indsuc = SYM(IND_SUC_DEF)              # |- @pred = IND_SUC
    # ONE_ONE @pred = ONE_ONE IND_SUC
    one_one_eq = AP_TERM(_one_one_ind, sel_eq_indsuc)
    # ONTO @pred = ONTO IND_SUC
    onto_eq    = AP_TERM(_onto_ind, sel_eq_indsuc)
    # ~(ONTO @pred) = ~(ONTO IND_SUC)
    NOT_C = mk_const("~", [])
    not_onto_eq = AP_TERM(NOT_C, onto_eq)
    # combined equality on conjunction:
    AND_C = mk_const("/\\", [])
    conj_eq = MK_COMB(AP_TERM(AND_C, one_one_eq), not_onto_eq)
    # rewrite th_at_w using conj_eq.
    th_at_indsuc = EQ_MP(conj_eq, th_at_w)        # |- ONE_ONE IND_SUC /\ ~(ONTO IND_SUC)
    return CONJUNCT1(th_at_indsuc), CONJUNCT2(th_at_indsuc)


ONE_ONE_IND_SUC, NOT_ONTO_IND_SUC = _prove_ind_suc_props()


# ---------------------------------------------------------------------------
# Step 2.  Extract IND_1 : ind such that  !x. ~(IND_SUC x = IND_1).
#
#   ~ONTO IND_SUC      gives, after unfolding ONTO,   ~(!y. ?x. y = IND_SUC x).
#   classically:                                   ?y. ~(?x. y = IND_SUC x)
#                                                  ?y. !x. ~(y = IND_SUC x)
#                                       hence       ?y. !x. ~(IND_SUC x = y).
#   IND_1 := @z. !x. ~(IND_SUC x = z).
# ---------------------------------------------------------------------------

_x_ind = Var("x", ind_ty)
_y_ind = Var("y", ind_ty)
_z_ind = Var("z", ind_ty)


def _prove_exists_witness():
    """ |- ?z. !x. ~(IND_SUC x = z). """
    # Step a: unfold ~(ONTO IND_SUC) using ONTO_DEF.
    # ONTO_DEF : |- ONTO = \f. !y. ?x. y = f x   (polymorphic).  Instantiate at ind->ind.
    onto_def_ind = INST_TYPE([(ind_ty, aty), (ind_ty, bty)], ONTO_DEF)
    # AP_THM at IND_SUC:  |- ONTO IND_SUC = (\f. ...) IND_SUC.
    eq1 = AP_THM(onto_def_ind, IND_SUC)
    # BETA-reduce the RHS to the unfolded body.
    eq2 = TRANS(eq1, BETA_CONV(rand(eq1._concl)))   # |- ONTO IND_SUC = !y. ?x. y = IND_SUC x
    # Negate both sides:
    NOT_C = mk_const("~", [])
    not_eq = AP_TERM(NOT_C, eq2)                     # |- ~(ONTO IND_SUC) = ~(!y. ?x. y = IND_SUC x)
    not_forall = EQ_MP(not_eq, NOT_ONTO_IND_SUC)     # |- ~(!y. ?x. y = IND_SUC x)

    # Step b: NOT_FORALL_TO_EX_NOT to get ?y. ~(?x. y = IND_SUC x).
    inner_pred = mk_abs(_y_ind,
                    mk_exists(_x_ind, mk_eq(_y_ind, mk_comb(IND_SUC, _x_ind))))
    ex_not = NOT_FORALL_TO_EX_NOT(not_forall, inner_pred)
    # ex_not : |- ?y. ~(?x. y = IND_SUC x)

    # Step c: For each y in scope, convert ~(?x. y = IND_SUC x) to !x. ~(y = IND_SUC x)
    # via NOT_EX_TO_FORALL_NOT, then to !x. ~(IND_SUC x = y) by NE_SYM.
    # We use ELIM_EX: pull out the witness y from ex_not, do the conversion,
    # then re-EXISTS over z.
    ex_pred_outer = mk_abs(_y_ind,
                       mk_not(mk_exists(_x_ind, mk_eq(_y_ind, mk_comb(IND_SUC, _x_ind)))))

    def body_fn(th_at_y):
        # th_at_y : {body_at_y} |- ~(?x. y' = IND_SUC x)  with y' = @ex_pred_outer.
        # The witness here is @ex_pred_outer, but we keep using `_y_ind` symbolically:
        # ELIM_EX substitutes via vsubst, so th_at_y uses the actual witness term.
        # We use NOT_EX_TO_FORALL_NOT with pred = \x. y' = IND_SUC x.
        # Recover y' from the structure of th_at_y._concl.
        # th_at_y._concl  = ~(?x. y' = IND_SUC x).
        not_ex_term = th_at_y._concl
        ex_term = rand(not_ex_term)              # ?x. y' = IND_SUC x
        ex_pred = rand(ex_term)                  # \x. y' = IND_SUC x  (Abs)
        # Apply NOT_EX_TO_FORALL_NOT.
        forall_not = NOT_EX_TO_FORALL_NOT(th_at_y, ex_pred)
        # forall_not : |- !x. ~(y' = IND_SUC x)
        # Now rewrite each instance via NE_SYM under GEN.
        spec_x = SPEC(_x_ind, forall_not)        # |- ~(y' = IND_SUC x)
        sym_x  = NE_SYM(spec_x)                  # |- ~(IND_SUC x = y')
        forall_swapped = GEN(_x_ind, sym_x)      # |- !x. ~(IND_SUC x = y')
        # Existentially introduce z over y'.
        # Pred:  \z. !x. ~(IND_SUC x = z)
        target_pred = mk_abs(_z_ind,
                          mk_forall(_x_ind,
                              mk_not(mk_eq(mk_comb(IND_SUC, _x_ind), _z_ind))))
        # The witness is the actual y' inside th_at_y, which is dest_eq's lhs of
        # an inner equality. Recover it from forall_swapped's body.
        # forall_swapped._concl = !x. ~(IND_SUC x = y'). Extract y' from inside:
        body_forall = rand(forall_swapped._concl)  # \x. ~(IND_SUC x = y')
        # The body of the inner Abs has the form ~(IND_SUC x = y').
        not_eq_inside = body_forall.body          # ~(IND_SUC x = y')
        eq_inside = rand(not_eq_inside)            # IND_SUC x = y'
        y_witness = rand(eq_inside)                # y'
        return EXISTS(target_pred, y_witness, forall_swapped)

    final = ELIM_EX(ex_pred_outer, ex_not._concl, body_fn)
    final = PROVE_HYP(ex_not, final)
    return final


_EXISTS_WITNESS = _prove_exists_witness()  # |- ?z. !x. ~(IND_SUC x = z)


# Define IND_1 = @z. !x. ~(IND_SUC x = z).
_select_ind = mk_const("@", [(ind_ty, aty)])
_witness_pred = mk_abs(_z_ind,
                   mk_forall(_x_ind,
                       mk_not(mk_eq(mk_comb(IND_SUC, _x_ind), _z_ind))))
IND_1_DEF = new_basic_definition(
    mk_eq(Var("IND_1", ind_ty), mk_comb(_select_ind, _witness_pred)))
IND_1 = mk_const("IND_1", [])


def _prove_ind_suc_neq_ind_1():
    """ |- !x. ~(IND_SUC x = IND_1). """
    # SELECT_AX gives:  P x ==> P (@P).  Specialise at _witness_pred.
    sel_inst = INST_TYPE([(ind_ty, aty)], SELECT_AX)
    sel_pq = SPEC(_z_ind, SPEC(_witness_pred, sel_inst))
    # |- _witness_pred z ==> _witness_pred (@_witness_pred)
    # Pull the existential body via ELIM_EX.
    def body_fn(th_at_z):
        # th_at_z : {body_at_z} |- !x. ~(IND_SUC x = z')   where z' = @_witness_pred
        return th_at_z

    raw = ELIM_EX(_witness_pred, _EXISTS_WITNESS._concl, body_fn)
    raw = PROVE_HYP(_EXISTS_WITNESS, raw)
    # raw : |- !x. ~(IND_SUC x = w)   where w = @_witness_pred.
    # Rewrite w to IND_1 using SYM(IND_1_DEF).
    sel_eq_ind1 = SYM(IND_1_DEF)                  # |- @_witness_pred = IND_1
    # The conclusion of `raw` is `!x. ~(IND_SUC x = w)`.  We need to substitute
    # w by IND_1 inside the equation `IND_SUC x = w`.  Build the abstraction
    # `\w. !x. ~(IND_SUC x = w)`, AP_TERM to sel_eq_ind1, and EQ_MP raw.
    w_var = Var("w", ind_ty)
    big_pred = mk_abs(w_var,
                  mk_forall(_x_ind,
                      mk_not(mk_eq(mk_comb(IND_SUC, _x_ind), w_var))))
    # |- (\w. !x. ~(IND_SUC x = w)) (@_witness_pred) = (\w. ...) IND_1
    func_eq = AP_TERM(big_pred, sel_eq_ind1)
    # Beta-normalise both sides.
    func_eq_norm_lhs = BETA_CONV(mk_comb(big_pred, mk_comb(_select_ind, _witness_pred)))
    func_eq_norm_rhs = BETA_CONV(mk_comb(big_pred, IND_1))
    # |- (\w. ...) (@_witness_pred) = !x. ~(IND_SUC x = @_witness_pred)
    # |- (\w. ...) IND_1 = !x. ~(IND_SUC x = IND_1)
    bridge = TRANS(SYM(func_eq_norm_lhs), TRANS(func_eq, func_eq_norm_rhs))
    # bridge : |- !x. ~(IND_SUC x = w) = !x. ~(IND_SUC x = IND_1)
    return EQ_MP(bridge, raw)


IND_SUC_NEQ_IND_1 = _prove_ind_suc_neq_ind_1()  # |- !x. ~(IND_SUC x = IND_1)


# ---------------------------------------------------------------------------
# Step 3.  Define the inductive predicate NUM_REP on ind.
#
#   NUM_REP a := !P. P IND_1 /\ (!i. P i ==> P (IND_SUC i)) ==> P a.
# ---------------------------------------------------------------------------

_a_ind  = Var("a", ind_ty)
_i_ind  = Var("i", ind_ty)
_P_ind  = Var("P", mk_fun_ty(ind_ty, bool_ty))

NUM_REP_DEF = new_basic_definition(
    mk_eq(Var("NUM_REP", mk_fun_ty(ind_ty, bool_ty)),
          mk_abs(_a_ind,
              mk_forall(_P_ind,
                  mk_imp(
                      mk_and(mk_comb(_P_ind, IND_1),
                             mk_forall(_i_ind,
                                 mk_imp(mk_comb(_P_ind, _i_ind),
                                        mk_comb(_P_ind, mk_comb(IND_SUC, _i_ind))))),
                      mk_comb(_P_ind, _a_ind))))))
NUM_REP = mk_const("NUM_REP", [])


def _NUM_REP_unfold(a_term):
    r""" |- NUM_REP a = (!P. P IND_1 /\ (!i. P i ==> P (IND_SUC i)) ==> P a). """
    # AP_THM NUM_REP_DEF a, then BETA.
    eq = AP_THM(NUM_REP_DEF, a_term)
    return TRANS(eq, BETA_CONV(rand(eq._concl)))


# ---------------------------------------------------------------------------
# Step 4.  Witness existence:  |- ?a. NUM_REP a.   (witness: IND_1.)
# ---------------------------------------------------------------------------

def _prove_NUM_REP_IND_1():
    """ |- NUM_REP IND_1. """
    # Goal: !P. (P IND_1 /\ closure) ==> P IND_1.
    P_IND_1 = mk_comb(_P_ind, IND_1)
    closure = mk_forall(_i_ind,
                  mk_imp(mk_comb(_P_ind, _i_ind),
                         mk_comb(_P_ind, mk_comb(IND_SUC, _i_ind))))
    big_hyp = mk_and(P_IND_1, closure)
    h = ASSUME(big_hyp)
    th = CONJUNCT1(h)                                  # {hyp} |- P IND_1
    inner = GEN(_P_ind, DISCH(big_hyp, th))            # |- !P. hyp ==> P IND_1
    # Re-fold via NUM_REP_unfold reversed.
    eq = _NUM_REP_unfold(IND_1)                        # |- NUM_REP IND_1 = !P. ...
    return EQ_MP(SYM(eq), inner)


NUM_REP_IND_1 = _prove_NUM_REP_IND_1()


def _prove_NUM_REP_IND_SUC():
    """ |- !i. NUM_REP i ==> NUM_REP (IND_SUC i). """
    # Assume NUM_REP i. Show NUM_REP (IND_SUC i):
    #   for any P, hyp = P IND_1 /\ closure(P).  Then closure gives P i ==> P(IND_SUC i),
    #   and NUM_REP i applied at P + hyp gives P i, hence P (IND_SUC i).
    NR_i = mk_comb(NUM_REP, _i_ind)
    NR_si = mk_comb(NUM_REP, mk_comb(IND_SUC, _i_ind))
    h_NRi = ASSUME(NR_i)
    # Goal: !P. (P IND_1 /\ closure) ==> P (IND_SUC i).
    P_IND_1 = mk_comb(_P_ind, IND_1)
    closure = mk_forall(_i_ind,
                  mk_imp(mk_comb(_P_ind, _i_ind),
                         mk_comb(_P_ind, mk_comb(IND_SUC, _i_ind))))
    big_hyp = mk_and(P_IND_1, closure)
    h_hyp = ASSUME(big_hyp)
    # Convert h_NRi to its unfolded form: !P. hyp ==> P i.
    eq_unfold_i = _NUM_REP_unfold(_i_ind)
    h_NRi_unfold = EQ_MP(eq_unfold_i, h_NRi)
    # SPEC at P, MP at h_hyp.
    P_i = MP(SPEC(_P_ind, h_NRi_unfold), h_hyp)        # {NR_i, hyp} |- P i
    # Closure: !i. P i ==> P (IND_SUC i).
    cl = CONJUNCT2(h_hyp)
    cl_at_i = SPEC(_i_ind, cl)                          # {hyp} |- P i ==> P (IND_SUC i)
    P_si = MP(cl_at_i, P_i)                             # {NR_i, hyp} |- P (IND_SUC i)
    inner = GEN(_P_ind, DISCH(big_hyp, P_si))           # {NR_i} |- !P. hyp ==> P (IND_SUC i)
    eq_unfold_si = _NUM_REP_unfold(mk_comb(IND_SUC, _i_ind))
    NR_si_th = EQ_MP(SYM(eq_unfold_si), inner)          # {NR_i} |- NUM_REP (IND_SUC i)
    return GEN(_i_ind, DISCH(NR_i, NR_si_th))


NUM_REP_IND_SUC_CLOSED = _prove_NUM_REP_IND_SUC()  # |- !i. NUM_REP i ==> NUM_REP (IND_SUC i)


_EXISTS_NUM_REP = EXISTS(mk_abs(_a_ind, mk_comb(NUM_REP, _a_ind)),
                         IND_1, NUM_REP_IND_1)        # |- ?a. (\a. NUM_REP a) a
# Strictly: EXISTS produces `?a. (\a. NUM_REP a) a`; but new_basic_type_definition
# wants `|- P x` with P being the predicate.  We must ensure the predicate is
# closed and equals (\a. NUM_REP a).  The conclusion of EXISTS already has the
# right shape: `(\a. NUM_REP a) IND_1` -> we need to BETA-reduce.  Actually
# new_basic_type_definition reads `P = fun, x = arg` from the Comb, so passing
# `(\a. NUM_REP a) IND_1` is fine -- the predicate becomes `\a. NUM_REP a`.

# However, for cleanliness we want `NUM_REP IND_1` directly as the existence
# theorem -- but new_basic_type_definition will then take P = NUM_REP and
# x = IND_1, which requires P closed; NUM_REP is a constant, so it has no free
# vars, perfect.  Use NUM_REP_IND_1 directly.


# ---------------------------------------------------------------------------
# Step 5.  Carve out `num` as a subtype of `ind`.
# ---------------------------------------------------------------------------

MK_DEST, DEST_MK = new_basic_type_definition(
    "num", ("mk_num", "dest_num"), NUM_REP_IND_1)
# MK_DEST : |- mk_num (dest_num a) = a              (a : num)
# DEST_MK : |- NUM_REP r = (dest_num (mk_num r) = r) (r : ind)

num_ty = mk_type("num", [])
mk_num = mk_const("mk_num", [])
dest_num = mk_const("dest_num", [])


# ---------------------------------------------------------------------------
# Step 6.  Define the constants `1` and `SUC` on num.
#
#   1 = mk_num IND_1.
#   SUC = \n:num. mk_num (IND_SUC (dest_num n)).
# ---------------------------------------------------------------------------

ONE_DEF = new_basic_definition(
    mk_eq(Var("1", num_ty), mk_comb(mk_num, IND_1)))
ONE = mk_const("1", [])

_n_num = Var("n", num_ty)
SUC_DEF = new_basic_definition(
    mk_eq(Var("SUC", mk_fun_ty(num_ty, num_ty)),
          mk_abs(_n_num,
              mk_comb(mk_num,
                  mk_comb(IND_SUC, mk_comb(dest_num, _n_num))))))
SUC = mk_const("SUC", [])


def mk_suc(t):
    return mk_comb(SUC, t)


def _SUC_unfold(n_term):
    """ |- SUC n = mk_num (IND_SUC (dest_num n)). """
    eq = AP_THM(SUC_DEF, n_term)
    return TRANS(eq, BETA_CONV(rand(eq._concl)))


# Standard variable names re-used throughout the arithmetic development.
x = Var("x", num_ty)
y = Var("y", num_ty)
z = Var("z", num_ty)
u = Var("u", num_ty)
v = Var("v", num_ty)
w = Var("w", num_ty)
P = Var("P", mk_fun_ty(num_ty, bool_ty))


# ---------------------------------------------------------------------------
# Step 7.  Lemma: |- !n:num. NUM_REP (dest_num n).
#
#   Strategy: from MK_DEST a:    mk_num (dest_num a) = a.
#   Apply dest_num:               dest_num (mk_num (dest_num a)) = dest_num a.
#   Use DEST_MK at r := dest_num a:
#                                  NUM_REP (dest_num a)
#                                = (dest_num (mk_num (dest_num a)) = dest_num a).
#   The RHS holds; EQ_MP backwards yields NUM_REP (dest_num a).
# ---------------------------------------------------------------------------

def _prove_NUM_REP_dest_num():
    """ |- !n. NUM_REP (dest_num n). """
    a_var = Var("a", num_ty)                           # the bound variable for GEN
    # MK_DEST_a : |- mk_num (dest_num a) = a.  But MK_DEST has bound var `a`.
    # Already in MK_DEST.  We INST nothing; just SPEC-like access.
    # MK_DEST itself is `|- mk_num (dest_num a) = a`, where a is the free Var.
    # Inspect its concl to grab the right Var name.
    # Per new_basic_type_definition: a = Var("a", num_ty).
    # Apply dest_num to both sides:
    md = MK_DEST                                        # |- mk_num (dest_num a) = a
    md_dest = AP_TERM(dest_num, md)                     # |- dest_num (mk_num (dest_num a)) = dest_num a
    # DEST_MK : |- NUM_REP r = (dest_num (mk_num r) = r), where r = Var("r", ind_ty).
    # INST r := dest_num a in DEST_MK.
    r_var = Var("r", ind_ty)
    da = mk_comb(dest_num, a_var)                       # dest_num a
    dm_inst = INST([(da, r_var)], DEST_MK)              # |- NUM_REP (dest_num a) = (dest_num (mk_num (dest_num a)) = dest_num a)
    NR_da = EQ_MP(SYM(dm_inst), md_dest)                # |- NUM_REP (dest_num a)
    return GEN(a_var, NR_da)


NUM_REP_dest_num = _prove_NUM_REP_dest_num()


# ---------------------------------------------------------------------------
# Step 8.  Working facts about ONE_ONE and ONTO unfolded at IND_SUC.
# ---------------------------------------------------------------------------

def _ONE_ONE_unfold_at_IND_SUC():
    """ |- ONE_ONE IND_SUC = !x1 x2. IND_SUC x1 = IND_SUC x2 ==> x1 = x2. """
    one_one_def_ind = INST_TYPE([(ind_ty, aty), (ind_ty, bty)], ONE_ONE_DEF)
    eq1 = AP_THM(one_one_def_ind, IND_SUC)
    return TRANS(eq1, BETA_CONV(rand(eq1._concl)))


_ONE_ONE_IND_SUC_unfold = EQ_MP(_ONE_ONE_unfold_at_IND_SUC(), ONE_ONE_IND_SUC)
# _ONE_ONE_IND_SUC_unfold : |- !x1 x2. IND_SUC x1 = IND_SUC x2 ==> x1 = x2


# ---------------------------------------------------------------------------
# Step 9.  Prove AXIOM_3 :  |- !x. ~(SUC x = 1).
# ---------------------------------------------------------------------------

def _prove_AXIOM_3():
    """ |- !x. ~(SUC x = 1). """
    # Assume SUC x = 1.  By SUC_DEF and ONE_DEF, this is
    #   mk_num (IND_SUC (dest_num x)) = mk_num IND_1.
    h_eq = ASSUME(mk_eq(mk_suc(x), ONE))                       # {SUC x = 1} |- SUC x = 1
    # Replace SUC x and 1 by their definitions on each side.
    SUC_x_eq = _SUC_unfold(x)                                  # |- SUC x = mk_num (IND_SUC (dest_num x))
    h_unfold = TRANS(SYM(SUC_x_eq), TRANS(h_eq, ONE_DEF))      # {SUC x = 1} |- mk_num (IND_SUC (dest_num x)) = mk_num IND_1
    # Apply dest_num to both sides:
    h_dest = AP_TERM(dest_num, h_unfold)                       # {SUC x = 1} |- dest_num (mk_num (IND_SUC (dest_num x))) = dest_num (mk_num IND_1)
    # Peel via DEST_MK at IND_SUC (dest_num x) and at IND_1 (using NUM_REP closure).
    # First: NUM_REP IND_1.  And NUM_REP (IND_SUC (dest_num x)).
    NR_dx = SPEC(x, NUM_REP_dest_num)                          # |- NUM_REP (dest_num x)
    NR_si_dx = MP(SPEC(mk_comb(dest_num, x), NUM_REP_IND_SUC_CLOSED), NR_dx)
    # NR_si_dx : |- NUM_REP (IND_SUC (dest_num x))
    # DEST_MK at r := IND_SUC (dest_num x):
    r_var = Var("r", ind_ty)
    s_dx = mk_comb(IND_SUC, mk_comb(dest_num, x))
    dm_at_sdx = INST([(s_dx, r_var)], DEST_MK)                 # |- NUM_REP (IND_SUC (dest_num x)) = (dest_num (mk_num (IND_SUC (dest_num x))) = IND_SUC (dest_num x))
    eq_lhs_peel = EQ_MP(dm_at_sdx, NR_si_dx)                   # |- dest_num (mk_num (IND_SUC (dest_num x))) = IND_SUC (dest_num x)
    # DEST_MK at r := IND_1:
    dm_at_ind1 = INST([(IND_1, r_var)], DEST_MK)               # |- NUM_REP IND_1 = (dest_num (mk_num IND_1) = IND_1)
    eq_rhs_peel = EQ_MP(dm_at_ind1, NUM_REP_IND_1)             # |- dest_num (mk_num IND_1) = IND_1
    # Combine:  IND_SUC (dest_num x) = dest_num (mk_num (IND_SUC (dest_num x))) = dest_num (mk_num IND_1) = IND_1.
    h_peel = TRANS(SYM(eq_lhs_peel), TRANS(h_dest, eq_rhs_peel))
    # h_peel : {SUC x = 1} |- IND_SUC (dest_num x) = IND_1
    # Contradicts IND_SUC_NEQ_IND_1 specialized to dest_num x.
    neq_at_dx = SPEC(mk_comb(dest_num, x), IND_SUC_NEQ_IND_1)  # |- ~(IND_SUC (dest_num x) = IND_1)
    th_F = MP(NOT_ELIM(neq_at_dx), h_peel)                     # {SUC x = 1} |- F
    th_disch = NOT_INTRO(DISCH(mk_eq(mk_suc(x), ONE), th_F))   # |- ~(SUC x = 1)
    return GEN(x, th_disch)


AXIOM_3 = _prove_AXIOM_3()


# ---------------------------------------------------------------------------
# Step 10.  Prove AXIOM_4 :  |- !x y. SUC x = SUC y ==> x = y.
# ---------------------------------------------------------------------------

def _prove_AXIOM_4():
    """ |- !x y. SUC x = SUC y ==> x = y. """
    h_eq = ASSUME(mk_eq(mk_suc(x), mk_suc(y)))                 # {SUC x = SUC y} |- ...
    SUC_x_eq = _SUC_unfold(x)                                  # |- SUC x = mk_num (IND_SUC (dest_num x))
    SUC_y_eq = _SUC_unfold(y)                                  # |- SUC y = mk_num (IND_SUC (dest_num y))
    h_unfold = TRANS(SYM(SUC_x_eq), TRANS(h_eq, SUC_y_eq))     # {...} |- mk_num (IND_SUC (dx)) = mk_num (IND_SUC (dy))
    # Apply dest_num.
    h_dest = AP_TERM(dest_num, h_unfold)                       # |- dest_num (mk_num (IND_SUC (dx))) = dest_num (mk_num (IND_SUC (dy)))
    # Peel via DEST_MK using NUM_REP closure for both sides.
    r_var = Var("r", ind_ty)
    NR_dx = SPEC(x, NUM_REP_dest_num)
    NR_dy = SPEC(y, NUM_REP_dest_num)
    NR_si_dx = MP(SPEC(mk_comb(dest_num, x), NUM_REP_IND_SUC_CLOSED), NR_dx)
    NR_si_dy = MP(SPEC(mk_comb(dest_num, y), NUM_REP_IND_SUC_CLOSED), NR_dy)
    s_dx = mk_comb(IND_SUC, mk_comb(dest_num, x))
    s_dy = mk_comb(IND_SUC, mk_comb(dest_num, y))
    eq_dx_peel = EQ_MP(INST([(s_dx, r_var)], DEST_MK), NR_si_dx)
    eq_dy_peel = EQ_MP(INST([(s_dy, r_var)], DEST_MK), NR_si_dy)
    # eq_dx_peel : |- dest_num (mk_num (IND_SUC (dx))) = IND_SUC (dx)
    # eq_dy_peel : |- dest_num (mk_num (IND_SUC (dy))) = IND_SUC (dy)
    h_peeled = TRANS(SYM(eq_dx_peel), TRANS(h_dest, eq_dy_peel))
    # h_peeled : {SUC x = SUC y} |- IND_SUC (dx) = IND_SUC (dy)
    # Use ONE_ONE IND_SUC.
    oo = SPEC(mk_comb(dest_num, y),
              SPEC(mk_comb(dest_num, x), _ONE_ONE_IND_SUC_unfold))
    # oo : |- IND_SUC (dx) = IND_SUC (dy) ==> dx = dy.
    dx_eq_dy = MP(oo, h_peeled)                                # {SUC x = SUC y} |- dx = dy
    # Apply mk_num:  mk_num (dx) = mk_num (dy).
    mk_app = AP_TERM(mk_num, dx_eq_dy)                         # {...} |- mk_num (dx) = mk_num (dy)
    # MK_DEST gives mk_num (dest_num x) = x  for any num x.
    # MK_DEST has the form: |- mk_num (dest_num a) = a where a is a Var of type num.
    a_var = Var("a", num_ty)
    md_x = INST([(x, a_var)], MK_DEST)                          # |- mk_num (dest_num x) = x
    md_y = INST([(y, a_var)], MK_DEST)                          # |- mk_num (dest_num y) = y
    x_eq_y = TRANS(SYM(md_x), TRANS(mk_app, md_y))              # {SUC x = SUC y} |- x = y
    return GEN(x, GEN(y, DISCH(mk_eq(mk_suc(x), mk_suc(y)), x_eq_y)))


AXIOM_4 = _prove_AXIOM_4()


# ---------------------------------------------------------------------------
# Step 11.  Prove INDUCTION :  |- !P. P 1 /\ (!x. P x ==> P (SUC x)) ==> !x. P x.
#
# Strategy:  Define Q i := NUM_REP i /\ P (mk_num i)  on ind.
#            Show Q IND_1   and  !i. Q i ==> Q (IND_SUC i).
#            For any num a, NUM_REP_dest_num gives NUM_REP (dest_num a);
#            apply NUM_REP at Q to obtain Q (dest_num a),
#            hence P (mk_num (dest_num a)) = P a (via MK_DEST).
# ---------------------------------------------------------------------------

def _prove_INDUCTION():
    r""" |- !P. P 1 /\ (!x. P x ==> P (SUC x)) ==> !x. P x. """
    base_term = mk_comb(P, ONE)
    step_term = mk_forall(x,
                    mk_imp(mk_comb(P, x),
                           mk_comb(P, mk_suc(x))))
    big_hyp = mk_and(base_term, step_term)
    h = ASSUME(big_hyp)
    base_th = CONJUNCT1(h)                       # {hyp} |- P 1
    step_th = CONJUNCT2(h)                       # {hyp} |- !x. P x ==> P (SUC x)

    # Build Q = \i:ind. NUM_REP i /\ P (mk_num i).
    NR_i = mk_comb(NUM_REP, _i_ind)
    P_mki = mk_comb(P, mk_comb(mk_num, _i_ind))
    Q_body = mk_and(NR_i, P_mki)
    Q_lam = mk_abs(_i_ind, Q_body)

    def Q_unfold(i_term):
        r""" |- Q i = NUM_REP i /\ P (mk_num i)  (with i_term substituted). """
        return BETA_CONV(mk_comb(Q_lam, i_term))

    # ----- Q IND_1. -----
    # NUM_REP IND_1 : NUM_REP_IND_1.
    # P (mk_num IND_1) = P 1  via SYM(ONE_DEF) under AP_TERM P.
    one_eq_mki1 = SYM(ONE_DEF)                           # |- mk_num IND_1 = 1   actually wait:
    # ONE_DEF : |- 1 = mk_num IND_1.  SYM(ONE_DEF) : |- mk_num IND_1 = 1.
    # We have base_th : P 1; we need P (mk_num IND_1).
    # AP_TERM P on ONE_DEF:  |- P 1 = P (mk_num IND_1).
    P_eq = AP_TERM(P, ONE_DEF)                           # |- P 1 = P (mk_num IND_1)
    P_mk_ind1 = EQ_MP(P_eq, base_th)                     # {hyp} |- P (mk_num IND_1)
    Q_at_IND_1_inner = CONJ(NUM_REP_IND_1, P_mk_ind1)    # {hyp} |- NUM_REP IND_1 /\ P (mk_num IND_1)
    Q_at_IND_1 = EQ_MP(SYM(Q_unfold(IND_1)), Q_at_IND_1_inner)   # {hyp} |- Q IND_1

    # ----- !i. Q i ==> Q (IND_SUC i). -----
    h_Qi = ASSUME(mk_comb(Q_lam, _i_ind))                # {Q i} |- Q i
    Qi_inner = EQ_MP(Q_unfold(_i_ind), h_Qi)             # {Q i} |- NUM_REP i /\ P (mk_num i)
    NR_i_th = CONJUNCT1(Qi_inner)
    P_mki_th = CONJUNCT2(Qi_inner)
    # NUM_REP (IND_SUC i):
    NR_si_th = MP(SPEC(_i_ind, NUM_REP_IND_SUC_CLOSED), NR_i_th)   # {Q i} |- NUM_REP (IND_SUC i)
    # P (mk_num (IND_SUC i)) :
    # SUC (mk_num i) by SUC_DEF = mk_num (IND_SUC (dest_num (mk_num i))).
    # By DEST_MK with NR_i_th: dest_num (mk_num i) = i.
    r_var = Var("r", ind_ty)
    dm_at_i = INST([(_i_ind, r_var)], DEST_MK)           # |- NUM_REP i = (dest_num (mk_num i) = i)
    di_eq_i = EQ_MP(dm_at_i, NR_i_th)                    # {Q i} |- dest_num (mk_num i) = i
    # IND_SUC applied:
    isdi_eq_isi = AP_TERM(IND_SUC, di_eq_i)              # {Q i} |- IND_SUC (dest_num (mk_num i)) = IND_SUC i
    # mk_num applied:
    mki_si = AP_TERM(mk_num, isdi_eq_isi)                # {Q i} |- mk_num (IND_SUC (dest_num (mk_num i))) = mk_num (IND_SUC i)
    # SUC_DEF unfolded at (mk_num i):  SUC (mk_num i) = mk_num (IND_SUC (dest_num (mk_num i))).
    suc_mk_i_eq = _SUC_unfold(mk_comb(mk_num, _i_ind))
    # |- SUC (mk_num i) = mk_num (IND_SUC (dest_num (mk_num i)))
    # Combine: SUC (mk_num i) = mk_num (IND_SUC i).
    SUC_mki_eq_mk_si = TRANS(suc_mk_i_eq, mki_si)        # {Q i} |- SUC (mk_num i) = mk_num (IND_SUC i)
    # From step_th: !x. P x ==> P (SUC x).
    step_at_mki = SPEC(mk_comb(mk_num, _i_ind), step_th) # {hyp} |- P (mk_num i) ==> P (SUC (mk_num i))
    P_SUC_mki = MP(step_at_mki, P_mki_th)                # {hyp, Q i} |- P (SUC (mk_num i))
    # Rewrite:  P (SUC (mk_num i)) = P (mk_num (IND_SUC i)).
    P_eq2 = AP_TERM(P, SUC_mki_eq_mk_si)                 # {Q i} |- P (SUC (mk_num i)) = P (mk_num (IND_SUC i))
    P_mk_si = EQ_MP(P_eq2, P_SUC_mki)                    # {hyp, Q i} |- P (mk_num (IND_SUC i))
    # Combine to get Q (IND_SUC i) inner.
    Q_si_inner = CONJ(NR_si_th, P_mk_si)                 # {hyp, Q i} |- NUM_REP (IND_SUC i) /\ P (mk_num (IND_SUC i))
    Q_si = EQ_MP(SYM(Q_unfold(mk_comb(IND_SUC, _i_ind))), Q_si_inner)   # {hyp, Q i} |- Q (IND_SUC i)
    Q_step_imp = DISCH(mk_comb(Q_lam, _i_ind), Q_si)     # {hyp} |- Q i ==> Q (IND_SUC i)
    Q_step_all = GEN(_i_ind, Q_step_imp)                 # {hyp} |- !i. Q i ==> Q (IND_SUC i)

    # Combine for NUM_REP usage:
    Q_closure = CONJ(Q_at_IND_1, Q_step_all)             # {hyp} |- Q IND_1 /\ (!i. Q i ==> Q (IND_SUC i))

    # Now for any num a:  NUM_REP_dest_num gives NUM_REP (dest_num a);
    # NUM_REP unfolded and instantiated at Q gives Q (dest_num a).
    NR_da = SPEC(x, NUM_REP_dest_num)                    # |- NUM_REP (dest_num x)
    da = mk_comb(dest_num, x)                            # dest_num x
    eq_unfold_da = _NUM_REP_unfold(da)                   # |- NUM_REP (dest_num x) = !P. ... ==> P (dest_num x)
    NR_da_unfold = EQ_MP(eq_unfold_da, NR_da)            # |- !P. ... ==> P (dest_num x)
    # SPEC at Q_lam.
    NR_da_at_Q = SPEC(Q_lam, NR_da_unfold)               # |- (Q IND_1 /\ closure(Q)) ==> Q (dest_num x)
    Q_at_da = MP(NR_da_at_Q, Q_closure)                  # {hyp} |- Q (dest_num x)
    # Unfold:
    Q_at_da_inner = EQ_MP(Q_unfold(da), Q_at_da)         # {hyp} |- NUM_REP (dest_num x) /\ P (mk_num (dest_num x))
    P_mk_dx = CONJUNCT2(Q_at_da_inner)                   # {hyp} |- P (mk_num (dest_num x))
    # MK_DEST: mk_num (dest_num x) = x.
    a_var = Var("a", num_ty)
    md_x = INST([(x, a_var)], MK_DEST)                   # |- mk_num (dest_num x) = x
    P_eq3 = AP_TERM(P, md_x)                             # |- P (mk_num (dest_num x)) = P x
    P_x = EQ_MP(P_eq3, P_mk_dx)                          # {hyp} |- P x

    forall_x = GEN(x, P_x)                               # {hyp} |- !x. P x
    return GEN(P, DISCH(big_hyp, forall_x))


INDUCTION = _prove_INDUCTION()


# ---------------------------------------------------------------------------
# Induction helper -- packages Axiom 5 for Landau-style proofs.
#
# Given a predicate  pred = \v. body[v]  and theorems
#       base_th : |- body[1/v]
#       step_th : |- !v. body[v] ==> body[v'/v]
# returns           |- !v. body[v].
# ---------------------------------------------------------------------------

def INDUCT(pred, base_th, step_th):
    if not isinstance(pred, Abs):
        raise HolError("INDUCT: pred must be an Abs")
    v_var = pred.bvar
    pred_1  = mk_comb(pred, ONE)
    pred_v  = mk_comb(pred, v_var)
    pred_vs = mk_comb(pred, mk_suc(v_var))
    base_pred = EQ_MP(SYM(BETA_CONV(pred_1)), base_th)
    inst_step    = SPEC(v_var, step_th)
    body_assume  = EQ_MP(BETA_CONV(pred_v), ASSUME(pred_v))
    body_succ    = MP(inst_step, body_assume)
    pred_vs_th   = EQ_MP(SYM(BETA_CONV(pred_vs)), body_succ)
    step_pred    = GEN(v_var, DISCH(pred_v, pred_vs_th))
    ind_inst     = SPEC(pred, INDUCTION)
    forall_pred  = MP(ind_inst, CONJ(base_pred, step_pred))
    body_th = EQ_MP(BETA_CONV(pred_v), SPEC(v_var, forall_pred))
    return GEN(v_var, body_th)


# ---------------------------------------------------------------------------
# INDUCT_PROVE -- high-level induction template.
#
#   var      : induction variable
#   body     : term mentioning `var` (the predicate body at var)
#   base     : |- body[var := 1]
#   step_fn  : callback receiving IH = ASSUME(body) and returning a theorem
#              of body[var := SUC var]  (using IH if needed).
#   Result   : |- !var. body.
# ---------------------------------------------------------------------------

def INDUCT_PROVE(var, body, base, step_fn):
    pred = mk_abs(var, body)
    IH = ASSUME(body)
    step_inner = step_fn(IH)
    step = GEN(var, DISCH(body, step_inner))
    return INDUCT(pred, base, step)


# ---------------------------------------------------------------------------
# Primitive recursion theorem.
#
#   |- !c:A h:num->A->A. ?fn:num->A. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
#
# Strategy: define the inductive graph
#     R c h n m  :=  !Q. (Q 1 c /\ (!k a. Q k a ==> Q (SUC k) (h k a))) ==> Q n m
# and prove by induction on n that  ?!m. R c h n m.  Then  fn := \n. @m. R c h n m
# satisfies the recursion equations.
# ---------------------------------------------------------------------------

# Standard variable names used in the recursion proof (live at type variable A
# so the final theorem is polymorphic).
_A = aty
_num_to_A     = mk_fun_ty(num_ty, _A)
_A_to_A       = mk_fun_ty(_A, _A)
_h_ty         = mk_fun_ty(num_ty, _A_to_A)
_Q_ty         = mk_fun_ty(num_ty, mk_fun_ty(_A, bool_ty))

_c   = Var("c", _A)
_h   = Var("h", _h_ty)
_n   = Var("n", num_ty)
_k   = Var("k", num_ty)
_m   = Var("m", _A)
_a   = Var("a", _A)
_b   = Var("b", _A)
_m1  = Var("m1", _A)
_m2  = Var("m2", _A)
_Q   = Var("Q", _Q_ty)
_fn  = Var("fn", _num_to_A)


def _mk_closure_hyp(Q_term, c_term, h_term):
    """Build the term  Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))."""
    Q_1_c   = mk_comb(mk_comb(Q_term, ONE), c_term)
    h_k_a   = mk_comb(mk_comb(h_term, _k), _a)
    Q_k_a   = mk_comb(mk_comb(Q_term, _k), _a)
    Q_sk_h  = mk_comb(mk_comb(Q_term, mk_suc(_k)), h_k_a)
    closure = mk_forall(_k, mk_forall(_a, mk_imp(Q_k_a, Q_sk_h)))
    return mk_and(Q_1_c, closure)


def _mk_R(c_term, h_term, n_term, m_term):
    """Build R c h n m as  !Q. (Q 1 c /\\ closure) ==> Q n m."""
    hyp = _mk_closure_hyp(_Q, c_term, h_term)
    Q_n_m = mk_comb(mk_comb(_Q, n_term), m_term)
    return mk_forall(_Q, mk_imp(hyp, Q_n_m))


def _prove_R_at_1():
    """ |- R c h 1 c    (with c, h as free variables). """
    hyp = _mk_closure_hyp(_Q, _c, _h)
    h_th = ASSUME(hyp)                            # {hyp} |- hyp
    Q_1_c = CONJUNCT1(h_th)                       # {hyp} |- Q 1 c
    return GEN(_Q, DISCH(hyp, Q_1_c))             # |- !Q. hyp ==> Q 1 c

R_AT_1 = _prove_R_at_1()


def _prove_R_step():
    """ |- !n m. R c h n m ==> R c h (SUC n) (h n m). """
    R_n_m = _mk_R(_c, _h, _n, _m)
    h_n_m = mk_comb(mk_comb(_h, _n), _m)
    hyp = _mk_closure_hyp(_Q, _c, _h)

    th_R = ASSUME(R_n_m)                          # {R} |- R c h n m
    th_hyp = ASSUME(hyp)                          # {hyp} |- Q 1 c /\ closure
    R_at_Q = SPEC(_Q, th_R)                       # {R} |- hyp ==> Q n m
    Q_n_m = MP(R_at_Q, th_hyp)                    # {R, hyp} |- Q n m

    closure_th = CONJUNCT2(th_hyp)                # {hyp} |- !k a. Q k a ==> Q (SUC k) (h k a)
    closure_at_nm = SPEC(_m, SPEC(_n, closure_th))   # {hyp} |- Q n m ==> Q (SUC n) (h n m)
    Q_sn = MP(closure_at_nm, Q_n_m)               # {R, hyp} |- Q (SUC n) (h n m)

    inner = GEN(_Q, DISCH(hyp, Q_sn))             # {R} |- R c h (SUC n) (h n m)
    return GEN(_n, GEN(_m, DISCH(R_n_m, inner)))

R_STEP = _prove_R_step()


def _mk_unique_at(n_term):
    """Build  (?m. R c h n m) /\\ (!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2)."""
    R_n_m  = _mk_R(_c, _h, n_term, _m)
    R_n_m1 = _mk_R(_c, _h, n_term, _m1)
    R_n_m2 = _mk_R(_c, _h, n_term, _m2)
    exist  = mk_exists(_m, R_n_m)
    unique = mk_forall(_m1, mk_forall(_m2,
                mk_imp(mk_and(R_n_m1, R_n_m2), mk_eq(_m1, _m2))))
    return mk_and(exist, unique)


def _prove_R_unique_base():
    """ |- (?m. R c h 1 m) /\\ (!m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2). """
    R_1_m   = _mk_R(_c, _h, ONE, _m)
    R_1_m1  = _mk_R(_c, _h, ONE, _m1)
    R_1_m2  = _mk_R(_c, _h, ONE, _m2)

    # Existence: witness m = c, using Lemma 1.
    exist_th = EXISTS(mk_abs(_m, R_1_m), _c, R_AT_1)   # |- ?m. R c h 1 m

    # Uniqueness: define Q'(k, a) := (k = 1) ==> (a = c).
    # We will show Q' satisfies the closure hypothesis, then specialise R c h 1 _ at Q'.
    Qp_body = mk_imp(mk_eq(_k, ONE), mk_eq(_a, _c))     # using free k, a; but Q' has type num->A->bool
    # Actually the bound vars in Q' are independent: Q' = \k:num. \a:A. (k = 1) ==> (a = c)
    k_b = Var("k", num_ty)
    a_b = Var("a", _A)
    Qp = mk_abs(k_b, mk_abs(a_b, mk_imp(mk_eq(k_b, ONE), mk_eq(a_b, _c))))

    def apply_Qp(k_t, a_t):
        """Return (|- Q' k a = (k = 1 ==> a = c), the equality from beta)."""
        # Q' k a beta-reduces to (k = 1) ==> (a = c).
        Qp_k = mk_comb(Qp, k_t)
        bot1 = BETA_CONV(Qp_k)                   # |- Q' k = \a. ...
        Qp_k_a = mk_comb(Qp_k, a_t)
        bot2 = AP_THM(bot1, a_t)                 # |- Q' k a = (\a. ...) a
        bot3 = TRANS(bot2, BETA_CONV(rand(bot2._concl)))
        return bot3                              # |- Q' k a = (k = 1 ==> a = c)

    # 1. Q' 1 c.   reduces to (1 = 1) ==> (c = c), proved by DISCH+REFL.
    eq_red_1c = apply_Qp(ONE, _c)
    inner_1c = DISCH(mk_eq(ONE, ONE), REFL(_c))   # |- (1 = 1) ==> (c = c)
    Qp_1_c = EQ_MP(SYM(eq_red_1c), inner_1c)      # |- Q' 1 c

    # 2. !k a. Q' k a ==> Q' (SUC k) (h k a).   Body: SUC k = 1 ==> h k a = c.
    # Vacuous: SUC k != 1 by AXIOM_3, so the hypothesis SUC k = 1 leads to F, hence anything.
    h_k_a = mk_comb(mk_comb(_h, _k), _a)
    eq_red_LHS = apply_Qp(_k, _a)                          # |- Q' k a = (k=1 ==> a=c)
    eq_red_RHS = apply_Qp(mk_suc(_k), h_k_a)               # |- Q' (SUC k) (h k a) = (SUC k=1 ==> h k a=c)
    # Inner: SUC k = 1 ==> h k a = c.   Use AXIOM_3 specialized to k.
    ax3_k = SPEC(_k, AXIOM_3)                              # |- ~(SUC k = 1)
    # NOT_ELIM gives  |- (SUC k = 1) ==> F.
    from logic import NOT_ELIM, CONTR
    sk_eq_1_imp_F = NOT_ELIM(ax3_k)                        # |- (SUC k = 1) ==> F
    # |- (SUC k = 1) ==> (h k a = c):  apply CONTR.
    h_sk_eq_1 = ASSUME(mk_eq(mk_suc(_k), ONE))             # {SUC k = 1} |- SUC k = 1
    th_F = MP(sk_eq_1_imp_F, h_sk_eq_1)                    # {SUC k = 1} |- F
    th_hkc = CONTR(mk_eq(h_k_a, _c), th_F)                 # {SUC k = 1} |- h k a = c
    inner_step = DISCH(mk_eq(mk_suc(_k), ONE), th_hkc)     # |- (SUC k = 1) ==> (h k a = c)
    # Lift through eq_red_RHS:
    Qp_sk_hka = EQ_MP(SYM(eq_red_RHS), inner_step)         # |- Q' (SUC k) (h k a)
    # Build  Q' k a ==> Q' (SUC k) (h k a):  the antecedent is ignored (RHS holds).
    Qp_k_a_term = rand(eq_red_LHS._concl).fun.arg   # not actually needed, but for clarity
    Qp_k_a_term = mk_comb(mk_comb(Qp, _k), _a)
    step_imp = DISCH(Qp_k_a_term, Qp_sk_hka)               # |- Q' k a ==> Q' (SUC k) (h k a)
    closure_Qp = GEN(_k, GEN(_a, step_imp))                # |- !k a. Q' k a ==> Q' (SUC k) (h k a)

    closure_hyp_Qp = CONJ(Qp_1_c, closure_Qp)              # |- (Q' 1 c) /\ closure(Q')

    # Now derive uniqueness:  R c h 1 m1 /\ R c h 1 m2 ==> m1 = m2.
    h_R_m1 = ASSUME(R_1_m1)                                # {R 1 m1} |- ...
    h_R_m2 = ASSUME(R_1_m2)
    R_at_Qp_m1 = SPEC(Qp, h_R_m1)                          # {R 1 m1} |- (Q' 1 c /\ closure) ==> Q' 1 m1
    Qp_1_m1 = MP(R_at_Qp_m1, closure_hyp_Qp)               # {R 1 m1} |- Q' 1 m1
    # Convert via  Q' 1 m1 = ((1 = 1) ==> (m1 = c)).
    eq_red_1m1 = apply_Qp(ONE, _m1)
    inner_1m1 = EQ_MP(eq_red_1m1, Qp_1_m1)                 # {R 1 m1} |- (1=1) ==> (m1 = c)
    m1_eq_c = MP(inner_1m1, REFL(ONE))                     # {R 1 m1} |- m1 = c
    # Same for m2.
    R_at_Qp_m2 = SPEC(Qp, h_R_m2)
    Qp_1_m2 = MP(R_at_Qp_m2, closure_hyp_Qp)
    eq_red_1m2 = apply_Qp(ONE, _m2)
    inner_1m2 = EQ_MP(eq_red_1m2, Qp_1_m2)
    m2_eq_c = MP(inner_1m2, REFL(ONE))                     # {R 1 m2} |- m2 = c
    # Combine:  m1 = c = m2.
    m1_eq_m2 = TRANS(m1_eq_c, SYM(m2_eq_c))                # {R 1 m1, R 1 m2} |- m1 = m2

    # Discharge into  (R 1 m1 /\ R 1 m2) ==> m1 = m2.
    conj_h = ASSUME(mk_and(R_1_m1, R_1_m2))
    use_conj = MP(MP(DISCH(R_1_m1, DISCH(R_1_m2, m1_eq_m2)),
                     CONJUNCT1(conj_h)), CONJUNCT2(conj_h))
    unique_th = GEN(_m1, GEN(_m2,
                    DISCH(mk_and(R_1_m1, R_1_m2), use_conj)))

    return CONJ(exist_th, unique_th)

R_UNIQUE_BASE = _prove_R_unique_base()


def _prove_R_unique_step():
    """ |- !n. _mk_unique_at(n) ==> _mk_unique_at(SUC n). """
    R_n_m   = _mk_R(_c, _h, _n, _m)
    pred_R_n = mk_abs(_m, R_n_m)             # \m. R c h n m

    IH_term = _mk_unique_at(_n)               # IH at n
    IH = ASSUME(IH_term)
    IH_exist  = CONJUNCT1(IH)                 # {IH} |- ?m. R c h n m
    IH_unique = CONJUNCT2(IH)                 # {IH} |- !m1 m2. R c h n m1 /\ R c h n m2 ==> m1 = m2

    # Witness: m_n = @m. R c h n m.
    sel_const = mk_const("@", [(_A, aty)])
    m_n = mk_comb(sel_const, pred_R_n)        # @m. R c h n m

    # We'll build target := _mk_unique_at(SUC n)  under hypothesis {IH, ...},
    # using ELIM_EX to introduce a hypothesis  R c h n m_n.
    R_n_mn = _mk_R(_c, _h, _n, m_n)           # R c h n m_n

    # ----- Existence at SUC n. -----
    # From R c h n m_n  (hypothesis), R_STEP gives R c h (SUC n) (h n m_n).
    h_n_mn = mk_comb(mk_comb(_h, _n), m_n)
    R_step_inst = SPEC(m_n, SPEC(_n, R_STEP))                 # |- R c h n m_n ==> R c h (SUC n) (h n m_n)
    R_sn_hn = MP(R_step_inst, ASSUME(R_n_mn))                  # {R_n_mn} |- R c h (SUC n) (h n m_n)

    R_sn_m = _mk_R(_c, _h, mk_suc(_n), _m)
    pred_R_sn = mk_abs(_m, R_sn_m)
    exist_sn = EXISTS(pred_R_sn, h_n_mn, R_sn_hn)              # {R_n_mn} |- ?m. R c h (SUC n) m

    # ----- Uniqueness at SUC n. -----
    # Define  Q'(k, b) := R c h k b /\ (k = SUC n ==> b = h n m_n).
    k_b = Var("k", num_ty)
    a_b = Var("a", _A)
    Qp_body = mk_and(_mk_R(_c, _h, k_b, a_b),
                      mk_imp(mk_eq(k_b, mk_suc(_n)),
                             mk_eq(a_b, h_n_mn)))
    Qp = mk_abs(k_b, mk_abs(a_b, Qp_body))

    def apply_Qp(k_t, a_t):
        r"""Return |- Q' k a = (R c h k a /\ (k = SUC n ==> a = h n m_n))."""
        Qp_k = mk_comb(Qp, k_t)
        bot1 = BETA_CONV(Qp_k)                # |- Q' k = \a. ...
        Qp_k_a = mk_comb(Qp_k, a_t)
        bot2 = AP_THM(bot1, a_t)
        bot3 = TRANS(bot2, BETA_CONV(rand(bot2._concl)))
        return bot3                            # |- Q' k a = body[k_t, a_t]

    # 1. Q'(1, c).  We need:
    #    R c h 1 c    /\    (1 = SUC n ==> c = h n m_n).
    Qp_1c_eq = apply_Qp(ONE, _c)               # |- Q' 1 c = (R c h 1 c /\ (1 = SUC n ==> c = h n m_n))
    R_1_c = R_AT_1                              # |- R c h 1 c
    # second conjunct: (1 = SUC n ==> c = h n m_n).  Vacuous via AXIOM_3 (SUC n != 1 i.e. ~(1 = SUC n)? -- direction: AXIOM_3 has SUC n != 1).
    # Assume 1 = SUC n.  SYM gives SUC n = 1.  AXIOM_3 says ~(SUC n = 1).  Contradiction.
    h_1_eq_sn = ASSUME(mk_eq(ONE, mk_suc(_n)))           # {1 = SUC n} |- 1 = SUC n
    sn_eq_1 = SYM(h_1_eq_sn)                              # {1 = SUC n} |- SUC n = 1
    ax3_n = SPEC(_n, AXIOM_3)                             # |- ~(SUC n = 1)
    th_F_1 = MP(NOT_ELIM(ax3_n), sn_eq_1)                  # {1 = SUC n} |- F
    th_c_eq_hnmn = CONTR(mk_eq(_c, h_n_mn), th_F_1)        # {1 = SUC n} |- c = h n m_n
    inner_1c = DISCH(mk_eq(ONE, mk_suc(_n)), th_c_eq_hnmn)   # |- 1 = SUC n ==> c = h n m_n
    Qp_1_c_inner = CONJ(R_1_c, inner_1c)                   # |- R c h 1 c /\ (1 = SUC n ==> c = h n m_n)
    Qp_1_c = EQ_MP(SYM(Qp_1c_eq), Qp_1_c_inner)            # |- Q' 1 c

    # 2. !k a. Q' k a ==> Q' (SUC k) (h k a).
    h_k_a = mk_comb(mk_comb(_h, _k), _a)
    Qp_k_a_eq = apply_Qp(_k, _a)                                  # |- Q' k a = (R c h k a /\ (k = SUC n ==> a = h n m_n))
    Qp_sk_hka_eq = apply_Qp(mk_suc(_k), h_k_a)                    # |- Q' (SUC k) (h k a) = (R c h (SUC k) (h k a) /\ ...)

    # Assume Q' k a.  Get R c h k a and (k = SUC n ==> a = h n m_n).
    Qp_k_a = mk_comb(mk_comb(Qp, _k), _a)
    h_Qp_ka = ASSUME(Qp_k_a)
    inner_Qp = EQ_MP(Qp_k_a_eq, h_Qp_ka)                          # {Qp_k_a} |- R k a /\ (k = SUC n ==> a = h n m_n)
    R_k_a = CONJUNCT1(inner_Qp)                                   # {Qp_k_a} |- R c h k a
    second_part = CONJUNCT2(inner_Qp)                              # {Qp_k_a} |- k = SUC n ==> a = h n m_n

    # First conjunct of Q' (SUC k) (h k a): R c h (SUC k) (h k a).
    R_step_at_ka = SPEC(_a, SPEC(_k, R_STEP))                      # |- R c h k a ==> R c h (SUC k) (h k a)
    R_sk_hka = MP(R_step_at_ka, R_k_a)                              # {Qp_k_a} |- R c h (SUC k) (h k a)

    # Second conjunct: (SUC k = SUC n ==> h k a = h n m_n).
    # Assume SUC k = SUC n. By AXIOM_4, k = n.
    h_sk_eq_sn = ASSUME(mk_eq(mk_suc(_k), mk_suc(_n)))             # {SUC k = SUC n} |- SUC k = SUC n
    ax4_kn = SPEC(_n, SPEC(_k, AXIOM_4))                            # |- SUC k = SUC n ==> k = n
    k_eq_n = MP(ax4_kn, h_sk_eq_sn)                                 # {SUC k = SUC n} |- k = n

    # Now from R_k_a (= R c h k a) plus k = n, get R c h n a (rewrite k to n).
    # AP rewriting: substitute k=n in R c h k a.  Use AP_THM/AP_TERM at the relation level.
    # Easier: use AP_TERM on the function form `\k. R c h k a` applied to k=n.
    # But R c h k a contains k.  Let's do it by congruence:
    #   R c h k a = R c h n a   from k = n.
    # The shape: R c h k a = (!Q. (...) ==> Q k a).  We need to rewrite k inside.
    # Build the abstraction \kk. R c h kk a, then AP_TERM to k_eq_n.
    kk = Var("kk", num_ty)
    R_func_a = mk_abs(kk, _mk_R(_c, _h, kk, _a))                    # \kk. R c h kk a
    # |- (\kk. R c h kk a) k = R c h k a
    beta_at_k = BETA_CONV(mk_comb(R_func_a, _k))
    beta_at_n = BETA_CONV(mk_comb(R_func_a, _n))
    # AP_TERM applied to k_eq_n gives:  |- (\kk. R c h kk a) k = (\kk. R c h kk a) n.
    func_eq = AP_TERM(R_func_a, k_eq_n)                              # {SUC k = SUC n} |- (\kk. R c h kk a) k = (\kk. R c h kk a) n
    # Combine:  R c h k a = (\kk. R k a) k = (\kk. R k a) n = R c h n a.
    R_k_eq_R_n = TRANS(SYM(beta_at_k), TRANS(func_eq, beta_at_n))    # {SUC k = SUC n} |- R c h k a = R c h n a
    R_n_a = EQ_MP(R_k_eq_R_n, R_k_a)                                  # {Qp_k_a, SUC k = SUC n} |- R c h n a

    # Now apply IH_unique at (a, m_n): R c h n a /\ R c h n m_n ==> a = m_n.
    IH_at_a_mn = SPEC(m_n, SPEC(_a, IH_unique))                       # {IH} |- R n a /\ R n m_n ==> a = m_n
    R_n_mn_h = ASSUME(R_n_mn)                                          # {R_n_mn} |- R c h n m_n
    a_eq_mn = MP(IH_at_a_mn, CONJ(R_n_a, R_n_mn_h))                    # {Qp_k_a, SUC k = SUC n, IH, R_n_mn} |- a = m_n

    # Now h k a = h n m_n.  Use AP_TERM/AP_THM on h.
    # h k a = h n a   (from k = n via AP_THM(AP_TERM h k_eq_n) ).
    # Then h n a = h n m_n via AP_TERM(h n) on a_eq_mn.
    h_k_eq_h_n = AP_TERM(_h, k_eq_n)                                   # {SUC k = SUC n} |- h k = h n
    h_k_a_eq_h_n_a = AP_THM(h_k_eq_h_n, _a)                            # {SUC k = SUC n} |- h k a = h n a
    h_n_a_eq_h_n_mn = AP_TERM(mk_comb(_h, _n), a_eq_mn)                # {Qp_k_a, SUC k=SUC n, IH, R_n_mn} |- h n a = h n m_n
    h_k_a_eq_h_n_mn = TRANS(h_k_a_eq_h_n_a, h_n_a_eq_h_n_mn)            # ditto |- h k a = h n m_n

    second_imp_inner = DISCH(mk_eq(mk_suc(_k), mk_suc(_n)), h_k_a_eq_h_n_mn)   # {Qp_k_a, IH, R_n_mn} |- SUC k = SUC n ==> h k a = h n m_n

    Qp_sk_hka_inner = CONJ(R_sk_hka, second_imp_inner)                  # {Qp_k_a, IH, R_n_mn} |- R c h (SUC k) (h k a) /\ (SUC k = SUC n ==> h k a = h n m_n)
    Qp_sk_hka = EQ_MP(SYM(Qp_sk_hka_eq), Qp_sk_hka_inner)               # {...} |- Q' (SUC k) (h k a)

    # Build (Q' k a ==> Q' (SUC k) (h k a)) under {IH, R_n_mn}, then GEN k, a.
    step_imp_Qp = DISCH(Qp_k_a, Qp_sk_hka)                              # {IH, R_n_mn} |- Q' k a ==> Q' (SUC k) (h k a)
    closure_Qp = GEN(_k, GEN(_a, step_imp_Qp))                          # {IH, R_n_mn} |- !k a. Q' k a ==> Q' (SUC k) (h k a)

    closure_hyp_Qp_th = CONJ(Qp_1_c, closure_Qp)                        # {IH, R_n_mn} |- (Q' 1 c) /\ closure(Q')

    # Now assume R c h (SUC n) m1, R c h (SUC n) m2.
    R_sn_m1 = _mk_R(_c, _h, mk_suc(_n), _m1)
    R_sn_m2 = _mk_R(_c, _h, mk_suc(_n), _m2)
    h_R_sn_m1 = ASSUME(R_sn_m1)
    h_R_sn_m2 = ASSUME(R_sn_m2)
    R_at_Qp_m1 = SPEC(Qp, h_R_sn_m1)                                     # {R_sn_m1} |- ((Q' 1 c) /\ closure) ==> Q' (SUC n) m1
    Qp_sn_m1 = MP(R_at_Qp_m1, closure_hyp_Qp_th)                          # {R_sn_m1, IH, R_n_mn} |- Q' (SUC n) m1

    Qp_sn_m1_eq = apply_Qp(mk_suc(_n), _m1)                               # |- Q' (SUC n) m1 = (R (SUC n) m1 /\ (SUC n = SUC n ==> m1 = h n m_n))
    inner_m1 = EQ_MP(Qp_sn_m1_eq, Qp_sn_m1)
    second_m1 = CONJUNCT2(inner_m1)                                       # {...} |- SUC n = SUC n ==> m1 = h n m_n
    m1_eq_hnmn = MP(second_m1, REFL(mk_suc(_n)))                          # {R_sn_m1, IH, R_n_mn} |- m1 = h n m_n

    R_at_Qp_m2 = SPEC(Qp, h_R_sn_m2)
    Qp_sn_m2 = MP(R_at_Qp_m2, closure_hyp_Qp_th)
    Qp_sn_m2_eq = apply_Qp(mk_suc(_n), _m2)
    inner_m2 = EQ_MP(Qp_sn_m2_eq, Qp_sn_m2)
    second_m2 = CONJUNCT2(inner_m2)
    m2_eq_hnmn = MP(second_m2, REFL(mk_suc(_n)))                          # {R_sn_m2, IH, R_n_mn} |- m2 = h n m_n

    m1_eq_m2 = TRANS(m1_eq_hnmn, SYM(m2_eq_hnmn))                          # {R_sn_m1, R_sn_m2, IH, R_n_mn} |- m1 = m2

    # Build  (R_sn_m1 /\ R_sn_m2) ==> m1 = m2:
    conj_h = ASSUME(mk_and(R_sn_m1, R_sn_m2))
    m1_eq_m2_combined = MP(MP(DISCH(R_sn_m1, DISCH(R_sn_m2, m1_eq_m2)),
                                CONJUNCT1(conj_h)),
                            CONJUNCT2(conj_h))
    unique_sn = GEN(_m1, GEN(_m2,
                       DISCH(mk_and(R_sn_m1, R_sn_m2), m1_eq_m2_combined)))
    # unique_sn : {IH, R_n_mn} |- !m1 m2. R c h (SUC n) m1 /\ R c h (SUC n) m2 ==> m1 = m2

    # Combine existence and uniqueness at SUC n.
    combined_sn = CONJ(exist_sn, unique_sn)                                # {IH, R_n_mn} |- _mk_unique_at(SUC n)

    # Now eliminate R_n_mn via ELIM_EX from IH_exist (which is `?m. R c h n m`).
    # Build body_fn such that body_fn(ASSUME(R c h n m_n)) returns combined_sn.
    # The witness via ELIM_EX is `@m. R c h n m` = m_n; so body_v[w/v] = R c h n m_n exactly.
    R_n_pred = pred_R_n   # \m. R c h n m
    # Sanity: BETA_CONV at m_n yields R_n_mn.
    # Also IH_exist is `?m. R c h n m`. So hyp_ex = mk_exists(_m, R_n_m).
    hyp_ex = mk_exists(_m, R_n_m)

    def body_fn(th_R_n_w):
        # th_R_n_w : {R c h n m_n} |- R c h n m_n
        # We want combined_sn but with R_n_mn replaced as a hypothesis.
        # combined_sn already uses ASSUME(R_n_mn), so body_fn(_) effectively is just combined_sn.
        # But we need to replace its ASSUME(R_n_mn) hypothesis with th_R_n_w.
        # PROVE_HYP(th_R_n_w, combined_sn) does this.
        return PROVE_HYP(th_R_n_w, combined_sn)

    # ELIM_EX wraps everything: returns {hyp_ex} ∪ ... |- target.
    combined_under_IH = ELIM_EX(R_n_pred, hyp_ex, body_fn)                  # {hyp_ex, IH} |- combined_sn

    # hyp_ex is exactly IH_exist's conclusion. Discharge it via PROVE_HYP using IH_exist.
    combined_final = PROVE_HYP(IH_exist, combined_under_IH)                  # {IH} |- combined_sn

    return GEN(_n, DISCH(IH_term, combined_final))


R_UNIQUE_STEP = _prove_R_unique_step()


# Now combine via INDUCT to get R_UNIQUE: |- !n. _mk_unique_at(n).
def _prove_R_unique():
    pred = mk_abs(_n, _mk_unique_at(_n))
    return INDUCT(pred, R_UNIQUE_BASE, R_UNIQUE_STEP)

R_UNIQUE = _prove_R_unique()


# ---------------------------------------------------------------------------
# NUM_RECURSION:  |- !c h. ?fn:num->A. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
# ---------------------------------------------------------------------------

def _prove_num_recursion():
    # Define fn := \n. @m. R c h n m.
    # So fn 1 = @m. R c h 1 m.
    # Show fn 1 = c via uniqueness at 1.
    # And fn (SUC n) = h n (fn n) via uniqueness at SUC n combined with R_STEP.
    R_n_m   = _mk_R(_c, _h, _n, _m)
    R_1_m   = _mk_R(_c, _h, ONE, _m)
    pred_R_n = mk_abs(_m, R_n_m)
    pred_R_1 = mk_abs(_m, R_1_m)
    sel_const = mk_const("@", [(_A, aty)])
    fn_body = mk_abs(_n, mk_comb(sel_const, pred_R_n))   # \n. @m. R c h n m

    # fn applied to a term k beta-reduces to @m. R c h k m.
    # Define convenience:
    def fn_app(k_t):
        return mk_comb(fn_body, k_t)

    # Step 1: fn 1 = c.
    # fn 1 beta-reduces to @m. R c h 1 m.
    # By R_UNIQUE specialised at 1, ?m. R c h 1 m  AND uniqueness.
    # Both R_AT_1 and SELECT_AX give R c h 1 (@m. R c h 1 m). Then uniqueness with R_AT_1 gives @m... = c.
    R_unique_1 = SPEC(ONE, R_UNIQUE)                                    # |- ?m. R 1 m /\ uniqueness at 1
    exist_1  = CONJUNCT1(R_unique_1)                                     # |- ?m. R c h 1 m
    unique_1 = CONJUNCT2(R_unique_1)                                     # |- !m1 m2. R 1 m1 /\ R 1 m2 ==> m1 = m2

    # Use SELECT_AX to derive R c h 1 (@m. R 1 m).
    # SELECT_AX: !P x. P x ==> P (@P).
    sel_inst = INST_TYPE([(_A, aty)], SELECT_AX)
    sel_at_pred1 = SPEC(_m, SPEC(pred_R_1, sel_inst))                    # |- pred_R_1 m ==> pred_R_1 (@pred_R_1)
    # Convert to R 1 m ==> R 1 (@pred_R_1) via BETA.
    pred_R_1_at_m = mk_comb(pred_R_1, _m)
    pred_R_1_at_w = mk_comb(pred_R_1, mk_comb(sel_const, pred_R_1))
    body_v = rand(BETA_CONV(pred_R_1_at_m)._concl)   # = R c h 1 m  (with _m free)
    body_at_w = rand(BETA_CONV(pred_R_1_at_w)._concl)  # = R c h 1 (@m. R 1 m)
    th_pred_v = EQ_MP(SYM(BETA_CONV(pred_R_1_at_m)), ASSUME(body_v))     # {body_v} |- pred_R_1 m
    th_pred_w = MP(sel_at_pred1, th_pred_v)                                # {body_v} |- pred_R_1 (@..)
    th_body_at_w = EQ_MP(BETA_CONV(pred_R_1_at_w), th_pred_w)              # {body_v} |- R 1 (@..)

    # Now using ELIM_EX with hyp_ex = exist_1 conclusion to get {exist_1.concl} |- R c h 1 (@m. R 1 m).
    ex_term_1 = exist_1._concl

    def body_fn_1(th):
        # th : {R 1 m_1} |- R 1 m_1 where m_1 = @m. R 1 m and th is body_at_w
        return th
    th_R_1_atP = ELIM_EX(pred_R_1, ex_term_1, body_fn_1)                  # {ex_term_1} |- R c h 1 (@m. R 1 m)
    th_R_1_atP_clean = PROVE_HYP(exist_1, th_R_1_atP)                      # |- R c h 1 (@m. R 1 m)

    # R_AT_1: |- R c h 1 c.  Together with uniqueness at 1, conclude (@m. R 1 m) = c.
    sel_pred_R_1 = mk_comb(sel_const, pred_R_1)                            # @m. R c h 1 m
    unique_at_w_c = SPEC(_c, SPEC(sel_pred_R_1, unique_1))                  # |- R 1 (@..) /\ R 1 c ==> (@..) = c
    sel_eq_c = MP(unique_at_w_c, CONJ(th_R_1_atP_clean, R_AT_1))            # |- (@..) = c

    # fn 1 = (\n. @m. R n m) 1 = @m. R 1 m  via BETA.
    fn_1 = fn_app(ONE)
    beta_fn_1 = BETA_CONV(fn_1)                                              # |- fn 1 = @m. R 1 m
    fn_1_eq_c = TRANS(beta_fn_1, sel_eq_c)                                   # |- fn 1 = c

    # Step 2: !n. fn (SUC n) = h n (fn n).
    # By same trick, we get  R c h k (@m. R c h k m)  for any k (as long as ?m. R c h k m).
    # Specialising R_UNIQUE at _n we get existence and uniqueness at n.
    R_unique_n = SPEC(_n, R_UNIQUE)
    exist_n  = CONJUNCT1(R_unique_n)                                          # |- ?m. R c h n m
    R_unique_sn = SPEC(mk_suc(_n), R_UNIQUE)
    unique_sn = CONJUNCT2(R_unique_sn)                                         # |- !m1 m2. R (SUC n) m1 /\ R (SUC n) m2 ==> m1 = m2

    # Get R c h n (@m. R c h n m) under existence at n.
    ex_term_n = exist_n._concl
    th_R_n_atP = ELIM_EX(pred_R_n, ex_term_n, lambda th: th)                   # {ex_term_n} |- R c h n (@m. R c h n m)
    th_R_n_atP_clean = PROVE_HYP(exist_n, th_R_n_atP)                          # |- R c h n (@m. R n m)

    # R_STEP gives R c h (SUC n) (h n (@m. R n m)).
    sel_pred_R_n = mk_comb(sel_const, pred_R_n)                                # @m. R c h n m  (= fn n after beta)
    h_n_selRn = mk_comb(mk_comb(_h, _n), sel_pred_R_n)
    R_step_at = SPEC(sel_pred_R_n, SPEC(_n, R_STEP))                            # |- R n (@m...) ==> R (SUC n) (h n (@m...))
    R_sn_h_n_sel = MP(R_step_at, th_R_n_atP_clean)                              # |- R (SUC n) (h n (@m. R n m))

    # Also R c h (SUC n) (@m. R c h (SUC n) m) using SELECT_AX.
    pred_R_sn_term = mk_abs(_m, _mk_R(_c, _h, mk_suc(_n), _m))
    exist_sn = CONJUNCT1(R_unique_sn)
    ex_term_sn = exist_sn._concl
    th_R_sn_atP = ELIM_EX(pred_R_sn_term, ex_term_sn, lambda th: th)
    th_R_sn_atP_clean = PROVE_HYP(exist_sn, th_R_sn_atP)                        # |- R (SUC n) (@m. R (SUC n) m)
    sel_pred_R_sn = mk_comb(sel_const, pred_R_sn_term)                           # @m. R c h (SUC n) m  (= fn (SUC n) after beta)

    # Apply uniqueness at SUC n: (@m. R (SUC n) m) = h n (@m. R n m).
    unique_at_sn = SPEC(h_n_selRn, SPEC(sel_pred_R_sn, unique_sn))               # |- R (SUC n) (@m..) /\ R (SUC n) (h n (@m..)) ==> (@m..) = h n (@m..)
    sel_sn_eq_hn = MP(unique_at_sn, CONJ(th_R_sn_atP_clean, R_sn_h_n_sel))
    # sel_sn_eq_hn : |- (@m. R (SUC n) m) = h n (@m. R n m).

    # fn (SUC n) BETA-reduces to (@m. R (SUC n) m).
    fn_sn = fn_app(mk_suc(_n))
    beta_fn_sn = BETA_CONV(fn_sn)                                                # |- fn (SUC n) = @m. R (SUC n) m
    # h n (fn n) = h n (@m. R n m)  via AP_TERM(h n, BETA_CONV(fn n)).
    fn_n = fn_app(_n)
    beta_fn_n = BETA_CONV(fn_n)                                                   # |- fn n = @m. R n m
    h_n_fnn_eq = AP_TERM(mk_comb(_h, _n), beta_fn_n)                              # |- h n (fn n) = h n (@m. R n m)
    # Combine: fn (SUC n) = @m. R (SUC n) m = h n (@m. R n m) = h n (fn n).
    fn_sn_eq_h_n_fnn = TRANS(beta_fn_sn, TRANS(sel_sn_eq_hn, SYM(h_n_fnn_eq)))    # |- fn (SUC n) = h n (fn n)
    forall_n_step = GEN(_n, fn_sn_eq_h_n_fnn)                                      # |- !n. fn (SUC n) = h n (fn n)

    # Combine and existential-introduce fn.
    combined = CONJ(fn_1_eq_c, forall_n_step)                                       # |- fn 1 = c /\ !n. fn (SUC n) = h n (fn n)
    # Build  ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
    # Predicate \fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
    fn_var = _fn
    fn_1_var = mk_comb(fn_var, ONE)
    fn_sn_var = mk_comb(fn_var, mk_suc(_n))
    fn_n_var = mk_comb(fn_var, _n)
    body_pred = mk_and(mk_eq(fn_1_var, _c),
                        mk_forall(_n,
                            mk_eq(fn_sn_var,
                                  mk_comb(mk_comb(_h, _n), fn_n_var))))
    pred_fn = mk_abs(fn_var, body_pred)
    exist_fn = EXISTS(pred_fn, fn_body, combined)                                    # |- ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n)

    return GEN(_c, GEN(_h, exist_fn))


NUM_RECURSION = _prove_num_recursion()


def _selftest_R():
    from logic import pp_thm
    print("R_AT_1:        ", pp_thm(R_AT_1))
    print("R_STEP:        ", pp_thm(R_STEP))
    print("R_UNIQUE_BASE: ", pp_thm(R_UNIQUE_BASE))
    print("R_UNIQUE_STEP: ", pp_thm(R_UNIQUE_STEP))
    print("R_UNIQUE:      ", pp_thm(R_UNIQUE))
    print("NUM_RECURSION: ", pp_thm(NUM_RECURSION))


if __name__ == "__main__":
    _selftest_R()
