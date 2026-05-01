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
from tactics import (
    AP_TERM, AP_THM, BETA_CONV, BETA_NORM, SYM, SPEC, GEN, GENL,
    CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP, EXISTS,
    PROVE_HYP, ELIM_EX, NOT_ELIM, NOT_INTRO, CONTR,
    NE_SYM, TRANS_CHAIN,
    BETA_RULE, REWRITE_RULE,
)
from classical import NOT_FORALL_TO_EX_NOT, NOT_EX_TO_FORALL_NOT
from proof import proof
from parser import DEFAULT_SIG, parse


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
    eq2 = BETA_RULE(eq1)                             # |- ONTO IND_SUC = !y. ?x. y = IND_SUC x
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
    bridge = TRANS_CHAIN([SYM(func_eq_norm_lhs), func_eq, func_eq_norm_rhs])
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
    return BETA_RULE(AP_THM(NUM_REP_DEF, a_term))


# Register surface syntax for the ind-typed kernel constants we've built so
# far. Without these, @proof blocks below cannot mention IND_1, IND_SUC or
# NUM_REP by name. (Per-proof type annotations still cover ind-typed bound
# variables, since `num` isn't yet the default var type.)
DEFAULT_SIG.add_type("ind", ind_ty)
DEFAULT_SIG.add_const("IND_1", IND_1)
DEFAULT_SIG.add_const("IND_SUC", IND_SUC)
DEFAULT_SIG.add_const("NUM_REP", NUM_REP)
_P_ind_ty = mk_fun_ty(ind_ty, bool_ty)


# ---------------------------------------------------------------------------
# Step 4.  Witness existence:  |- ?a. NUM_REP a.   (witness: IND_1.)
# ---------------------------------------------------------------------------

@proof
def NUM_REP_IND_1(p):
    p.goal("NUM_REP IND_1", types={"P": _P_ind_ty})
    p.have("eq: NUM_REP IND_1 = "
           "(!P. P IND_1 /\\ (!i:ind. P i ==> P (IND_SUC i)) ==> P IND_1)") \
        .by_thm(_NUM_REP_unfold(IND_1))
    with p.have("inner: !P. P IND_1 /\\ "
                "(!i:ind. P i ==> P (IND_SUC i)) ==> P IND_1") \
            .proof():
        p.fix("P")
        p.assume("hyp: P IND_1 /\\ (!i:ind. P i ==> P (IND_SUC i))")
        p.thus("P IND_1").by(CONJUNCT1, "hyp")
    p.thus("NUM_REP IND_1").by_eq_mp(SYM(p.fact("eq")), "inner")


@proof
def NUM_REP_IND_SUC_CLOSED(p):
    p.goal("!i:ind. NUM_REP i ==> NUM_REP (IND_SUC i)",
           types={"P": _P_ind_ty})
    p.fix("i")
    p.assume("h_NRi: NUM_REP i")
    p.have("eq_i: NUM_REP i = "
           "(!P. P IND_1 /\\ (!j:ind. P j ==> P (IND_SUC j)) ==> P i)") \
        .by_thm(_NUM_REP_unfold(_i_ind))
    p.have("h_NRi_unfold: !P. P IND_1 /\\ "
           "(!j:ind. P j ==> P (IND_SUC j)) ==> P i") \
        .by_eq_mp(p.fact("eq_i"), "h_NRi")
    p.have("eq_si: NUM_REP (IND_SUC i) = "
           "(!P. P IND_1 /\\ (!j:ind. P j ==> P (IND_SUC j)) ==> P (IND_SUC i))") \
        .by_thm(_NUM_REP_unfold(mk_comb(IND_SUC, _i_ind)))
    with p.have("inner: !P. P IND_1 /\\ "
                "(!j:ind. P j ==> P (IND_SUC j)) ==> P (IND_SUC i)") \
            .proof():
        p.fix("P")
        p.assume("hyp: P IND_1 /\\ (!j:ind. P j ==> P (IND_SUC j))")
        p.split_conj("hyp", "h_base", "h_step")
        p.have("h_NRi_at_P: P IND_1 /\\ "
               "(!j:ind. P j ==> P (IND_SUC j)) ==> P i") \
            .by(SPEC, "P", "h_NRi_unfold")
        p.have("Pi: P i").by("h_NRi_at_P", CONJ(p.fact("h_base"), p.fact("h_step")))
        p.have("step_i: P i ==> P (IND_SUC i)").by(SPEC, "i", "h_step")
        p.thus("P (IND_SUC i)").by("step_i", "Pi")
    p.thus("NUM_REP (IND_SUC i)").by_eq_mp(SYM(p.fact("eq_si")), "inner")


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

# Surface registration: num is the default type for free vars from this
# point on, and mk_num / dest_num are first-class names in @proof blocks.
DEFAULT_SIG.add_type("num", num_ty)
DEFAULT_SIG.add_const("mk_num", mk_num)
DEFAULT_SIG.add_const("dest_num", dest_num)
DEFAULT_SIG.default_var_ty = num_ty


# ---------------------------------------------------------------------------
# Step 6.  Define the constants `1` and `SUC` on num.
#
#   1 = mk_num IND_1.
#   SUC = \n:num. mk_num (IND_SUC (dest_num n)).
# ---------------------------------------------------------------------------

ONE_DEF = new_basic_definition(
    mk_eq(Var("1", num_ty), mk_comb(mk_num, IND_1)))
ONE = mk_const("1", [])
DEFAULT_SIG.add_const("1", ONE)

_n_num = Var("n", num_ty)
SUC_DEF = new_basic_definition(
    mk_eq(Var("SUC", mk_fun_ty(num_ty, num_ty)),
          mk_abs(_n_num,
              mk_comb(mk_num,
                  mk_comb(IND_SUC, mk_comb(dest_num, _n_num))))))
SUC = mk_const("SUC", [])
DEFAULT_SIG.add_const("SUC", SUC)


def mk_suc(t):
    return mk_comb(SUC, t)


def _SUC_unfold(n_term):
    """ |- SUC n = mk_num (IND_SUC (dest_num n)). """
    return BETA_RULE(AP_THM(SUC_DEF, n_term))


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

@proof
def NUM_REP_dest_num(p):
    p.goal("!a. NUM_REP (dest_num a)")
    p.fix("a")
    p.have("md_dest: dest_num (mk_num (dest_num a)) = dest_num a") \
        .by_thm(AP_TERM(dest_num, MK_DEST))
    a_kvar = Var("a", num_ty)
    p.have("dm_inst: NUM_REP (dest_num a) = "
           "(dest_num (mk_num (dest_num a)) = dest_num a)") \
        .by_thm(INST([(mk_comb(dest_num, a_kvar), Var("r", ind_ty))], DEST_MK))
    p.thus("NUM_REP (dest_num a)").by_eq_mp(SYM(p.fact("dm_inst")), "md_dest")


# ---------------------------------------------------------------------------
# Step 8.  Working facts about ONE_ONE and ONTO unfolded at IND_SUC.
# ---------------------------------------------------------------------------

def _ONE_ONE_unfold_at_IND_SUC():
    """ |- ONE_ONE IND_SUC = !x1 x2. IND_SUC x1 = IND_SUC x2 ==> x1 = x2. """
    one_one_def_ind = INST_TYPE([(ind_ty, aty), (ind_ty, bty)], ONE_ONE_DEF)
    return BETA_RULE(AP_THM(one_one_def_ind, IND_SUC))


_ONE_ONE_IND_SUC_unfold = EQ_MP(_ONE_ONE_unfold_at_IND_SUC(), ONE_ONE_IND_SUC)
# _ONE_ONE_IND_SUC_unfold : |- !x1 x2. IND_SUC x1 = IND_SUC x2 ==> x1 = x2


# ---------------------------------------------------------------------------
# Step 9.  Prove AXIOM_3 :  |- !x. ~(SUC x = 1).
# ---------------------------------------------------------------------------

@proof
def AXIOM_3(p):
    p.goal("!x. ~(SUC x = 1)")
    p.fix("x")
    with p.suppose("h: SUC x = 1"):
        # SUC x = mk_num (IND_SUC (dest_num x)) and 1 = mk_num IND_1, so the
        # hypothesis says mk_num (IND_SUC (dest_num x)) = mk_num IND_1. Apply
        # dest_num to both sides and peel via DEST_MK using NUM_REP closure.
        h_unfold = TRANS_CHAIN([SYM(p.unfold(SUC_DEF, "x")),
                                p.fact("h"), ONE_DEF])
        h_dest = AP_TERM(dest_num, h_unfold)
        r_var = Var("r", ind_ty)
        NR_si_dx = MP(SPEC(mk_comb(dest_num, x), NUM_REP_IND_SUC_CLOSED),
                      SPEC(x, NUM_REP_dest_num))
        s_dx = mk_comb(IND_SUC, mk_comb(dest_num, x))
        eq_lhs_peel = EQ_MP(INST([(s_dx, r_var)], DEST_MK), NR_si_dx)
        eq_rhs_peel = EQ_MP(INST([(IND_1, r_var)], DEST_MK), NUM_REP_IND_1)
        h_peel = TRANS_CHAIN([SYM(eq_lhs_peel), h_dest, eq_rhs_peel])
        neq_at_dx = SPEC(mk_comb(dest_num, x), IND_SUC_NEQ_IND_1)
        p.absurd().by_thm(MP(NOT_ELIM(neq_at_dx), h_peel))


# ---------------------------------------------------------------------------
# Step 10.  Prove AXIOM_4 :  |- !x y. SUC x = SUC y ==> x = y.
# ---------------------------------------------------------------------------

@proof
def AXIOM_4(p):
    p.goal("!x y. SUC x = SUC y ==> x = y")
    p.fix("x y")
    p.assume("h: SUC x = SUC y")
    h_unfold = TRANS_CHAIN([SYM(p.unfold(SUC_DEF, "x")),
                            p.fact("h"),
                            p.unfold(SUC_DEF, "y")])
    h_dest = AP_TERM(dest_num, h_unfold)
    r_var = Var("r", ind_ty)
    NR_si_dx = MP(SPEC(mk_comb(dest_num, x), NUM_REP_IND_SUC_CLOSED),
                  SPEC(x, NUM_REP_dest_num))
    NR_si_dy = MP(SPEC(mk_comb(dest_num, y), NUM_REP_IND_SUC_CLOSED),
                  SPEC(y, NUM_REP_dest_num))
    s_dx = mk_comb(IND_SUC, mk_comb(dest_num, x))
    s_dy = mk_comb(IND_SUC, mk_comb(dest_num, y))
    eq_dx_peel = EQ_MP(INST([(s_dx, r_var)], DEST_MK), NR_si_dx)
    eq_dy_peel = EQ_MP(INST([(s_dy, r_var)], DEST_MK), NR_si_dy)
    h_peeled = TRANS_CHAIN([SYM(eq_dx_peel), h_dest, eq_dy_peel])
    oo = SPEC(mk_comb(dest_num, y),
              SPEC(mk_comb(dest_num, x), _ONE_ONE_IND_SUC_unfold))
    dx_eq_dy = MP(oo, h_peeled)
    mk_app = AP_TERM(mk_num, dx_eq_dy)
    a_var = Var("a", num_ty)
    md_x = INST([(x, a_var)], MK_DEST)
    md_y = INST([(y, a_var)], MK_DEST)
    p.thus("x = y").by_thm(TRANS_CHAIN([SYM(md_x), mk_app, md_y]))


# ---------------------------------------------------------------------------
# Step 11.  Prove INDUCTION :  |- !P. P 1 /\ (!x. P x ==> P (SUC x)) ==> !x. P x.
#
# Strategy:  Define Q i := NUM_REP i /\ P (mk_num i)  on ind.
#            Show Q IND_1   and  !i. Q i ==> Q (IND_SUC i).
#            For any num a, NUM_REP_dest_num gives NUM_REP (dest_num a);
#            apply NUM_REP at Q to obtain Q (dest_num a),
#            hence P (mk_num (dest_num a)) = P a (via MK_DEST).
# ---------------------------------------------------------------------------

_P_num_ty = mk_fun_ty(num_ty, bool_ty)


@proof
def INDUCTION(p):
    p.goal("!P. P 1 /\\ (!x. P x ==> P (SUC x)) ==> !x. P x",
           types={"P": _P_num_ty})
    p.fix("P")
    p.assume("h: P 1 /\\ (!x. P x ==> P (SUC x))")
    p.split_conj("h", "h_base", "h_step")
    p.let("Q(i:ind) := NUM_REP i /\\ P (mk_num i)")

    # ----- Q IND_1. -----
    with p.have("Q_1: Q IND_1").proof():
        p.have("P_mk_ind1: P (mk_num IND_1)") \
            .by_eq_mp(AP_TERM(P, ONE_DEF), "h_base")
        p.thus("NUM_REP IND_1 /\\ P (mk_num IND_1)") \
            .by_thm(CONJ(NUM_REP_IND_1, p.fact("P_mk_ind1")))

    # ----- !i. Q i ==> Q (IND_SUC i). -----
    with p.have("Q_step: !i:ind. Q i ==> Q (IND_SUC i)").proof():
        p.fix("i")
        p.assume("h_Qi: Q i")
        p.split_conj("h_Qi", "NR_i", "P_mki")
        p.have("NR_si: NUM_REP (IND_SUC i)") \
            .by(NUM_REP_IND_SUC_CLOSED, "i", "NR_i")
        # SUC (mk_num i) = mk_num (IND_SUC i):
        #   SUC_DEF gives  SUC (mk_num i) = mk_num (IND_SUC (dest_num (mk_num i)))
        #   DEST_MK at i (with NR_i) gives  dest_num (mk_num i) = i.
        di_eq_i = EQ_MP(INST([(_i_ind, Var("r", ind_ty))], DEST_MK),
                         p.fact("NR_i"))
        SUC_mki_eq_mk_si = TRANS(
            p.unfold(SUC_DEF, mk_comb(mk_num, _i_ind)),
            AP_TERM(mk_num, AP_TERM(IND_SUC, di_eq_i)))
        # h_step at mk_num i then rewrite SUC (mk_num i) -> mk_num (IND_SUC i).
        P_SUC_mki = MP(SPEC(mk_comb(mk_num, _i_ind), p.fact("h_step")),
                       p.fact("P_mki"))
        p.have("P_mk_si: P (mk_num (IND_SUC i))") \
            .by_eq_mp(AP_TERM(P, SUC_mki_eq_mk_si), P_SUC_mki)
        p.thus("NUM_REP (IND_SUC i) /\\ P (mk_num (IND_SUC i))") \
            .by_thm(CONJ(p.fact("NR_si"), p.fact("P_mk_si")))

    # ----- For any x, NUM_REP at Q gives Q (dest_num x); peel via MK_DEST. -----
    with p.thus("!x. P x").proof():
        p.fix("x")
        NR_da_unfold = EQ_MP(_NUM_REP_unfold(mk_comb(dest_num, x)),
                             SPEC(x, NUM_REP_dest_num))
        p.have("Q_da: Q (dest_num x)") \
            .by_select(NR_da_unfold, "Q",
                       CONJ(p.fact("Q_1"), p.fact("Q_step")))
        p.split_conj("Q_da", "_NR_dx", "P_mk_dx")
        p.thus("P x").by_eq_mp(
            AP_TERM(P, INST([(x, Var("a", num_ty))], MK_DEST)),
            "P_mk_dx")


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


_R_TYPES = {"Q": _Q_ty, "c": _A, "h": _h_ty, "a": _A, "m": _A, "m1": _A,
            "m2": _A, "fn": _num_to_A}
_R_BODY = ("!Q. (Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))) ==> Q n m")


@proof
def R_AT_1(p):
    p.goal("!Q. (Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))) ==> Q 1 c",
           types=_R_TYPES)
    p.fix("Q")
    p.assume("hyp: Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))")
    p.thus("Q 1 c").by(CONJUNCT1, "hyp")


_R_LET = ("R(c, h, n, m) := !Q. (Q 1 c /\\ "
          "(!k a. Q k a ==> Q (SUC k) (h k a))) ==> Q n m")


@proof
def R_STEP(p):
    p.let(_R_LET, types=_R_TYPES)
    p.goal("!n m. R c h n m ==> R c h (SUC n) (h n m)", types=_R_TYPES)
    p.fix("n m")
    p.assume("hR: R c h n m")
    with p.thus("R c h (SUC n) (h n m)").proof():
        p.fix("Q")
        p.assume("hyp: Q 1 c /\\ (!k a. Q k a ==> Q (SUC k) (h k a))")
        p.split_conj("hyp", "_h_base", "h_close")
        p.have("Q_n_m: Q n m").by("hR", "Q", "hyp")
        p.have("step_at: Q n m ==> Q (SUC n) (h n m)") \
            .by_thm(SPEC(_m, SPEC(_n, p.fact("h_close"))))
        p.thus("Q (SUC n) (h n m)").by("step_at", "Q_n_m")


def _mk_unique_at(n_term):
    """Build  (?m. R c h n m) /\\ (!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2)."""
    R_n_m  = _mk_R(_c, _h, n_term, _m)
    R_n_m1 = _mk_R(_c, _h, n_term, _m1)
    R_n_m2 = _mk_R(_c, _h, n_term, _m2)
    exist  = mk_exists(_m, R_n_m)
    unique = mk_forall(_m1, mk_forall(_m2,
                mk_imp(mk_and(R_n_m1, R_n_m2), mk_eq(_m1, _m2))))
    return mk_and(exist, unique)


@proof
def R_UNIQUE_BASE(p):
    p.let(_R_LET, types=_R_TYPES)
    p.let("Qp(k, a) := (k = 1) ==> (a = c)", types=_R_TYPES)
    p.goal("(?m. R c h 1 m) /\\ "
           "(!m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2)",
           types=_R_TYPES)
    # Existence: witness m = c, via R_AT_1.
    R_1_m = parse("R c h 1 m", _env_bindings=p._scope_env())
    p.have("exist: ?m. R c h 1 m") \
        .by_thm(EXISTS(mk_abs(_m, R_1_m), _c, R_AT_1))
    # Closure of Qp.
    with p.have("Qp_1_c: Qp 1 c").proof():
        p.assume("h11: 1 = 1")
        p.thus("c = c").by_thm(REFL(_c))
    with p.have("Qp_close: !k a. Qp k a ==> Qp (SUC k) (h k a)").proof():
        p.fix("k a")
        p.assume("h_Qpka: Qp k a")
        # Qp (SUC k) (h k a) unfolds to (SUC k = 1) ==> (h k a = c).
        # Vacuous: SUC k = 1 contradicts AXIOM_3 specialized at k.
        p.assume("h_eq1: SUC k = 1")
        p.absurd().by_conj("h_eq1", SPEC(_k, AXIOM_3))
    p.have("Qp_closure: Qp 1 c /\\ "
           "(!k a. Qp k a ==> Qp (SUC k) (h k a))") \
        .by_thm(CONJ(p.fact("Qp_1_c"), p.fact("Qp_close")))
    # Uniqueness.
    with p.have("unique: !m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2").proof():
        p.fix("m1 m2")
        p.assume("h_conj: R c h 1 m1 /\\ R c h 1 m2")
        p.split_conj("h_conj", "h_R_m1", "h_R_m2")
        p.have("Qp_1_m1: Qp 1 m1") \
            .by_select("h_R_m1", "Qp", "Qp_closure")
        p.have("Qp_1_m2: Qp 1 m2") \
            .by_select("h_R_m2", "Qp", "Qp_closure")
        p.have("m1_eq_c: m1 = c").by("Qp_1_m1", REFL(ONE))
        p.have("m2_eq_c: m2 = c").by("Qp_1_m2", REFL(ONE))
        p.thus("m1 = m2") \
            .by_thm(TRANS(p.fact("m1_eq_c"), SYM(p.fact("m2_eq_c"))))
    p.thus("(?m. R c h 1 m) /\\ "
           "(!m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2)") \
        .by_thm(CONJ(p.fact("exist"), p.fact("unique")))


@proof
def R_UNIQUE_STEP(p):
    p.let(_R_LET, types=_R_TYPES)
    p.goal("!n. (?m. R c h n m) /\\ "
           "(!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2) ==> "
           "(?m. R c h (SUC n) m) /\\ "
           "(!m1 m2. R c h (SUC n) m1 /\\ R c h (SUC n) m2 ==> m1 = m2)",
           types=_R_TYPES)
    p.fix("n")
    p.assume("hIH: (?m. R c h n m) /\\ "
             "(!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2)")
    p.split_conj("hIH", "IH_exist", "IH_unique")
    # Bring witness m_n with R c h n m_n into scope.
    p.choose("m_n: R c h n m_n", from_="IH_exist")
    # Existence at SUC n: from R c h n m_n, R_STEP gives R c h (SUC n) (h n m_n).
    p.have("R_sn_hn: R c h (SUC n) (h n m_n)") \
        .by(R_STEP, "n", "m_n", "m_n_eq")
    p.have("exist_sn: ?m. R c h (SUC n) m") \
        .by_witness("h n m_n", "R_sn_hn")
    # Uniqueness at SUC n via Qp.
    p.let("Qp(k, a) := R c h k a /\\ (k = SUC n ==> a = h n m_n)",
           types=_R_TYPES)
    # Qp 1 c: R c h 1 c (R_AT_1) ∧ (1 = SUC n ==> c = h n m_n) (vacuous).
    with p.have("Qp_1_c: Qp 1 c").proof():
        with p.have("vac1: 1 = SUC n ==> c = h n m_n").proof():
            p.assume("h_1_sn: 1 = SUC n")
            p.absurd().by_conj(SYM(p.fact("h_1_sn")), SPEC(_n, AXIOM_3))
        p.thus("R c h 1 c /\\ (1 = SUC n ==> c = h n m_n)") \
            .by_thm(CONJ(R_AT_1, p.fact("vac1")))
    # !k a. Qp k a ==> Qp (SUC k) (h k a).
    with p.have("Qp_close: !k a. Qp k a ==> Qp (SUC k) (h k a)").proof():
        p.fix("k a")
        p.assume("h_Qpka: Qp k a")
        p.split_conj("h_Qpka", "R_k_a", "_step_part")
        p.have("R_sk_hka: R c h (SUC k) (h k a)") \
            .by(R_STEP, "k", "a", "R_k_a")
        with p.have("vac2: SUC k = SUC n ==> h k a = h n m_n").proof():
            p.assume("h_sk_sn: SUC k = SUC n")
            p.have("k_eq_n: k = n").by(AXIOM_4, "k", "n", "h_sk_sn")
            # Rewrite R c h k a -> R c h n a using k = n.
            kk = Var("kk", num_ty)
            R_func_a = mk_abs(kk, parse("R c h kk a",
                                         _env_bindings={**p._scope_env(),
                                                        "kk": kk}))
            R_k_eq_R_n = TRANS_CHAIN([
                SYM(BETA_CONV(mk_comb(R_func_a, _k))),
                AP_TERM(R_func_a, p.fact("k_eq_n")),
                BETA_CONV(mk_comb(R_func_a, _n))])
            p.have("R_n_a: R c h n a") \
                .by_eq_mp(R_k_eq_R_n, "R_k_a")
            m_n_term = mk_comb(
                mk_const("@", [(_A, aty)]),
                mk_abs(_m, parse("R c h n m", _env_bindings=p._scope_env())))
            p.have("a_eq_mn: a = m_n") \
                .by(SPEC(m_n_term, SPEC(_a, p.fact("IH_unique"))),
                    CONJ(p.fact("R_n_a"), p.fact("m_n_eq")))
            # h k a = h n a (from k=n) ; h n a = h n m_n (from a=m_n).
            h_k_a_eq_h_n_mn = TRANS(
                AP_THM(AP_TERM(_h, p.fact("k_eq_n")), _a),
                AP_TERM(mk_comb(_h, _n), p.fact("a_eq_mn")))
            p.thus("h k a = h n m_n").by_thm(h_k_a_eq_h_n_mn)
        p.thus("R c h (SUC k) (h k a) /\\ "
               "(SUC k = SUC n ==> h k a = h n m_n)") \
            .by_thm(CONJ(p.fact("R_sk_hka"), p.fact("vac2")))
    p.have("Qp_closure: Qp 1 c /\\ "
           "(!k a. Qp k a ==> Qp (SUC k) (h k a))") \
        .by_thm(CONJ(p.fact("Qp_1_c"), p.fact("Qp_close")))
    with p.have("unique_sn: !m1 m2. R c h (SUC n) m1 /\\ "
                "R c h (SUC n) m2 ==> m1 = m2").proof():
        p.fix("m1 m2")
        p.assume("h_conj: R c h (SUC n) m1 /\\ R c h (SUC n) m2")
        p.split_conj("h_conj", "h_R_m1", "h_R_m2")
        p.have("Qp_sn_m1: Qp (SUC n) m1") \
            .by_select("h_R_m1", "Qp", "Qp_closure")
        p.have("Qp_sn_m2: Qp (SUC n) m2") \
            .by_select("h_R_m2", "Qp", "Qp_closure")
        p.split_conj("Qp_sn_m1", "_R_sn_m1", "step1")
        p.split_conj("Qp_sn_m2", "_R_sn_m2", "step2")
        p.have("m1_eq: m1 = h n m_n").by("step1", REFL(mk_suc(_n)))
        p.have("m2_eq: m2 = h n m_n").by("step2", REFL(mk_suc(_n)))
        p.thus("m1 = m2") \
            .by_thm(TRANS(p.fact("m1_eq"), SYM(p.fact("m2_eq"))))
    p.thus("(?m. R c h (SUC n) m) /\\ "
           "(!m1 m2. R c h (SUC n) m1 /\\ R c h (SUC n) m2 ==> m1 = m2)") \
        .by_thm(CONJ(p.fact("exist_sn"), p.fact("unique_sn")))


# Now combine via INDUCT to get R_UNIQUE: |- !n. _mk_unique_at(n).
def _prove_R_unique():
    pred = mk_abs(_n, _mk_unique_at(_n))
    return INDUCT(pred, R_UNIQUE_BASE, R_UNIQUE_STEP)

R_UNIQUE = _prove_R_unique()


# ---------------------------------------------------------------------------
# NUM_RECURSION:  |- !c h. ?fn:num->A. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
# ---------------------------------------------------------------------------

@proof
def NUM_RECURSION(p):
    p.let(_R_LET, types=_R_TYPES)
    p.goal("!c h. ?fn. fn 1 = c /\\ (!n. fn (SUC n) = h n (fn n))",
           types=_R_TYPES)
    p.fix("c h")
    sel_const = mk_const("@", [(_A, aty)])

    # Build R c h k m and pred_R_k = \m. R c h k m once for each k of interest.
    pred_R_1 = mk_abs(_m, _mk_R(_c, _h, ONE, _m))
    sel_pred_R_1 = mk_comb(sel_const, pred_R_1)

    # Step 1: (@m. R c h 1 m) = c, by uniqueness at 1 + R_AT_1 + SELECT.
    R_unique_1 = SPEC(ONE, R_UNIQUE)
    exist_1, unique_1 = CONJUNCT1(R_unique_1), CONJUNCT2(R_unique_1)
    R_1_at_sel = PROVE_HYP(
        exist_1,
        ELIM_EX(pred_R_1, exist_1._concl, lambda th: th))
    sel1_eq_c = MP(SPEC(_c, SPEC(sel_pred_R_1, unique_1)),
                   CONJ(R_1_at_sel, R_AT_1))   # |- (@m. R c h 1 m) = c

    # Step 2: !n. (@m. R c h (SUC n) m) = h n (@m. R c h n m).
    with p.have("fn_step: !n. (@m. R c h (SUC n) m) = "
                "h n (@m. R c h n m)").proof():
        p.fix("n")
        R_unique_n = SPEC(_n, R_UNIQUE)
        exist_n = CONJUNCT1(R_unique_n)
        pred_R_n = mk_abs(_m, _mk_R(_c, _h, _n, _m))
        R_n_at_sel = PROVE_HYP(
            exist_n,
            ELIM_EX(pred_R_n, exist_n._concl, lambda th: th))
        sel_pred_R_n = mk_comb(sel_const, pred_R_n)
        R_sn_h_n_sel = MP(SPEC(sel_pred_R_n, SPEC(_n, R_STEP)),
                          R_n_at_sel)
        R_unique_sn = SPEC(mk_suc(_n), R_UNIQUE)
        exist_sn, unique_sn = CONJUNCT1(R_unique_sn), CONJUNCT2(R_unique_sn)
        pred_R_sn = mk_abs(_m, _mk_R(_c, _h, mk_suc(_n), _m))
        R_sn_at_sel = PROVE_HYP(
            exist_sn,
            ELIM_EX(pred_R_sn, exist_sn._concl, lambda th: th))
        sel_pred_R_sn = mk_comb(sel_const, pred_R_sn)
        h_n_sel = mk_comb(mk_comb(_h, _n), sel_pred_R_n)
        p.thus("(@m. R c h (SUC n) m) = h n (@m. R c h n m)") \
            .by_thm(MP(SPEC(h_n_sel, SPEC(sel_pred_R_sn, unique_sn)),
                       CONJ(R_sn_at_sel, R_sn_h_n_sel)))

    # Build fn_body := \n. @m. R c h n m and EXISTS at it. The substituted
    # body of \fn. (...) at fn_body beta-reduces to the conjunction we have:
    # (fn_body 1) beta-converts to (@m. R c h 1 m); same for (fn_body n) and
    # (fn_body (SUC n)). We bridge via TRANS_CHAIN over BETA_CONVs.
    fn_body = mk_abs(_n, mk_comb(sel_const, mk_abs(_m, _mk_R(_c, _h, _n, _m))))
    fn_1   = mk_comb(fn_body, ONE)
    fn_n   = mk_comb(fn_body, _n)
    fn_sn  = mk_comb(fn_body, mk_suc(_n))
    beta_1  = BETA_CONV(fn_1)
    beta_n  = BETA_CONV(fn_n)
    beta_sn = BETA_CONV(fn_sn)
    fn_1_eq_c = TRANS(beta_1, sel1_eq_c)
    h_n_fnn_eq = AP_TERM(mk_comb(_h, _n), beta_n)
    fn_sn_eq = TRANS_CHAIN([
        beta_sn,
        SPEC(_n, p.fact("fn_step")),
        SYM(h_n_fnn_eq)])
    forall_step = GEN(_n, fn_sn_eq)
    combined = CONJ(fn_1_eq_c, forall_step)
    body_pred = mk_and(
        mk_eq(mk_comb(_fn, ONE), _c),
        mk_forall(_n, mk_eq(mk_comb(_fn, mk_suc(_n)),
                            mk_comb(mk_comb(_h, _n), mk_comb(_fn, _n)))))
    pred_fn = mk_abs(_fn, body_pred)
    p.thus("?fn. fn 1 = c /\\ (!n. fn (SUC n) = h n (fn n))") \
        .by_thm(EXISTS(pred_fn, fn_body, combined))


# ---------------------------------------------------------------------------
# define_recursive -- declare a binary operator on num by primitive recursion.
#
# Given:
#     c : term in x_var,                                     # value at y = 1
#     h : Abs(k_var, Abs(a_var, body[k, a, x_var])),         # step kernel
# define
#     name x y := (@fn:num->num. fn 1 = c /\ !n. fn (SUC n) = body[n, fn n]) y
# and return the two recursion equations as theorems:
#     BASE : |- !x. name x 1 = c
#     STEP : |- !x y. name x (SUC y) = body[y, name x y]
#
# Folds together NUM_RECURSION (existence) + SELECT_AX (witness extraction)
# + the BETA-reduction dance that turns the raw `h n (fn n)` form into the
# clean step body. Each new recursive operator becomes a one-liner.
# ---------------------------------------------------------------------------

from parser import define as _define


def define_recursive(name, fn_ty, x_var, c, h, *, prec=None, assoc="non"):
    if not isinstance(h, Abs) or not isinstance(h.body, Abs):
        raise HolError(
            "define_recursive: h must be Abs(k, Abs(a, body))")

    fn_to_num = mk_fun_ty(num_ty, num_ty)
    fn_var = Var("fn", fn_to_num)
    n_var = Var("n", num_ty)
    y_var = Var("y", num_ty)

    fn_1   = mk_comb(fn_var, ONE)
    fn_n   = mk_comb(fn_var, n_var)
    fn_sn  = mk_comb(fn_var, mk_suc(n_var))

    # Beta-reduce h n (fn n) once to get the clean step body
    # (= body[k:=n_var, a:=fn_n]).
    h_at_n   = BETA_CONV(mk_comb(h, n_var))                 # |- h n = (\a. body[k:=n])
    inner    = AP_THM(h_at_n, fn_n)                          # |- (h n) (fn n) = (\a. ...) (fn n)
    full     = BETA_CONV(rand(inner._concl))                 # |- (\a. ...) (fn n) = body[k:=n, a:=fn n]
    h_red    = TRANS(inner, full)                             # |- h n (fn n) = clean_step
    step_clean = rand(h_red._concl)

    # Clean predicate \fn. fn 1 = c /\ !n. fn (SUC n) = clean_step.
    pred_clean = mk_abs(fn_var,
        mk_and(mk_eq(fn_1, c),
                mk_forall(n_var, mk_eq(fn_sn, step_clean))))

    sel_const = mk_const("@", [(fn_to_num, aty)])
    sel_at_pc = mk_comb(sel_const, pred_clean)              # @fn. pred_clean fn

    # Operator definition: \x y. (@fn. pred_clean fn) y.
    op_rhs = mk_abs(x_var, mk_abs(y_var, mk_comb(sel_at_pc, y_var)))
    OP_DEF = _define(name, fn_ty, op_rhs, prec=prec, assoc=assoc)

    # NUM_RECURSION at this c, h: |- ?fn. fn 1 = c /\ !n. fn (SUC n) = h n (fn n).
    NR_num = INST_TYPE([(num_ty, aty)], NUM_RECURSION)
    spec_ch = SPEC(h, SPEC(c, NR_num))
    pred_raw = spec_ch._concl.arg
    sel_at_raw = mk_comb(sel_const, pred_raw)               # @fn. raw_body[fn]

    # Extract the conjunction body under the existential witness.
    body_raw = PROVE_HYP(spec_ch,
                          ELIM_EX(pred_raw, spec_ch._concl, lambda th: th))
    raw_base = CONJUNCT1(body_raw)                          # |- sel_at_raw 1 = c
    raw_step = CONJUNCT2(body_raw)                          # |- !n. sel_at_raw (SUC n) = h n (sel_at_raw n)

    # Convert raw step (with embedded h) to clean step (beta-reduced).
    raw_at_n   = SPEC(n_var, raw_step)
    h_red_w    = INST([(sel_at_raw, fn_var)], h_red)        # |- h n (sel_at_raw n) = clean_step[fn:=sel_at_raw]
    clean_at_n = TRANS(raw_at_n, h_red_w)                    # |- sel_at_raw (SUC n) = clean_step[fn:=sel_at_raw]
    clean_step_forall = GEN(n_var, clean_at_n)

    # pred_clean (sel_at_raw) holds: combine the two conjuncts.
    pc_at_raw_body = CONJ(raw_base, clean_step_forall)
    pc_at_raw_eq   = BETA_CONV(mk_comb(pred_clean, sel_at_raw))
    pc_at_raw      = EQ_MP(SYM(pc_at_raw_eq), pc_at_raw_body)

    # SELECT_AX: pred_clean (sel_at_raw) ==> pred_clean (@pred_clean).
    sel_inst = INST_TYPE([(fn_to_num, aty)], SELECT_AX)
    sel_imp  = SPEC(sel_at_raw, SPEC(pred_clean, sel_inst))
    pc_at_sel = MP(sel_imp, pc_at_raw)
    pc_at_sel_eq = BETA_CONV(mk_comb(pred_clean, sel_at_pc))
    pc_at_sel_body = EQ_MP(pc_at_sel_eq, pc_at_sel)
    sel_base = CONJUNCT1(pc_at_sel_body)                    # |- (@pred_clean) 1 = c
    sel_step = CONJUNCT2(pc_at_sel_body)                    # |- !n. (@pred_clean) (SUC n) = clean_step[fn:=@pred_clean]

    # Connect (@pred_clean) y back to `name x y` via OP_DEF.
    OP = mk_const(name, [])
    op_at_x = AP_THM(OP_DEF, x_var)
    op_at_x = TRANS(op_at_x, BETA_CONV(rand(op_at_x._concl)))   # |- name x = \y. (@pred_clean) y

    op_at_x_at_1 = AP_THM(op_at_x, ONE)
    op_at_x_at_1 = TRANS(op_at_x_at_1, BETA_CONV(rand(op_at_x_at_1._concl)))
    BASE_THM = GEN(x_var, TRANS(op_at_x_at_1, sel_base))         # |- !x. name x 1 = c

    op_at_x_at_y = AP_THM(op_at_x, y_var)
    op_at_x_at_y = TRANS(op_at_x_at_y, BETA_CONV(rand(op_at_x_at_y._concl)))
    op_at_x_at_sy = AP_THM(op_at_x, mk_suc(y_var))
    op_at_x_at_sy = TRANS(op_at_x_at_sy, BETA_CONV(rand(op_at_x_at_sy._concl)))
    sel_at_sy   = SPEC(y_var, sel_step)
    raw_step_eq = TRANS(op_at_x_at_sy, sel_at_sy)
    # raw_step_eq : |- name x (SUC y) = clean_step[fn:=@pred_clean, n:=y].
    # Rewrite (@pred_clean) y -> name x y on the RHS.
    step_eq = REWRITE_RULE([SYM(op_at_x_at_y)], raw_step_eq)
    STEP_THM = GENL([x_var, y_var], step_eq)

    return BASE_THM, STEP_THM


# Surface registrations are now performed inline as each constant becomes
# available (see the `DEFAULT_SIG.add_const(...)` calls above), so that
# @proof blocks within this module can refer to them by name.


def _selftest_R():
    from parser import pp_thm
    print("R_AT_1:        ", pp_thm(R_AT_1))
    print("R_STEP:        ", pp_thm(R_STEP))
    print("R_UNIQUE_BASE: ", pp_thm(R_UNIQUE_BASE))
    print("R_UNIQUE_STEP: ", pp_thm(R_UNIQUE_STEP))
    print("R_UNIQUE:      ", pp_thm(R_UNIQUE))
    print("NUM_RECURSION: ", pp_thm(NUM_RECURSION))


if __name__ == "__main__":
    _selftest_R()
