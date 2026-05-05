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
    Var, Abs, aty, mk_comb,
    mk_type, new_basic_type_definition,
    REFL, TRANS, ASSUME, EQ_MP, INST, INST_TYPE, HolError,
)
from basics import (
    bty, mk_abs, mk_app, mk_const, mk_eq,
    rand,
)
from axioms import (
    SELECT_AX, INFINITY_AX, ONE_ONE_DEF, ONTO_DEF,
    ind_ty,
    mk_and, mk_imp, mk_forall, mk_exists,
)
from tactics import (
    AP_TERM, AP_THM, BETA_CONV, SYM, SPEC, GEN, GENL,
    CONJ, CONJUNCT1, CONJUNCT2, DISCH, MP, EXISTS,
    CHOOSE_WITNESS, NOT_ELIM, NE_SYM, TRANS_CHAIN, UNFOLD, unfold_def_at,
    REWRITE_RULE,
)
from classical import NOT_FORALL_TO_EX_NOT, NOT_EX_TO_FORALL_NOT
from proof import proof, register_induction, InductionStrategy
from parser import (
    parse, parse_type, define as _define,
    add_const, add_type, set_default_var_ty,
)


# ---------------------------------------------------------------------------
# Step 1.  Extract IND_SUC : ind->ind from INFINITY_AX.
#
#   INFINITY_AX : |- ?f. ONE_ONE f /\ ~(ONTO f).
#   IND_SUC := @f. ONE_ONE f /\ ~(ONTO f).
# ---------------------------------------------------------------------------

_one_one_ind = mk_const("ONE_ONE", [(ind_ty, aty), (ind_ty, bty)])
_onto_ind    = mk_const("ONTO",    [(ind_ty, aty), (ind_ty, bty)])

IND_SUC_DEF = _define("IND_SUC", "ind -> ind",
    "@f:ind -> ind. ${oo} f /\\ ~(${onto} f)",
    oo=_one_one_ind, onto=_onto_ind)
IND_SUC = mk_const("IND_SUC", [])

# Register surface syntax as soon as each constant becomes available, so that
# subsequent ``@proof`` blocks can mention them by name. ``ind`` is the type
# of points we'll carve ``num`` out of, and ``ONE_ONE_ind`` / ``ONTO_ind`` are
# the (ind->ind)-instantiated copies of ``ONE_ONE`` / ``ONTO`` -- registering
# the polymorphic kernel constants directly would force the parser to do
# type inference, so we expose them at the single instantiation we need.
add_type("ind", ind_ty)
add_const("ONE_ONE_ind", _one_one_ind)
add_const("ONTO_ind",    _onto_ind)


@proof
def _IND_SUC_PROPS_PAIR(prf):
    # INFINITY_AX gives ?f. ONE_ONE f /\ ~(ONTO f). Choose the witness; it's
    # @(\f. ...) by definition of ``?``-elimination, which equals IND_SUC by
    # IND_SUC_DEF. Rewrite the chosen-witness fact to expose IND_SUC.
    prf.goal("ONE_ONE_ind IND_SUC /\\ ~(ONTO_ind IND_SUC)")
    prf.choose("f: ONE_ONE_ind f /\\ ~(ONTO_ind f)", from_=INFINITY_AX)
    prf.thus("ONE_ONE_ind IND_SUC /\\ ~(ONTO_ind IND_SUC)") \
        .by_rewrite_of("f_eq", [SYM(IND_SUC_DEF)])


ONE_ONE_IND_SUC = CONJUNCT1(_IND_SUC_PROPS_PAIR)
NOT_ONTO_IND_SUC = CONJUNCT2(_IND_SUC_PROPS_PAIR)


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


_NOT_C = mk_const("~", [])
_ONTO_DEF_IND = INST_TYPE([(ind_ty, aty), (ind_ty, bty)], ONTO_DEF)
# |- ~(ONTO IND_SUC) = ~(!y. ?x. y = IND_SUC x)
_NOT_ONTO_UNFOLD = AP_TERM(_NOT_C, UNFOLD(_ONTO_DEF_IND, IND_SUC))


@proof
def _EXISTS_WITNESS(prf):
    prf.goal("?z:ind. !x:ind. ~(IND_SUC x = z)")
    prf.have("not_forall: ~(!y:ind. ?x:ind. y = IND_SUC x)") \
        .by_eq_mp(_NOT_ONTO_UNFOLD, NOT_ONTO_IND_SUC)
    # NOT_FORALL_TO_EX_NOT swaps the outer quantifier to existential.
    _outer_pred = parse("\\y:ind. ?x:ind. y = IND_SUC x")
    prf.have("ex_not: ?y:ind. ~(?x:ind. y = IND_SUC x)") \
        .by_thm(NOT_FORALL_TO_EX_NOT(prf.fact("not_forall"), _outer_pred))
    prf.choose("y: ~(?x:ind. y = IND_SUC x)", from_="ex_not")
    # NOT_EX_TO_FORALL_NOT then NE_SYM to swap the inner equation orientation.
    _inner_pred = prf._parse("\\x:ind. y = IND_SUC x")
    prf.have("forall_neq: !x:ind. ~(y = IND_SUC x)") \
        .by_thm(NOT_EX_TO_FORALL_NOT(prf.fact("y_eq"), _inner_pred))
    with prf.have("forall_swapped: !x:ind. ~(IND_SUC x = y)").proof():
        prf.fix("x")
        prf.thus("~(IND_SUC x = y)") \
            .by_thm(NE_SYM(SPEC(prf._parse("x"), prf.fact("forall_neq"))))
    prf.thus("?z:ind. !x:ind. ~(IND_SUC x = z)") \
        .by_witness("y", "forall_swapped")


# Define IND_1 = @z. !x. ~(IND_SUC x = z).
IND_1_DEF = _define("IND_1", ind_ty,
    "@z:ind. !x:ind. ~(IND_SUC x = z)")
IND_1 = mk_const("IND_1", [])


@proof
def IND_SUC_NEQ_IND_1(prf):
    # _EXISTS_WITNESS : |- ?z. !x. ~(IND_SUC x = z); IND_1_DEF picks the very
    # @-witness as IND_1, so chooser-bind z and rewrite z -> IND_1.
    prf.goal("!x:ind. ~(IND_SUC x = IND_1)")
    prf.choose("z: !x:ind. ~(IND_SUC x = z)", from_=_EXISTS_WITNESS)
    prf.thus("!x:ind. ~(IND_SUC x = IND_1)") \
        .by_rewrite_of("z_eq", [SYM(IND_1_DEF)])


# ---------------------------------------------------------------------------
# Step 3.  Define the inductive predicate NUM_REP on ind.
#
#   NUM_REP a := !P. P IND_1 /\ (!i. P i ==> P (IND_SUC i)) ==> P a.
# ---------------------------------------------------------------------------

_a_ind  = Var("a", ind_ty)
_i_ind  = Var("i", ind_ty)
_P_ind_ty = parse_type("ind -> bool")
_P_ind  = Var("P", _P_ind_ty)

NUM_REP_DEF = _define("NUM_REP", _P_ind_ty,
    "\\a:ind. !P:ind->bool. "
    "P IND_1 /\\ (!i:ind. P i ==> P (IND_SUC i)) ==> P a")
NUM_REP = mk_const("NUM_REP", [])


def _NUM_REP_unfold(a_term):
    r""" |- NUM_REP a = (!P. P IND_1 /\ (!i. P i ==> P (IND_SUC i)) ==> P a). """
    return UNFOLD(NUM_REP_DEF, a_term)


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
        p.assume("(h_base, h_step): "
                 "P IND_1 /\\ (!j:ind. P j ==> P (IND_SUC j))")
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
add_type("num", num_ty)
add_const("mk_num", mk_num)
add_const("dest_num", dest_num)
set_default_var_ty(num_ty)


# ---------------------------------------------------------------------------
# Step 6.  Define the constants `1` and `SUC` on num.
#
#   1 = mk_num IND_1.
#   SUC = \n:num. mk_num (IND_SUC (dest_num n)).
# ---------------------------------------------------------------------------

ONE_DEF = _define("1", num_ty, "mk_num IND_1")
ONE = mk_const("1", [])

SUC_DEF = _define("SUC", "num -> num",
    "\\n:num. mk_num (IND_SUC (dest_num n))")
SUC = mk_const("SUC", [])


def mk_suc(t):
    return mk_comb(SUC, t)


# Standard variable names re-used throughout the arithmetic development.
x = Var("x", num_ty)
y = Var("y", num_ty)
z = Var("z", num_ty)
u = Var("u", num_ty)
v = Var("v", num_ty)
w = Var("w", num_ty)
P = Var("P", parse_type("num -> bool"))


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

_ONE_ONE_IND_SUC_unfold = EQ_MP(
    UNFOLD(INST_TYPE([(ind_ty, aty), (ind_ty, bty)], ONE_ONE_DEF), IND_SUC),
    ONE_ONE_IND_SUC)
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

_P_num_ty = parse_type("num -> bool")


@proof
def INDUCTION(p):
    p.goal("!P. P 1 /\\ (!x. P x ==> P (SUC x)) ==> !x. P x",
           types={"P": _P_num_ty})
    p.fix("P")
    p.assume("(h_base, h_step): P 1 /\\ (!x. P x ==> P (SUC x))")
    p.let("Q(i:ind) := NUM_REP i /\\ P (mk_num i)")

    # ----- Q IND_1. -----
    with p.have("Q_1: Q IND_1").proof():
        p.have("P_mk_ind1: P (mk_num IND_1)") \
            .by_eq_mp(AP_TERM(P, ONE_DEF), "h_base")
        p.thus("Q IND_1") \
            .by(CONJ, NUM_REP_IND_1, "P_mk_ind1")

    # ----- !i. Q i ==> Q (IND_SUC i). -----
    with p.have("Q_step: !i:ind. Q i ==> Q (IND_SUC i)").proof():
        p.fix("i")
        p.assume("(NR_i, P_mki): Q i")
        p.have("NR_si: NUM_REP (IND_SUC i)") \
            .by_match(NUM_REP_IND_SUC_CLOSED, "NR_i")
        di_eq_i = EQ_MP(INST([(_i_ind, Var("r", ind_ty))], DEST_MK),
                         p.fact("NR_i"))
        SUC_mki_eq_mk_si = TRANS(
            p.unfold(SUC_DEF, mk_comb(mk_num, _i_ind)),
            AP_TERM(mk_num, AP_TERM(IND_SUC, di_eq_i)))
        P_SUC_mki = MP(SPEC(mk_comb(mk_num, _i_ind), p.fact("h_step")),
                       p.fact("P_mki"))
        p.have("P_mk_si: P (mk_num (IND_SUC i))") \
            .by_eq_mp(AP_TERM(P, SUC_mki_eq_mk_si), P_SUC_mki)
        p.thus("Q (IND_SUC i)") \
            .by(CONJ, "NR_si", "P_mk_si")

    # ----- For any x, NUM_REP at Q gives Q (dest_num x); peel via MK_DEST. -----
    with p.thus("!x. P x").proof():
        p.fix("x")
        NR_da_unfold = EQ_MP(_NUM_REP_unfold(mk_comb(dest_num, x)),
                             SPEC(x, NUM_REP_dest_num))
        p.have("Q_da: Q (dest_num x)") \
            .by(NR_da_unfold, "Q",
                CONJ(p.fact("Q_1"), p.fact("Q_step")))
        p.split("Q_da", "(_NR_dx, P_mk_dx)")
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


# Register the natural-number induction strategy with the proof DSL.
# This is what makes ``p.induction("n")`` work for ``n : num`` without
# ``proof.py`` needing to import anything from this module.
register_induction(InductionStrategy(
    ty=num_ty,
    base_term=ONE,
    succ_fn=mk_suc,
    induct_prove=INDUCT_PROVE,
))


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
_num_to_A     = parse_type("num -> A")
_A_to_A       = parse_type("A -> A")
_h_ty         = parse_type("num -> A -> A")
_Q_ty         = parse_type("num -> A -> bool")

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
    Q_1_c   = mk_app(Q_term, ONE, c_term)
    h_k_a   = mk_app(h_term, _k, _a)
    Q_k_a   = mk_app(Q_term, _k, _a)
    Q_sk_h  = mk_app(Q_term, mk_suc(_k), h_k_a)
    closure = mk_forall(_k, mk_forall(_a, mk_imp(Q_k_a, Q_sk_h)))
    return mk_and(Q_1_c, closure)


def _mk_R(c_term, h_term, n_term, m_term):
    """Build R c h n m as  !Q. (Q 1 c /\\ closure) ==> Q n m."""
    hyp = _mk_closure_hyp(_Q, c_term, h_term)
    Q_n_m = mk_app(_Q, n_term, m_term)
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
        p.split("hyp", "(_h_base, h_close)")
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
    p.have("exist: ?m. R c h 1 m").by_witness("c", R_AT_1)
    # Closure of Qp.
    with p.have("Qp_1_c: Qp 1 c").proof():
        p.assume("h11: 1 = 1")
        p.thus("c = c").by_thm(REFL(_c))
    with p.have("Qp_close: !k a. Qp k a ==> Qp (SUC k) (h k a)").proof():
        p.fix("k a")
        p.assume("h_Qpka: Qp k a")
        # Vacuous: SUC k = 1 contradicts AXIOM_3 at k.
        p.assume("h_eq1: SUC k = 1")
        p.absurd().by_conj("h_eq1", SPEC(_k, AXIOM_3))
    p.have("Qp_closure: Qp 1 c /\\ "
           "(!k a. Qp k a ==> Qp (SUC k) (h k a))") \
        .by(CONJ, "Qp_1_c", "Qp_close")
    # Uniqueness.
    with p.have("unique: !m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2").proof():
        p.fix("m1 m2")
        p.assume("(h_R_m1, h_R_m2): R c h 1 m1 /\\ R c h 1 m2")
        p.have("Qp_1_m1: Qp 1 m1") \
            .by("h_R_m1", "Qp", "Qp_closure")
        p.have("Qp_1_m2: Qp 1 m2") \
            .by("h_R_m2", "Qp", "Qp_closure")
        p.have("m1_eq_c: m1 = c").by("Qp_1_m1", REFL(ONE))
        p.have("m2_eq_c: m2 = c").by("Qp_1_m2", REFL(ONE))
        p.thus("m1 = m2").by_rewrite(["m1_eq_c", "m2_eq_c"])
    p.thus("(?m. R c h 1 m) /\\ "
           "(!m1 m2. R c h 1 m1 /\\ R c h 1 m2 ==> m1 = m2)") \
        .by(CONJ, "exist", "unique")


@proof
def R_UNIQUE_STEP(p):
    p.let(_R_LET, types=_R_TYPES)
    p.goal("!n. (?m. R c h n m) /\\ "
           "(!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2) ==> "
           "(?m. R c h (SUC n) m) /\\ "
           "(!m1 m2. R c h (SUC n) m1 /\\ R c h (SUC n) m2 ==> m1 = m2)",
           types=_R_TYPES)
    p.fix("n")
    p.assume("(IH_exist, IH_unique): (?m. R c h n m) /\\ "
             "(!m1 m2. R c h n m1 /\\ R c h n m2 ==> m1 = m2)")
    # Bring witness m_n with R c h n m_n into scope.
    p.choose("m_n: R c h n m_n", from_="IH_exist")
    # Existence at SUC n: from R c h n m_n, R_STEP gives R c h (SUC n) (h n m_n).
    p.have("R_sn_hn: R c h (SUC n) (h n m_n)") \
        .by_match(R_STEP, "m_n_eq")
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
            .by(CONJ, R_AT_1, "vac1")
    # !k a. Qp k a ==> Qp (SUC k) (h k a).
    with p.have("Qp_close: !k a. Qp k a ==> Qp (SUC k) (h k a)").proof():
        p.fix("k a")
        p.assume("(R_k_a, _step_part): Qp k a")
        p.have("R_sk_hka: R c h (SUC k) (h k a)") \
            .by_match(R_STEP, "R_k_a")
        with p.have("vac2: SUC k = SUC n ==> h k a = h n m_n").proof():
            p.assume("h_sk_sn: SUC k = SUC n")
            p.have("k_eq_n: k = n").by_match(AXIOM_4, "h_sk_sn")
            # Rewrite R c h k a -> R c h n a using k = n. R_k_a's body is
            # under a !Q. binder and k_eq_n carries the SUC k = SUC n hyp,
            # so the rewriter's under-binder filter blocks it -- bridge by
            # hand at the abstraction \kk. R c h kk a.
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
        p.thus("Qp (SUC k) (h k a)").by(CONJ, "R_sk_hka", "vac2")
    p.have("Qp_closure: Qp 1 c /\\ "
           "(!k a. Qp k a ==> Qp (SUC k) (h k a))") \
        .by(CONJ, "Qp_1_c", "Qp_close")
    with p.have("unique_sn: !m1 m2. R c h (SUC n) m1 /\\ "
                "R c h (SUC n) m2 ==> m1 = m2").proof():
        p.fix("m1 m2")
        p.assume("(h_R_m1, h_R_m2): "
                 "R c h (SUC n) m1 /\\ R c h (SUC n) m2")
        p.have("Qp_sn_m1: Qp (SUC n) m1") \
            .by("h_R_m1", "Qp", "Qp_closure")
        p.have("Qp_sn_m2: Qp (SUC n) m2") \
            .by("h_R_m2", "Qp", "Qp_closure")
        p.split("Qp_sn_m1", "(_R_sn_m1, step1)")
        p.split("Qp_sn_m2", "(_R_sn_m2, step2)")
        p.have("m1_eq: m1 = h n m_n").by("step1", REFL(mk_suc(_n)))
        p.have("m2_eq: m2 = h n m_n").by("step2", REFL(mk_suc(_n)))
        p.thus("m1 = m2").by_rewrite(["m1_eq", "m2_eq"])
    p.thus("(?m. R c h (SUC n) m) /\\ "
           "(!m1 m2. R c h (SUC n) m1 /\\ R c h (SUC n) m2 ==> m1 = m2)") \
        .by(CONJ, "exist_sn", "unique_sn")


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
    R_1_at_sel = CHOOSE_WITNESS(pred_R_1, exist_1)
    sel1_eq_c = MP(SPEC(_c, SPEC(sel_pred_R_1, unique_1)),
                   CONJ(R_1_at_sel, R_AT_1))   # |- (@m. R c h 1 m) = c

    # Step 2: !n. (@m. R c h (SUC n) m) = h n (@m. R c h n m).
    with p.have("fn_step: !n. (@m. R c h (SUC n) m) = "
                "h n (@m. R c h n m)").proof():
        p.fix("n")
        R_unique_n = SPEC(_n, R_UNIQUE)
        exist_n = CONJUNCT1(R_unique_n)
        pred_R_n = mk_abs(_m, _mk_R(_c, _h, _n, _m))
        R_n_at_sel = CHOOSE_WITNESS(pred_R_n, exist_n)
        sel_pred_R_n = mk_comb(sel_const, pred_R_n)
        R_sn_h_n_sel = MP(SPEC(sel_pred_R_n, SPEC(_n, R_STEP)),
                          R_n_at_sel)
        R_unique_sn = SPEC(mk_suc(_n), R_UNIQUE)
        exist_sn, unique_sn = CONJUNCT1(R_unique_sn), CONJUNCT2(R_unique_sn)
        pred_R_sn = mk_abs(_m, _mk_R(_c, _h, mk_suc(_n), _m))
        R_sn_at_sel = CHOOSE_WITNESS(pred_R_sn, exist_sn)
        sel_pred_R_sn = mk_comb(sel_const, pred_R_sn)
        h_n_sel = mk_app(_h, _n, sel_pred_R_n)
        p.thus("(@m. R c h (SUC n) m) = h n (@m. R c h n m)") \
            .by_thm(MP(SPEC(h_n_sel, SPEC(sel_pred_R_sn, unique_sn)),
                       CONJ(R_sn_at_sel, R_sn_h_n_sel)))

    # Build fn_body := \n. @m. R c h n m and EXISTS at it. The substituted
    # body of \fn. (...) at fn_body beta-reduces to the conjunction we have:
    # (fn_body 1) beta-converts to (@m. R c h 1 m); same for (fn_body n) and
    # (fn_body (SUC n)). We bridge via TRANS_CHAIN over BETA_CONVs.
    fn_body = mk_abs(_n, mk_comb(sel_const, mk_abs(_m, _mk_R(_c, _h, _n, _m))))
    beta_1  = BETA_CONV(mk_comb(fn_body, ONE))
    beta_n  = BETA_CONV(mk_comb(fn_body, _n))
    beta_sn = BETA_CONV(mk_comb(fn_body, mk_suc(_n)))
    fn_1_eq_c = TRANS(beta_1, sel1_eq_c)
    h_n_fnn_eq = AP_TERM(mk_comb(_h, _n), beta_n)
    # fn_step's stored concl uses the folded ``R c h …`` carrier; materialize
    # the let so its conclusion matches beta_sn's unfolded ``!Q. …`` shape.
    fn_step_un = p.materialize_let(p.fact("fn_step"), "R")
    fn_sn_eq = TRANS_CHAIN([beta_sn,
                             SPEC(_n, fn_step_un),
                             SYM(h_n_fnn_eq)])
    combined = CONJ(fn_1_eq_c, GEN(_n, fn_sn_eq))
    p.thus("?fn. fn 1 = c /\\ (!n. fn (SUC n) = h n (fn n))") \
        .by_witness(fn_body, combined)


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


def define_recursive(name, fn_ty, x_var, c, h, *, prec=None, assoc="non"):
    if not isinstance(h, Abs) or not isinstance(h.body, Abs):
        raise HolError(
            "define_recursive: h must be Abs(k, Abs(a, body))")

    fn_to_num = parse_type("num -> num")
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
    body_raw = CHOOSE_WITNESS(pred_raw, spec_ch)
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
    op_at_x = unfold_def_at(OP_DEF, x_var)        # |- name x = \y. (@pred_clean) y

    op_at_x_at_1 = unfold_def_at(op_at_x, ONE)
    BASE_THM = GEN(x_var, TRANS(op_at_x_at_1, sel_base))         # |- !x. name x 1 = c

    op_at_x_at_y = unfold_def_at(op_at_x, y_var)
    op_at_x_at_sy = unfold_def_at(op_at_x, mk_suc(y_var))
    sel_at_sy   = SPEC(y_var, sel_step)
    raw_step_eq = TRANS(op_at_x_at_sy, sel_at_sy)
    # raw_step_eq : |- name x (SUC y) = clean_step[fn:=@pred_clean, n:=y].
    # Rewrite (@pred_clean) y -> name x y on the RHS.
    step_eq = REWRITE_RULE([SYM(op_at_x_at_y)], raw_step_eq)
    STEP_THM = GENL([x_var, y_var], step_eq)

    return BASE_THM, STEP_THM


# Surface registrations are now performed inline as each constant becomes
# available (see the `add_const(...)` calls above), so that
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
