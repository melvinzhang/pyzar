"""Order on ``nat0``, lifted from ``num`` via the ``rep_nat0`` iso, plus the
strong-induction principle that bit-extensionality and other unbounded-
recursion proofs require.

Provides:
  * ``nat0_lt n m``   --  strict less-than on nat0 (= rep_nat0 n < rep_nat0 m).
  * ``LT_NAT0``       --  the unfolding equation.
  * ``STRONG_INDUCTION_0``
        |- !P. (!n. (!k. nat0_lt k n ==> P k) ==> P n) ==> !n. P n.

The order is a one-line lift; the strong-induction principle is derived
from num's least-element principle (``SATZ_27``) by transporting the
"least counterexample" argument across the iso.
"""

from fusion import (
    Var,
    aty,
    REFL,
    TRANS,
    ASSUME,
    EQ_MP,
    INST,
    INST_TYPE,
    HolError,
)
from basics import mk_abs, mk_app, mk_const, mk_eq, rand, rator
from axioms import (
    SELECT_AX,
    mk_and,
    mk_forall,
    mk_exists,
    mk_imp,
    mk_not,
)
from tactics import (
    AP_TERM,
    AP_THM,
    BETA_CONV,
    SYM,
    SPEC,
    SPECL,
    GEN,
    GENL,
    CONJ,
    CONJUNCT1,
    CONJUNCT2,
    DISCH,
    MP,
    NOT_ELIM,
    NOT_INTRO,
    EXISTS,
    CHOOSE_WITNESS,
    UNFOLD,
    REWRITE_RULE,
)
from classical import EXCLUDED_MIDDLE, NOT_NOT_ELIM, NOT_FORALL_TO_EX_NOT
from num import num_ty
from nat import LT_DEF, SATZ_27
from nat0 import nat0_ty, abs_nat0, rep_nat0, REP_ABS, ABS_REP_NAT0
from parser import define, parse_type, add_const
from proof import proof, StrongInductionStrategy, register_strong_induction


# Keep parser defaults intact for downstream modules; we'll annotate types
# explicitly on goals here (predicates over nat0 versus num intermix).

# Standard variable names.
_n = Var("n", nat0_ty)
_m = Var("m", nat0_ty)
_k = Var("k", nat0_ty)
_v = Var("v", nat0_ty)
_r = Var("r", num_ty)


# ---------------------------------------------------------------------------
# Step 1.  Definition of ``nat0_lt``.
#
#   nat0_lt n m  :=  rep_nat0 n < rep_nat0 m.
# ---------------------------------------------------------------------------

LT_NAT0_DEF = define(
    "nat0_lt",
    parse_type("nat0 -> nat0 -> bool"),
    "\\n:nat0. \\m:nat0. rep_nat0 n < rep_nat0 m",
)
nat0_lt = mk_const("nat0_lt", [])


def mk_nat0_lt(n_term, m_term):
    return mk_app(nat0_lt, n_term, m_term)


# Pointwise unfolding: |- !n m. nat0_lt n m = (rep_nat0 n < rep_nat0 m).
def _prove_lt_nat0_pointwise():
    # AP_THM(LT_NAT0_DEF, n) twice + BETA both times.
    th_n = AP_THM(LT_NAT0_DEF, _n)
    th_n_beta = BETA_CONV(rand(th_n._concl))
    th_n_eq = TRANS(th_n, th_n_beta)
    th_nm = AP_THM(th_n_eq, _m)
    th_nm_beta = BETA_CONV(rand(th_nm._concl))
    return GENL([_n, _m], TRANS(th_nm, th_nm_beta))


LT_NAT0 = _prove_lt_nat0_pointwise()


# ---------------------------------------------------------------------------
# Step 2.  STRONG_INDUCTION_0.
#
#   |- !P. (!n. (!k. nat0_lt k n ==> P k) ==> P n) ==> !n. P n.
#
# Strategy: by contradiction. From ~(!n. P n) get a counterexample n_bad.
# Define R r := ?n:nat0. r = rep_nat0 n /\ ~P n; n_bad witnesses that R is
# non-empty (at rep_nat0 n_bad). SATZ_27 (least element) on R yields a
# minimal r0 = rep_nat0 n0 with ~P n0. For any k with k <_0 n0 (i.e.
# rep_nat0 k < r0), if ~P k then rep_nat0 k would witness R, but rep_nat0 k
# < r0 contradicts minimality. So !k. k <_0 n0 ==> P k. The hypothesis H
# then yields P n0, contradicting ~P n0.
# ---------------------------------------------------------------------------

_P_nat0_ty = parse_type("nat0 -> bool")


@proof
def STRONG_INDUCTION_0(p):
    p.goal(
        "!P. (!n. (!k. nat0_lt k n ==> P k) ==> P n) ==> !n. P n",
        types={"P": _P_nat0_ty, "n": nat0_ty, "k": nat0_ty},
    )
    p.fix("P")
    p.assume("H: !n. (!k. nat0_lt k n ==> P k) ==> P n")

    # Build R as an explicit num-predicate (lambda) once and use SPEC of SATZ_27
    # at it; this avoids let-folding interactions with by_match / unfold helpers.
    nn_var = Var("nn", nat0_ty)
    P_var = Var("P", _P_nat0_ty)
    R_body = mk_exists(
        nn_var,
        mk_and(
            mk_eq(_r, mk_app(rep_nat0, nn_var)),
            mk_not(mk_app(P_var, nn_var)),
        ),
    )
    R_pred = mk_abs(_r, R_body)  # \r. ?nn. r = rep_nat0 nn /\ ~(P nn)

    with p.thus("!n. P n").proof():
        p.fix("n")
        with p.thus("P n").by_contradiction("hnPn: ~(P n)"):
            # Build the witness "R (rep_nat0 n)" using nn := n.
            n_t = p._parse("n")
            R_at_rep_n = mk_app(R_pred, mk_app(rep_nat0, n_t))
            beta_R_at = BETA_CONV(R_at_rep_n)
            # ex_pred = \nn. rep_nat0 n = rep_nat0 nn /\ ~(P nn).
            ex_pred_at_n = mk_abs(
                nn_var,
                mk_and(
                    mk_eq(mk_app(rep_nat0, n_t), mk_app(rep_nat0, nn_var)),
                    mk_not(mk_app(P_var, nn_var)),
                ),
            )
            ex_th_witness = EXISTS(
                ex_pred_at_n,
                n_t,
                CONJ(REFL(mk_app(rep_nat0, n_t)), p.fact("hnPn")),
            )  # |- ?nn. rep_nat0 n = rep_nat0 nn /\ ~(P nn)
            R_n_th = EQ_MP(SYM(beta_R_at), ex_th_witness)  # |- R (rep_nat0 n)
            p.have("R_n:").by_thm(R_n_th)

            # ?r. R r via EXISTS at r := rep_nat0 n.
            r_pred_for_ex = mk_abs(_r, mk_app(R_pred, _r))  # \r. R r
            Rne_th = EXISTS(r_pred_for_ex, mk_app(rep_nat0, n_t), R_n_th)
            p.have("Rne:").by_thm(Rne_th)

            # SATZ_27 specialised at R_pred: (?r. R r) ==> ?r0. R r0 /\ !s. R s ==> r0 <= s.
            satz27_R = SPEC(R_pred, SATZ_27)  # |- (?n. R n) ==> ?m. R m /\ !k. R k ==> m <= k
            # Wait — SATZ_27 has bound vars n, m, k in its statement. Let me carefully check.
            # SATZ_27 : !N. (?n. N n) ==> ?m. N m /\ !k. N k ==> m <= k.
            # SPEC(R_pred, SATZ_27) gives (?n. R_pred n) ==> ?m. R_pred m /\ !k. R_pred k ==> m <= k.
            # The SPEC includes BETA-conversion in pyzar (see `SPEC` in tactics).
            least_th = MP(satz27_R, Rne_th)
            p.have("least:").by_thm(least_th)
            p.choose(
                "r0: R r0 /\\ (!s. R s ==> r0 <= s)",
                from_=least_th,
            ) if False else None
            # Use direct CHOOSE_WITNESS instead.
            least_pred_inner = least_th._concl.arg  # \m. R_pred m /\ ...
            chose_least = CHOOSE_WITNESS(least_pred_inner, least_th)
            # chose_least : |- R_pred r0_witness /\ !k. R_pred k ==> r0_witness <= k
            #   where r0_witness = @m. R_pred m /\ !k. R_pred k ==> m <= k.

            R_r0 = CONJUNCT1(chose_least)  # |- R_pred r0_w
            min_r0 = CONJUNCT2(chose_least)  # |- !k. R_pred k ==> r0_w <= k

            # Unfold R r0 to get the existential.
            R_r0_unf = BETA_CONV(R_r0._concl)  # |- R r0_w = (?nn. r0_w = rep_nat0 nn /\ ~(P nn))
            R_r0_ex = EQ_MP(R_r0_unf, R_r0)

            # Choose n0.
            r0_w = R_r0._concl.arg  # the SELECT term
            ex_at_r0_pred = R_r0_ex._concl.arg  # \nn. r0_w = rep_nat0 nn /\ ~(P nn)
            chose_n0 = CHOOSE_WITNESS(ex_at_r0_pred, R_r0_ex)
            # chose_n0 : |- r0_w = rep_nat0 n0_w /\ ~(P n0_w)
            #   where n0_w = @nn. ...
            r0_eq_rep = CONJUNCT1(chose_n0)
            nPn0 = CONJUNCT2(chose_n0)
            n0_w = chose_n0._concl.fun.arg.arg  # rep_nat0 n0_w from r0_w = rep_nat0 n0_w
            # Actually: chose_n0._concl is Comb(/\, fst, snd). fst = r0_w = rep_nat0 n0_w.
            # The n0_w is buried; let me just extract via term structure.
            # r0_eq_rep is r0_w = rep_nat0 n0_w; rand gives rep_nat0 n0_w; rand again gives n0_w.
            from basics import rand as _rand
            n0_w = _rand(_rand(r0_eq_rep._concl))

            # Prove !k. k <_0 n0_w ==> P k.
            forallk_body_template = lambda kk: mk_imp(
                mk_app(nat0_lt, kk, n0_w),
                mk_app(P_var, kk),
            )

            k_var = Var("k", nat0_ty)
            forallk_at_k = forallk_body_template(k_var)
            # Inline proof.
            hk = ASSUME(mk_app(nat0_lt, k_var, n0_w))
            # rep_nat0 k < rep_nat0 n0_w via LT_NAT0.
            lt_eq = SPECL([k_var, n0_w], LT_NAT0)  # |- nat0_lt k n0_w = (rep_nat0 k < rep_nat0 n0_w)
            hk_lt = EQ_MP(lt_eq, hk)  # |- rep_nat0 k < rep_nat0 n0_w

            # By contradiction on P k.
            hnPk = ASSUME(mk_not(mk_app(P_var, k_var)))
            # Build R (rep_nat0 k).
            R_at_rep_k = mk_app(R_pred, mk_app(rep_nat0, k_var))
            beta_R_at_k = BETA_CONV(R_at_rep_k)
            ex_pred_at_k = mk_abs(
                nn_var,
                mk_and(
                    mk_eq(mk_app(rep_nat0, k_var), mk_app(rep_nat0, nn_var)),
                    mk_not(mk_app(P_var, nn_var)),
                ),
            )
            ex_at_k = EXISTS(
                ex_pred_at_k,
                k_var,
                CONJ(REFL(mk_app(rep_nat0, k_var)), hnPk),
            )
            R_k = EQ_MP(SYM(beta_R_at_k), ex_at_k)
            # Minimality: r0_w <= rep_nat0 k.
            le1 = MP(SPEC(mk_app(rep_nat0, k_var), min_r0), R_k)
            # Substitute r0_w = rep_nat0 n0_w into le1's LHS.
            from tactics import REWRITE_RULE as _RR
            le2 = _RR([r0_eq_rep], le1)
            # le2 : rep_nat0 n0_w <= rep_nat0 k.  Convert to rep_nat0 k >= rep_nat0 n0_w via SATZ_14.
            from nat import _CONTRA_LT_GE, SATZ_14

            ge_th = MP(
                SPECL(
                    [mk_app(rep_nat0, n0_w), mk_app(rep_nat0, k_var)],
                    SATZ_14,
                ),
                le2,
            )  # |- rep_nat0 k >= rep_nat0 n0_w
            contra = MP(
                MP(
                    SPECL(
                        [mk_app(rep_nat0, k_var), mk_app(rep_nat0, n0_w)],
                        _CONTRA_LT_GE,
                    ),
                    hk_lt,
                ),
                ge_th,
            )

            # contra : F (under hyps {ASSUME k_lt_n0w, ASSUME ~Pk, ...}).
            # Discharge ~P k via NOT_NOT_ELIM.
            not_not_Pk = NOT_INTRO(DISCH(mk_not(mk_app(P_var, k_var)), contra))
            Pk_th = NOT_NOT_ELIM(not_not_Pk)  # under the ASSUME of hk
            # Discharge hk.
            forallk_at_k_th = DISCH(mk_app(nat0_lt, k_var, n0_w), Pk_th)
            forallk_th = GEN(k_var, forallk_at_k_th)
            p.have("forallk:").by_thm(forallk_th)

            # H @ n0_w: P n0_w.
            Pn0w = MP(SPEC(n0_w, p.fact("H")), forallk_th)
            p.have("Pn0:").by_thm(Pn0w)

            # Contradicts ~P n0_w.
            p.absurd().by_conj("Pn0", nPn0)


# ---------------------------------------------------------------------------
# Step 3.  Order-lifting helpers used downstream (bits.py for HALF_LT).
# ---------------------------------------------------------------------------


# REP_SUC0 :  |- !n. rep_nat0 (SUC0 n) = SUC (rep_nat0 n).
#
#   SUC0 n = (\m. abs_nat0 (SUC (rep_nat0 m))) n        by AP_THM SUC0_DEF
#          = abs_nat0 (SUC (rep_nat0 n))                 by BETA
# rep_nat0 (SUC0 n) = rep_nat0 (abs_nat0 (SUC (rep_nat0 n))) = SUC (rep_nat0 n)
#                                                        by AP_TERM rep_nat0
#                                                           and REP_ABS.
def _prove_rep_suc0():
    from nat0 import SUC0_DEF
    from num import SUC, mk_suc

    suc0_at_n = AP_THM(SUC0_DEF, _n)
    beta = BETA_CONV(rand(suc0_at_n._concl))
    suc0_unfold = TRANS(suc0_at_n, beta)  # |- SUC0 n = abs_nat0 (SUC (rep_nat0 n))
    rep_app = AP_TERM(rep_nat0, suc0_unfold)
    rep_abs = SPEC(mk_suc(mk_app(rep_nat0, _n)), REP_ABS)
    return GEN(_n, TRANS(rep_app, rep_abs))


REP_SUC0 = _prove_rep_suc0()


# Register strong induction on nat0 with the proof DSL so users can
# write ``with p.strong_induction("n", "IH"): ...`` for nat0-typed
# variables.
register_strong_induction(
    StrongInductionStrategy(ty=nat0_ty, lt=nat0_lt, thm=STRONG_INDUCTION_0)
)


# NAT0_LT_SUC0 :  |- !n. nat0_lt n (SUC0 n).
#
# rep_nat0 n < rep_nat0 (SUC0 n) = SUC (rep_nat0 n).
# In num: x < SUC x  via  SATZ_18 (x + 1 > x), SATZ_11 (x > y ==> y < x), and ADD_1 (x + 1 = SUC x).
@proof
def NAT0_LT_SUC0(p):
    from nat import SATZ_18, SATZ_11, ADD_1

    p.goal("!n:nat0. nat0_lt n (SUC0 n)", types={"n": nat0_ty})
    p.fix("n")
    n_t = p._parse("n")
    rep_n = mk_app(rep_nat0, n_t)
    # rep_n + 1 > rep_n
    gt = SPECL([rep_n, mk_const("1", [])], SATZ_18)  # |- rep_n + 1 > rep_n
    # rep_n < rep_n + 1
    lt_in_num = MP(
        SPECL([mk_app(mk_const("+", []), rep_n, mk_const("1", [])), rep_n], SATZ_11),
        gt,
    )  # |- rep_n < rep_n + 1
    # rep_n + 1 = SUC rep_n
    add1_n = SPEC(rep_n, ADD_1)  # |- rep_n + 1 = SUC rep_n
    lt_in_suc = REWRITE_RULE([add1_n], lt_in_num)  # |- rep_n < SUC rep_n
    # SUC rep_n = rep_nat0 (SUC0 n) via SYM REP_SUC0.
    rep_suc0_n = SPEC(n_t, REP_SUC0)  # |- rep_nat0 (SUC0 n) = SUC (rep_nat0 n)
    lt_via_rep = REWRITE_RULE([SYM(rep_suc0_n)], lt_in_suc)  # |- rep_n < rep_nat0 (SUC0 n)
    # Fold via LT_NAT0.
    lt_eq = SPECL([n_t, mk_app(mk_const("SUC0", []), n_t)], LT_NAT0)
    p.thus("nat0_lt n (SUC0 n)").by_eq_mp(SYM(lt_eq), lt_via_rep)


# NAT0_LT_TRANS :  |- !a b c. nat0_lt a b ==> nat0_lt b c ==> nat0_lt a c.
@proof
def NAT0_LT_TRANS(p):
    from nat import SATZ_15

    p.goal(
        "!a b c. nat0_lt a b ==> nat0_lt b c ==> nat0_lt a c",
        types={"a": nat0_ty, "b": nat0_ty, "c": nat0_ty},
    )
    p.fix("a b c")
    p.assume("hab: nat0_lt a b", "hbc: nat0_lt b c")
    a_t, b_t, c_t = p._parse("a"), p._parse("b"), p._parse("c")
    ab_eq = SPECL([a_t, b_t], LT_NAT0)
    bc_eq = SPECL([b_t, c_t], LT_NAT0)
    ac_eq = SPECL([a_t, c_t], LT_NAT0)
    hab_num = EQ_MP(ab_eq, p.fact("hab"))
    hbc_num = EQ_MP(bc_eq, p.fact("hbc"))
    rep_a = mk_app(rep_nat0, a_t)
    rep_b = mk_app(rep_nat0, b_t)
    rep_c = mk_app(rep_nat0, c_t)
    hac_num = MP(MP(SPECL([rep_a, rep_b, rep_c], SATZ_15), hab_num), hbc_num)
    p.thus("nat0_lt a c").by_eq_mp(SYM(ac_eq), hac_num)


# NAT0_LT_NOT_REFL :  |- !n. ~(nat0_lt n n).
#
# Lift the num irreflexivity ``~(x < x)`` (extracted from SATZ_9_EXCL_13
# at y := x via REFL) through ``LT_NAT0``.
@proof
def NAT0_LT_NOT_REFL(p):
    from nat import _SATZ_9_EXCL_13

    p.goal("!n. ~(nat0_lt n n)", types={"n": nat0_ty})
    p.fix("n")
    with p.suppose("h: nat0_lt n n"):
        n_t = p._parse("n")
        rep_n = mk_app(rep_nat0, n_t)
        nn_eq = SPECL([n_t, n_t], LT_NAT0)
        h_num = EQ_MP(nn_eq, p.fact("h"))  # |- rep_n < rep_n
        # x < y unfolds to ?v. y = x + v.
        ex_eq = UNFOLD(LT_DEF, rep_n, rep_n)  # |- (rep_n < rep_n) = (?v. rep_n = rep_n + v)
        ex_th = EQ_MP(ex_eq, h_num)  # |- ?v. rep_n = rep_n + v
        # _SATZ_9_EXCL_13 : !x y. ~(x = y /\ ?v. y = x + v).
        excl = SPECL([rep_n, rep_n], _SATZ_9_EXCL_13)
        # Build (rep_n = rep_n /\ ?v. rep_n = rep_n + v).
        conj_th = CONJ(REFL(rep_n), ex_th)
        p.absurd().by_thm(MP(NOT_ELIM(excl), conj_th))


# NAT0_LT_ASYM :  |- !m n. nat0_lt m n ==> ~(nat0_lt n m).
#
# By NAT0_LT_TRANS + NAT0_LT_NOT_REFL: m < n /\ n < m gives m < m.
@proof
def NAT0_LT_ASYM(p):
    p.goal("!m n. nat0_lt m n ==> ~(nat0_lt n m)", types={"m": nat0_ty, "n": nat0_ty})
    p.fix("m n")
    p.assume("hmn: nat0_lt m n")
    with p.suppose("hnm: nat0_lt n m"):
        p.have("hmm: nat0_lt m m").by(
            NAT0_LT_TRANS, "m", "n", "m", "hmn", "hnm"
        )
        p.have("nrefl: ~(nat0_lt m m)").by(NAT0_LT_NOT_REFL, "m")
        p.absurd().by_conj("nrefl", "hmm")


# NAT0_LT_SUC0_MONO :  |- !n m. nat0_lt n m ==> nat0_lt (SUC0 n) (SUC0 m).
#
# Witness: rep_nat0 n < rep_nat0 m  ==>  SUC (rep_nat0 n) < SUC (rep_nat0 m).
# In num: SATZ_19C with z := 1 gives x + 1 < y + 1 from x < y; ADD_1 turns into SUC.
@proof
def NAT0_LT_SUC0_MONO(p):
    from nat import SATZ_19C, ADD_1

    p.goal(
        "!n m. nat0_lt n m ==> nat0_lt (SUC0 n) (SUC0 m)",
        types={"n": nat0_ty, "m": nat0_ty},
    )
    p.fix("n m")
    p.assume("h: nat0_lt n m")
    n_t, m_t = p._parse("n"), p._parse("m")
    rep_n = mk_app(rep_nat0, n_t)
    rep_m = mk_app(rep_nat0, m_t)
    nm_eq = SPECL([n_t, m_t], LT_NAT0)
    h_num = EQ_MP(nm_eq, p.fact("h"))  # |- rep_n < rep_m
    one_t = mk_const("1", [])
    plus = mk_const("+", [])
    h_plus_one = MP(SPECL([rep_n, rep_m, one_t], SATZ_19C), h_num)
    # |- rep_n + 1 < rep_m + 1
    add1_n = SPEC(rep_n, ADD_1)
    add1_m = SPEC(rep_m, ADD_1)
    h_suc = REWRITE_RULE([add1_n, add1_m], h_plus_one)
    # |- SUC rep_n < SUC rep_m
    rep_suc0_n = SPEC(n_t, REP_SUC0)
    rep_suc0_m = SPEC(m_t, REP_SUC0)
    h_via_rep = REWRITE_RULE([SYM(rep_suc0_n), SYM(rep_suc0_m)], h_suc)
    # |- rep_nat0 (SUC0 n) < rep_nat0 (SUC0 m)
    SUC0_c = mk_const("SUC0", [])
    sn_sm_eq = SPECL([mk_app(SUC0_c, n_t), mk_app(SUC0_c, m_t)], LT_NAT0)
    p.thus("nat0_lt (SUC0 n) (SUC0 m)").by_eq_mp(SYM(sn_sm_eq), h_via_rep)


# NAT0_LT_0_SUC0 :  |- !m. nat0_lt 0 (SUC0 m).
#
# Induction on m.  Base: nat0_lt 0 (SUC0 0) by NAT0_LT_SUC0 at 0.  Step: chain
# IH (nat0_lt 0 (SUC0 m)) with NAT0_LT_SUC0 at SUC0 m (giving
# nat0_lt (SUC0 m) (SUC0 (SUC0 m))) through NAT0_LT_TRANS.
@proof
def NAT0_LT_0_SUC0(p):
    p.goal("!m. nat0_lt 0 (SUC0 m)", types={"m": nat0_ty})
    p.fix("m")
    with p.induction("m"):
        with p.base():
            p.thus("nat0_lt 0 (SUC0 0)").by(NAT0_LT_SUC0, "0")
        with p.step("IH"):
            p.have(
                "step_lt: nat0_lt (SUC0 m) (SUC0 (SUC0 m))"
            ).by(NAT0_LT_SUC0, "SUC0 m")
            p.thus("nat0_lt 0 (SUC0 (SUC0 m))").by(
                NAT0_LT_TRANS,
                "0", "SUC0 m", "SUC0 (SUC0 m)",
                "IH", "step_lt",
            )


# NAT0_LT_SUC0_INSERT :
#   |- !a b c. nat0_lt a b ==> nat0_lt b c ==> nat0_lt (SUC0 a) c.
#
# In num, "a < b" is "a + 1 ≤ b".  Combining with "b < c" via SATZ_16A gives
# "a + 1 < c"; ADD_1 rewrites a + 1 to SUC a, and REP_SUC0 folds back into
# nat0.
@proof
def NAT0_LT_SUC0_INSERT(p):
    from nat import SATZ_25, SATZ_13, SATZ_16A, SATZ_12, ADD_1

    p.goal(
        "!a b c. nat0_lt a b ==> nat0_lt b c ==> nat0_lt (SUC0 a) c",
        types={"a": nat0_ty, "b": nat0_ty, "c": nat0_ty},
    )
    p.fix("a b c")
    p.assume("hab: nat0_lt a b", "hbc: nat0_lt b c")
    a_t, b_t, c_t = p._parse("a"), p._parse("b"), p._parse("c")
    SUC0_c = mk_const("SUC0", [])
    rep_a = mk_app(rep_nat0, a_t)
    rep_b = mk_app(rep_nat0, b_t)
    rep_c = mk_app(rep_nat0, c_t)
    plus_c = mk_const("+", [])
    one_t = mk_const("1", [])
    a_plus_1 = mk_app(plus_c, rep_a, one_t)

    ab_eq = SPECL([a_t, b_t], LT_NAT0)
    bc_eq = SPECL([b_t, c_t], LT_NAT0)
    sa_c_eq = SPECL([mk_app(SUC0_c, a_t), c_t], LT_NAT0)

    hab_num = EQ_MP(ab_eq, p.fact("hab"))  # |- rep_a < rep_b
    hbc_num = EQ_MP(bc_eq, p.fact("hbc"))  # |- rep_b < rep_c

    # rep_b > rep_a, hence rep_b >= rep_a + 1 (Landau Theorem 25).
    b_gt_a = MP(SPECL([rep_a, rep_b], SATZ_12), hab_num)
    b_ge = MP(SPECL([rep_a, rep_b], SATZ_25), b_gt_a)
    # Reorient via SATZ_13: rep_a + 1 <= rep_b.
    a1_le_b = MP(SPECL([rep_b, a_plus_1], SATZ_13), b_ge)
    # SATZ_16A then chains with hbc_num to give rep_a + 1 < rep_c.
    a1_lt_c = MP(
        MP(SPECL([a_plus_1, rep_b, rep_c], SATZ_16A), a1_le_b),
        hbc_num,
    )
    # rep_a + 1 = SUC rep_a; rep_nat0 (SUC0 a) = SUC rep_a.
    add1_eq = SPEC(rep_a, ADD_1)  # |- rep_a + 1 = SUC rep_a
    suc_a_lt_c = REWRITE_RULE([add1_eq], a1_lt_c)
    rep_suc0_eq = SPEC(a_t, REP_SUC0)
    sa_lt_c = REWRITE_RULE([SYM(rep_suc0_eq)], suc_a_lt_c)
    p.thus("nat0_lt (SUC0 a) c").by_eq_mp(SYM(sa_c_eq), sa_lt_c)


if __name__ == "__main__":
    from parser import pp_thm

    print("Step 1 OK -- nat0_lt defined.")
    print("  LT_NAT0_DEF :", pp_thm(LT_NAT0_DEF))
    print("  LT_NAT0     :", pp_thm(LT_NAT0))
    print("Step 2 OK -- STRONG_INDUCTION_0 proved.")
    print("  STRONG_INDUCTION_0:", pp_thm(STRONG_INDUCTION_0))
    print("Step 3 OK -- order helpers (REP_SUC0, NAT0_LT_SUC0/_TRANS/_MONO).")
    print("  REP_SUC0           :", pp_thm(REP_SUC0))
    print("  NAT0_LT_SUC0       :", pp_thm(NAT0_LT_SUC0))
    print("  NAT0_LT_TRANS      :", pp_thm(NAT0_LT_TRANS))
    print("  NAT0_LT_NOT_REFL   :", pp_thm(NAT0_LT_NOT_REFL))
    print("  NAT0_LT_ASYM       :", pp_thm(NAT0_LT_ASYM))
    print("  NAT0_LT_SUC0_MONO  :", pp_thm(NAT0_LT_SUC0_MONO))
    print("  NAT0_LT_0_SUC0     :", pp_thm(NAT0_LT_0_SUC0))
    print("  NAT0_LT_SUC0_INSERT:", pp_thm(NAT0_LT_SUC0_INSERT))
