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
from basics import mk_abs, mk_app, mk_const, mk_eq, rand
from axioms import (
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
from classical import NOT_NOT_ELIM
from num import num_ty
from nat import LT_DEF, SATZ_27
from nat0 import nat0_ty, abs_nat0, rep_nat0, REP_ABS, ABS_REP_NAT0
from parser import define, parse_type
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
            satz27_R = SPEC(
                R_pred, SATZ_27
            )  # |- (?n. R n) ==> ?m. R m /\ !k. R k ==> m <= k
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
            R_r0_unf = BETA_CONV(
                R_r0._concl
            )  # |- R r0_w = (?nn. r0_w = rep_nat0 nn /\ ~(P nn))
            R_r0_ex = EQ_MP(R_r0_unf, R_r0)

            # Choose n0.
            ex_at_r0_pred = R_r0_ex._concl.arg  # \nn. r0_w = rep_nat0 nn /\ ~(P nn)
            chose_n0 = CHOOSE_WITNESS(ex_at_r0_pred, R_r0_ex)
            # chose_n0 : |- r0_w = rep_nat0 n0_w /\ ~(P n0_w)
            #   where n0_w = @nn. ...
            r0_eq_rep = CONJUNCT1(chose_n0)
            nPn0 = CONJUNCT2(chose_n0)
            n0_w = (
                chose_n0._concl.fun.arg.arg
            )  # rep_nat0 n0_w from r0_w = rep_nat0 n0_w
            # Actually: chose_n0._concl is Comb(/\, fst, snd). fst = r0_w = rep_nat0 n0_w.
            # The n0_w is buried; let me just extract via term structure.
            # r0_eq_rep is r0_w = rep_nat0 n0_w; rand gives rep_nat0 n0_w; rand again gives n0_w.
            from basics import rand as _rand

            n0_w = _rand(_rand(r0_eq_rep._concl))

            # Prove !k. k <_0 n0_w ==> P k.
            k_var = Var("k", nat0_ty)
            # Inline proof.
            hk = ASSUME(mk_app(nat0_lt, k_var, n0_w))
            # rep_nat0 k < rep_nat0 n0_w via LT_NAT0.
            lt_eq = SPECL(
                [k_var, n0_w], LT_NAT0
            )  # |- nat0_lt k n0_w = (rep_nat0 k < rep_nat0 n0_w)
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
    from num import mk_suc

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
    lt_via_rep = REWRITE_RULE(
        [SYM(rep_suc0_n)], lt_in_suc
    )  # |- rep_n < rep_nat0 (SUC0 n)
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
        ex_eq = UNFOLD(
            LT_DEF, rep_n, rep_n
        )  # |- (rep_n < rep_n) = (?v. rep_n = rep_n + v)
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
        p.have("hmm: nat0_lt m m").by(NAT0_LT_TRANS, "m", "n", "m", "hmn", "hnm")
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
            p.have("step_lt: nat0_lt (SUC0 m) (SUC0 (SUC0 m))").by(
                NAT0_LT_SUC0, "SUC0 m"
            )
            p.thus("nat0_lt 0 (SUC0 (SUC0 m))").by(
                NAT0_LT_TRANS,
                "0",
                "SUC0 m",
                "SUC0 (SUC0 m)",
                "IH",
                "step_lt",
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


# ---------------------------------------------------------------------------
# Step 4.  Predecessor / case-on-SUC0 helpers, used by NUM_RECURSION_LT.
# ---------------------------------------------------------------------------
#
# NAT0_NOT_LT_ZERO :  |- !k. ~(nat0_lt k 0).
#   Unfolds to ``rep_nat0 k < rep_nat0 0 = 1``; but rep_nat0 lands in num
#   (1, 2, 3, ...) so rep_nat0 k >= 1, hence not < 1. Use SATZ_24
#   (``!x:num. x >= 1``) and contradiction via SATZ_25 / NOT_LT_AND_GE.


@proof
def NAT0_NOT_LT_ZERO(p):
    from nat import SATZ_24, _CONTRA_LT_GE
    from nat0 import ZERO_DEF
    from num import ONE

    p.goal("!k. ~(nat0_lt k 0)", types={"k": nat0_ty})
    p.fix("k")
    with p.suppose("h: nat0_lt k 0"):
        k_t = p._parse("k")
        rep_k = mk_app(rep_nat0, k_t)
        # Unfold nat0_lt and rep_nat0 0.
        lt_eq = SPECL([k_t, mk_const("0", [])], LT_NAT0)
        h_num = EQ_MP(lt_eq, p.fact("h"))  # |- rep_k < rep_nat0 0
        # rep_nat0 0 = 1 via ZERO_DEF + REP_ABS.
        rep0_eq = TRANS(AP_TERM(rep_nat0, ZERO_DEF), SPEC(ONE, REP_ABS))
        # |- rep_nat0 0 = 1
        h_lt_one = REWRITE_RULE([rep0_eq], h_num)  # |- rep_k < 1
        # rep_k >= 1 by SATZ_24.
        ge_one = SPEC(rep_k, SATZ_24)  # |- rep_k >= 1
        # _CONTRA_LT_GE : !a b. a < b ==> b >= a ==> F.
        contra = MP(
            MP(SPECL([rep_k, ONE], _CONTRA_LT_GE), h_lt_one),
            ge_one,
        )
        p.absurd().by_thm(contra)


# NAT0_NEQ_ZERO_PRED : |- !d. ~(d = 0) ==> ?d'. d = SUC0 d'.
#   Direct nat0 induction.


@proof
def NAT0_NEQ_ZERO_PRED(p):
    from fusion import REFL
    from nat0 import mk_suc0

    p.goal(
        "!d. ~(d = 0) ==> ?dp:nat0. d = SUC0 dp",
        types={"d": nat0_ty},
    )
    p.fix("d")
    with p.induction("d"):
        with p.base():
            p.assume("h: ~(0 = 0)")
            p.have("h_eq: 0 = 0").by_thm(REFL(mk_const("0", [])))
            p.absurd().by_conj("h", "h_eq")
        with p.step("IH_unused"):
            p.assume("h: ~(SUC0 d = 0)")
            d_t = p._parse("d")
            p.thus("?dp:nat0. SUC0 d = SUC0 dp").by_witness("d", REFL(mk_suc0(d_t)))


# NAT0_LT_SUC0_CASES :  |- !k d. nat0_lt k (SUC0 d) ==> k = d \/ nat0_lt k d.
#   In num: rep_nat0 k < SUC (rep_nat0 d) iff rep_nat0 k <= rep_nat0 d
#   (Landau SATZ_25/SATZ_22), and ``<= y`` splits as ``< y`` or ``= y``;
#   the equality lifts back to ``k = d`` via ABS_REP_NAT0.


@proof
def NAT0_LT_SUC0_CASES(p):
    from nat import SATZ_10, SATZ_25, ADD_1
    from nat0 import mk_suc0
    from num import mk_suc

    p.goal(
        "!k d. nat0_lt k (SUC0 d) ==> k = d \\/ nat0_lt k d",
        types={"k": nat0_ty, "d": nat0_ty},
    )
    p.fix("k d")
    p.assume("h: nat0_lt k (SUC0 d)")
    k_t, d_t = p._parse("k"), p._parse("d")
    rep_k = mk_app(rep_nat0, k_t)
    rep_d = mk_app(rep_nat0, d_t)
    # rep_k < SUC rep_d.
    lt_eq = SPECL([k_t, mk_suc0(d_t)], LT_NAT0)
    h_num = EQ_MP(lt_eq, p.fact("h"))  # |- rep_k < rep_nat0 (SUC0 d)
    rep_suc0_d = SPEC(d_t, REP_SUC0)
    h_lt_suc = REWRITE_RULE([rep_suc0_d], h_num)  # |- rep_k < SUC rep_d
    # SUC rep_d = rep_d + 1 by ADD_1 (sym).
    add1_d = SPEC(rep_d, ADD_1)  # |- rep_d + 1 = SUC rep_d
    # SATZ_10 : !x y. (x = y) \/ (x > y) \/ (x < y).
    tri = SPECL([rep_k, rep_d], SATZ_10)
    p.have(
        "tri: (rep_nat0 k = rep_nat0 d) \\/ (rep_nat0 k > rep_nat0 d) "
        "\\/ (rep_nat0 k < rep_nat0 d)"
    ).by_thm(tri)
    with p.cases_on("tri"):
        with p.case("heq: rep_nat0 k = rep_nat0 d"):
            # k = abs_nat0 (rep_nat0 k) = abs_nat0 (rep_nat0 d) = d.
            a_var = Var("a", nat0_ty)
            abs_k = INST([(k_t, a_var)], ABS_REP_NAT0)
            abs_d = INST([(d_t, a_var)], ABS_REP_NAT0)
            abs_eq = AP_TERM(abs_nat0, p.fact("heq"))
            # |- abs_nat0 (rep_nat0 k) = abs_nat0 (rep_nat0 d)
            k_eq_d = TRANS(SYM(abs_k), TRANS(abs_eq, abs_d))
            p.have("kd: k = d").by_thm(k_eq_d)
            p.thus("k = d \\/ nat0_lt k d").by_disj("kd")
        with p.case("rest: (rep_nat0 k > rep_nat0 d) \\/ (rep_nat0 k < rep_nat0 d)"):
            with p.cases_on("rest"):
                with p.case("hgt: rep_nat0 k > rep_nat0 d"):
                    # Contradicts h_lt_suc: rep_k < SUC rep_d.
                    # SATZ_25: a > b ==> a >= b + 1.
                    ge_th = MP(SPECL([rep_d, rep_k], SATZ_25), p.fact("hgt"))
                    # ge_th : rep_k >= rep_d + 1 = SUC rep_d.
                    ge_suc = REWRITE_RULE([add1_d], ge_th)
                    # Contradiction: h_lt_suc says rep_k < SUC rep_d.
                    from nat import _CONTRA_LT_GE

                    contra = MP(
                        MP(
                            SPECL([rep_k, mk_suc(rep_d)], _CONTRA_LT_GE),
                            h_lt_suc,
                        ),
                        ge_suc,
                    )
                    p.absurd().by_thm(contra)
                with p.case("hlt: rep_nat0 k < rep_nat0 d"):
                    kd_eq = SPECL([k_t, d_t], LT_NAT0)
                    p.have("klt: nat0_lt k d").by_eq_mp(SYM(kd_eq), p.fact("hlt"))
                    p.thus("k = d \\/ nat0_lt k d").by_disj("klt")


# NAT0_LT_SUC0_INV :  |- !a b. nat0_lt (SUC0 a) (SUC0 b) ==> nat0_lt a b.
#
# Inverse of NAT0_LT_SUC0_MONO. Apply NAT0_LT_SUC0_CASES to the hypothesis to
# get ``SUC0 a = b \/ nat0_lt (SUC0 a) b``; in the equality branch substitute
# b := SUC0 a and conclude via NAT0_LT_SUC0; in the strict branch chain
# ``nat0_lt a (SUC0 a)`` (NAT0_LT_SUC0) with the strict fact via NAT0_LT_TRANS.


@proof
def NAT0_LT_SUC0_INV(p):
    p.goal(
        "!a b. nat0_lt (SUC0 a) (SUC0 b) ==> nat0_lt a b",
        types={"a": nat0_ty, "b": nat0_ty},
    )
    p.fix("a b")
    p.assume("h: nat0_lt (SUC0 a) (SUC0 b)")
    p.have("h_cases: SUC0 a = b \\/ nat0_lt (SUC0 a) b").by(
        NAT0_LT_SUC0_CASES, "SUC0 a", "b", "h"
    )
    p.have("h_a_lt_sa: nat0_lt a (SUC0 a)").by(NAT0_LT_SUC0, "a")
    with p.cases_on("h_cases"):
        with p.case("h_eq: SUC0 a = b"):
            p.thus("nat0_lt a b").by_rewrite_of("h_a_lt_sa", ["h_eq"])
        with p.case("h_lt: nat0_lt (SUC0 a) b"):
            p.thus("nat0_lt a b").by(
                NAT0_LT_TRANS, "a", "SUC0 a", "b", "h_a_lt_sa", "h_lt"
            )


# ---------------------------------------------------------------------------
# Step 5.  NUM_RECURSION_LT -- polymorphic well-founded-recursion existence.
#
#   |- !F:(nat0 -> A) -> nat0 -> A.
#        (!f g n. (!k. nat0_lt k n ==> f k = g k) ==> F f n = F g n)
#        ==>
#        ?h:nat0 -> A. !n. h n = F h n.
#
# Strategy: depth-bounded recursion built on NUM_RECURSION_0.
#
#   1. Specialise NUM_RECURSION_0 at the value type ``nat0 -> A`` to get an
#      H : nat0 -> nat0 -> A satisfying
#          H 0       = (\n. ARB_A)
#          H (SUC0 d) = (\n. F (H d) n).
#   2. Define h := \n. H (SUC0 n) n.
#   3. Stabilization lemma (proved here by STRONG_INDUCTION_0 on k):
#          !d k. nat0_lt k d ==> H d k = h k.
#      Step at k: pick d > k. Then d = SUC0 d' (NAT0_NEQ_ZERO_PRED), and
#      k = d' or k <_0 d' (NAT0_LT_SUC0_CASES). Either way, every j < k
#      has j <_0 d' too, so by IH H d' j = h j and H k j = h j; combined
#      with MONO_F these give H (SUC0 d') k = F (H d') k = F (H k) k = h k.
#   4. !n. h n = F h n: apply stabilization at d := SUC0 n (every k < n
#      satisfies k <_0 SUC0 n).
# ---------------------------------------------------------------------------


def _build_mono_term(F_var, f_var, g_var, n_var, k_var, nat0_lt_const):
    """Build the MONO_F predicate:
         !f g n. (!k. nat0_lt k n ==> f k = g k) ==> F f n = F g n.
    Returns a HOL term (no theorem)."""
    inner = mk_forall(
        k_var,
        mk_imp(
            mk_app(nat0_lt_const, k_var, n_var),
            mk_eq(mk_app(f_var, k_var), mk_app(g_var, k_var)),
        ),
    )
    body = mk_imp(
        inner,
        mk_eq(
            mk_app(F_var, f_var, n_var),
            mk_app(F_var, g_var, n_var),
        ),
    )
    return mk_forall(f_var, mk_forall(g_var, mk_forall(n_var, body)))


def _prove_num_recursion_lt():
    from nat0 import (
        ZERO,
        mk_suc0,
        NUM_RECURSION_0,
    )
    from axioms import T, mk_select

    A = aty
    F_ty = parse_type("(nat0 -> A) -> nat0 -> A")
    nat0_to_A = parse_type("nat0 -> A")

    F_var = Var("F", F_ty)
    f_var = Var("f", nat0_to_A)
    g_var = Var("g", nat0_to_A)
    n_var = Var("n", nat0_ty)
    k_var = Var("k", nat0_ty)
    d_var = Var("d", nat0_ty)
    j_var = Var("j", nat0_ty)
    arb_A = mk_select(Var("v", A), T)  # ARB := @v:A. T

    # MONO_F as a term.
    mono_term = _build_mono_term(F_var, f_var, g_var, n_var, k_var, nat0_lt)

    # Step 1. Use NUM_RECURSION_0 at A := nat0_to_A.
    NR0_at = INST_TYPE([(nat0_to_A, aty)], NUM_RECURSION_0)
    # |- !c h. ?fn:nat0 -> nat0_to_A. fn 0 = c /\ !n. fn (SUC0 n) = h n (fn n)

    c_const = mk_abs(n_var, arb_A)  # \n. ARB_A
    # h_step (d:nat0) (prev:nat0_to_A) := \n. F prev n
    prev_var = Var("prev", nat0_to_A)
    h_step = mk_abs(
        d_var,
        mk_abs(
            prev_var,
            mk_abs(n_var, mk_app(F_var, prev_var, n_var)),
        ),
    )

    NR0_spec = SPEC(h_step, SPEC(c_const, NR0_at))
    # NR0_spec : ?fn. fn 0 = c_const /\ !d. fn (SUC0 d) = h_step d (fn d)

    pred_H = NR0_spec._concl.arg  # \fn. fn 0 = c_const /\ !d. ...
    H_props_raw = CHOOSE_WITNESS(pred_H, NR0_spec)
    # H_props_raw : H 0 = c_const /\ !d. H (SUC0 d) = h_step d (H d)
    # where H = @fn. ...
    H_term = mk_app(
        mk_const("@", [(nat0_to_A, aty)])
        if False
        else mk_const("@", [(parse_type("nat0 -> nat0 -> A"), aty)]),
        pred_H,
    )

    H_step_raw = CONJUNCT2(H_props_raw)  # !d. H (SUC0 d) = h_step d (H d)

    # Beta-reduce h_step to clean form: H (SUC0 d) = \n. F (H d) n.
    H_step_at_d_raw = SPEC(d_var, H_step_raw)  # H (SUC0 d) = h_step d (H d)
    # h_step d = \prev. \n. F prev n  (by beta)
    h_step_at_d = BETA_CONV(mk_app(h_step, d_var))
    # |- h_step d = (\prev. \n. F prev n)
    inner_app = AP_THM(h_step_at_d, mk_app(H_term, d_var))
    # |- h_step d (H d) = (\prev. \n. F prev n) (H d)
    inner_beta = BETA_CONV(rand(inner_app._concl))
    # |- (\prev. \n. F prev n) (H d) = (\n. F (H d) n)
    rhs_clean = TRANS(inner_app, inner_beta)
    # |- h_step d (H d) = (\n. F (H d) n)
    H_step_clean_at_d = TRANS(H_step_at_d_raw, rhs_clean)
    # |- H (SUC0 d) = (\n. F (H d) n)
    H_step_clean = GEN(d_var, H_step_clean_at_d)

    # Pointwise H (SUC0 d) n = F (H d) n.
    H_step_at = AP_THM(SPEC(d_var, H_step_clean), n_var)
    H_step_at = TRANS(H_step_at, BETA_CONV(rand(H_step_at._concl)))
    # |- H (SUC0 d) n = F (H d) n
    H_step_pt = GEN(d_var, GEN(n_var, H_step_at))

    # Step 2. Define h := \n. H (SUC0 n) n.
    h_term = mk_abs(n_var, mk_app(H_term, mk_suc0(n_var), n_var))

    # Pointwise h n = H (SUC0 n) n.
    h_at_n = BETA_CONV(mk_app(h_term, n_var))  # |- h n = H (SUC0 n) n
    h_at = GEN(n_var, h_at_n)

    # Step 3. Stabilization lemma:
    #   !d. nat0_lt k d ==> H d k = h k.
    # We prove the form !k. !d. nat0_lt k d ==> H d k = h k by strong induction on k.

    # Build the stab predicate: \k. !d. nat0_lt k d ==> H d k = h k.
    stab_body = mk_forall(
        d_var,
        mk_imp(
            mk_app(nat0_lt, k_var, d_var),
            mk_eq(
                mk_app(H_term, d_var, k_var),
                mk_app(h_term, k_var),
            ),
        ),
    )
    stab_pred = mk_abs(k_var, stab_body)

    # Stabilization is provable from MONO_F + NAT0_NEQ_ZERO_PRED + NAT0_LT_SUC0_CASES
    # + STRONG_INDUCTION_0. The proof below uses ASSUME(MONO_F) and
    # closes by GENERALIZE / DISCH at the end. Working under ASSUME(MONO_F):
    mono_assume = ASSUME(mono_term)

    # ----- Strong induction on k -----
    # Specialise STRONG_INDUCTION_0 at stab_pred:
    SI = SPEC(stab_pred, STRONG_INDUCTION_0)
    # Form: (!k. (!j. nat0_lt j k ==> stab_pred j) ==> stab_pred k) ==> !k. stab_pred k.
    # Beta-reduce SI's hypothesis and conclusion to working form.
    # Hypothesis we must prove: !k. (!j. nat0_lt j k ==> stab_body[k:=j]) ==> stab_body.
    # We work entirely under ASSUME(MONO_F) and produce stab : |- !k. !d. ...

    # The induction step: take k with IH "!j. nat0_lt j k ==> !d. nat0_lt j d ==> H d j = h j".
    # Show: !d. nat0_lt k d ==> H d k = h k.

    # IH_term: !j. nat0_lt j k ==> stab_body[k:=j]
    IH_term = mk_forall(
        j_var,
        mk_imp(
            mk_app(nat0_lt, j_var, k_var),
            mk_forall(
                d_var,
                mk_imp(
                    mk_app(nat0_lt, j_var, d_var),
                    mk_eq(
                        mk_app(H_term, d_var, j_var),
                        mk_app(h_term, j_var),
                    ),
                ),
            ),
        ),
    )
    IH_assume = ASSUME(IH_term)

    # Take d with nat0_lt k d.
    kd_lt_term = mk_app(nat0_lt, k_var, d_var)
    kd_lt_assume = ASSUME(kd_lt_term)  # |- nat0_lt k d

    # Step 3a. Show d ≠ 0. By NAT0_NOT_LT_ZERO at k: ~(nat0_lt k 0). If d=0, kd_lt_assume contradicts.
    # We prove ~(d = 0) by suppose-contradiction.
    d_eq_0_term = mk_eq(d_var, ZERO)
    d_eq_0_assume = ASSUME(d_eq_0_term)
    # Substitute d := 0 into kd_lt_assume.
    kd_lt_at_0 = REWRITE_RULE([d_eq_0_assume], kd_lt_assume)
    # |- nat0_lt k 0 (under d_eq_0_assume)
    not_lt_0_at_k = SPEC(k_var, NAT0_NOT_LT_ZERO)  # |- ~(nat0_lt k 0)
    contra_d_zero = MP(NOT_ELIM(not_lt_0_at_k), kd_lt_at_0)  # F (under hyps)
    # Discharge d_eq_0_assume to get ~(d = 0).
    d_neq_0 = NOT_INTRO(DISCH(d_eq_0_term, contra_d_zero))
    # |- ~(d = 0) (under {kd_lt_assume})

    # Step 3b. Get d' s.t. d = SUC0 d'.
    pred_d = MP(SPEC(d_var, NAT0_NEQ_ZERO_PRED), d_neq_0)
    # |- ?dp:nat0. d = SUC0 dp
    dp_pred = pred_d._concl.arg  # \dp. d = SUC0 dp
    pred_chosen = CHOOSE_WITNESS(dp_pred, pred_d)
    # |- d = SUC0 dp_w  (under hyps; dp_w := @dp. d = SUC0 dp)
    dp_w = rand(pred_chosen._concl)  # SUC0 dp_w; rand again to get dp_w
    dp_w = rand(dp_w)
    # Now pred_chosen : |- d = SUC0 dp_w.

    # Step 3c. nat0_lt k (SUC0 dp_w) (transport kd_lt_assume).
    k_lt_S_dp = REWRITE_RULE([pred_chosen], kd_lt_assume)
    # |- nat0_lt k (SUC0 dp_w)

    # Step 3d. By NAT0_LT_SUC0_CASES: k = dp_w \/ nat0_lt k dp_w.
    cases = MP(SPECL([k_var, dp_w], NAT0_LT_SUC0_CASES), k_lt_S_dp)
    # |- k = dp_w \/ nat0_lt k dp_w

    # Step 3e. Establish j_lt_dp : !j. nat0_lt j k ==> nat0_lt j dp_w.
    # In case k = dp_w: j < k = dp_w, so j < dp_w. Done by REWRITE.
    # In case nat0_lt k dp_w: j < k < dp_w, so j < dp_w by NAT0_LT_TRANS.
    # We use DISJ_CASES_TAC equivalent.
    j_lt_k_term = mk_app(nat0_lt, j_var, k_var)
    j_lt_k_assume = ASSUME(j_lt_k_term)  # |- nat0_lt j k

    # Branch 1: k = dp_w.
    k_eq_dp_term = mk_eq(k_var, dp_w)
    k_eq_dp_assume = ASSUME(k_eq_dp_term)
    j_lt_dp_via_eq = REWRITE_RULE([k_eq_dp_assume], j_lt_k_assume)
    # |- nat0_lt j dp_w (under {j_lt_k, k = dp_w})
    branch1 = DISCH(k_eq_dp_term, j_lt_dp_via_eq)
    # |- (k = dp_w) ==> nat0_lt j dp_w

    # Branch 2: nat0_lt k dp_w.
    k_lt_dp_term = mk_app(nat0_lt, k_var, dp_w)
    k_lt_dp_assume = ASSUME(k_lt_dp_term)
    j_lt_dp_via_trans = MP(
        MP(
            SPECL([j_var, k_var, dp_w], NAT0_LT_TRANS),
            j_lt_k_assume,
        ),
        k_lt_dp_assume,
    )
    branch2 = DISCH(k_lt_dp_term, j_lt_dp_via_trans)

    # Combine via DISJ_CASES.
    from tactics import DISJ_CASES

    j_lt_dp = DISJ_CASES(cases, branch1, branch2)
    # |- nat0_lt j dp_w (under {j_lt_k, kd_lt, mono})

    # Step 3f. Use IH at j to get H dp_w j = h j and H k j = h j.
    # IH at j: nat0_lt j k ==> !d. nat0_lt j d ==> H d j = h j.
    IH_at_j = SPEC(j_var, IH_assume)
    # |- nat0_lt j k ==> !d. nat0_lt j d ==> H d j = h j

    # Under j_lt_k_assume:
    IH_inner_at_j = MP(IH_at_j, j_lt_k_assume)
    # |- !d. nat0_lt j d ==> H d j = h j

    H_dp_j = MP(SPEC(dp_w, IH_inner_at_j), j_lt_dp)
    # |- H dp_w j = h j  (under {j_lt_k, kd_lt, mono, ...})

    H_k_j = MP(SPEC(k_var, IH_inner_at_j), j_lt_k_assume)
    # |- H k j = h j

    # H dp_w j = H k j (under same hyps).
    H_eq_at_j = TRANS(H_dp_j, SYM(H_k_j))
    # |- H dp_w j = H k j

    # Discharge j_lt_k to get !j. nat0_lt j k ==> H dp_w j = H k j.
    H_eq_dischk = DISCH(j_lt_k_term, H_eq_at_j)
    H_eq_forall = GEN(j_var, H_eq_dischk)
    # |- !j. nat0_lt j k ==> H dp_w j = H k j  (under {kd_lt, mono})

    # Step 3g. Apply MONO_F at f := H dp_w, g := H k, n := k.
    H_dp_curried = mk_app(H_term, dp_w)
    H_k_curried = mk_app(H_term, k_var)

    # mono_assume specialised: F (H dp_w) k = F (H k) k.
    mono_at = SPEC(k_var, SPEC(H_k_curried, SPEC(H_dp_curried, mono_assume)))
    # |- (!j. nat0_lt j k ==> H dp_w j = H k j) ==> F (H dp_w) k = F (H k) k

    # Need to rename bound j inside. The SPEC may have introduced k as a bound name, let's check.
    # mono_assume : !f g n. (!k. nat0_lt k n ==> f k = g k) ==> F f n = F g n.
    # SPEC(H_dp_curried, mono_assume): !g n. (!k. nat0_lt k n ==> H dp_w k = g k) ==> ...
    # Hmm: this might rename inner k automatically; let me trust the kernel.

    F_eq = MP(mono_at, H_eq_forall)
    # |- F (H dp_w) k = F (H k) k

    # Step 3h. H d k = F (H dp_w) k via H_step_pt at d := dp_w + pred_chosen.
    H_step_at_dp = SPEC(k_var, SPEC(dp_w, H_step_pt))
    # |- H (SUC0 dp_w) k = F (H dp_w) k
    H_step_at_d_via_eq = REWRITE_RULE([SYM(pred_chosen)], H_step_at_dp)
    # |- H d k = F (H dp_w) k

    # h k = H (SUC0 k) k = F (H k) k.
    h_at_k = SPEC(k_var, h_at)  # |- h k = H (SUC0 k) k
    H_step_at_k_eq = SPEC(k_var, SPEC(k_var, H_step_pt))
    # |- H (SUC0 k) k = F (H k) k
    h_eq_F_H_k = TRANS(h_at_k, H_step_at_k_eq)
    # |- h k = F (H k) k

    # Combine: H d k = F (H dp_w) k = F (H k) k = h k.
    final = TRANS(TRANS(H_step_at_d_via_eq, F_eq), SYM(h_eq_F_H_k))
    # |- H d k = h k  (under {kd_lt, mono, IH})

    # Discharge kd_lt then GEN d.
    final_dischd = DISCH(kd_lt_term, final)
    # |- nat0_lt k d ==> H d k = h k  (under {mono, IH})
    final_forall_d = GEN(d_var, final_dischd)
    # |- !d. nat0_lt k d ==> H d k = h k

    # Need to rebuild as stab_pred at k. stab_pred k = beta-reduced form.
    stab_at_k_eq = BETA_CONV(mk_app(stab_pred, k_var))
    # |- stab_pred k = (!d. nat0_lt k d ==> H d k = h k)
    stab_at_k_th = EQ_MP(SYM(stab_at_k_eq), final_forall_d)

    # Discharge IH_assume.
    IH_dischk_at_k = DISCH(IH_term, stab_at_k_th)
    # |- (!j. nat0_lt j k ==> stab_pred j) ==> stab_pred k -- but the LHS is in
    # terms of stab_body, not stab_pred j (beta). We need to rewrite IH to use stab_pred j.

    # Actually IH_assume's body uses j_lt_k_term but inner forall uses stab_body[k:=j], which
    # is what stab_pred j beta-reduces to. So we need to either accept this or convert.
    # Build the canonical IH form: !j. nat0_lt j k ==> stab_pred j.
    stab_at_j_eq = BETA_CONV(mk_app(stab_pred, j_var))
    # |- stab_pred j = (!d. nat0_lt j d ==> H d j = h j)
    canonical_IH = mk_forall(
        j_var,
        mk_imp(
            mk_app(nat0_lt, j_var, k_var),
            mk_app(stab_pred, j_var),
        ),
    )
    canonical_IH_assume = ASSUME(canonical_IH)
    # Convert canonical_IH to IH_term via stab_at_j_eq under each j.
    IH_inst_j = MP(SPEC(j_var, canonical_IH_assume), ASSUME(j_lt_k_term))
    # IH_inst_j : stab_pred j (under j_lt_k)
    IH_inst_j_unbeta = EQ_MP(stab_at_j_eq, IH_inst_j)
    # IH_inst_j_unbeta : !d. nat0_lt j d ==> H d j = h j (under {j_lt_k, canonical_IH})
    IH_dischj_at_j = DISCH(j_lt_k_term, IH_inst_j_unbeta)
    IH_forallj_canonical_form = GEN(j_var, IH_dischj_at_j)
    # |- !j. nat0_lt j k ==> (!d. nat0_lt j d ==> H d j = h j)  (under canonical_IH)
    # That's IH_term under canonical_IH; use this to discharge IH_assume in IH_dischk_at_k.

    # IH_dischk_at_k says: IH_term ==> stab_pred k.
    # Now derive stab_pred k under canonical_IH by MP.
    stab_at_k_under_canonical = MP(IH_dischk_at_k, IH_forallj_canonical_form)
    # |- stab_pred k (under canonical_IH + kd-related; but kd-related discharged already)

    # Now discharge canonical_IH and GEN k to satisfy the strong induction premise.
    si_premise_at_k = DISCH(canonical_IH, stab_at_k_under_canonical)
    # |- (!j. nat0_lt j k ==> stab_pred j) ==> stab_pred k
    si_premise = GEN(k_var, si_premise_at_k)
    # |- !k. (!j. nat0_lt j k ==> stab_pred j) ==> stab_pred k

    # Apply STRONG_INDUCTION_0.
    stab_concl = MP(SI, si_premise)
    # |- !k. stab_pred k

    # Unbeta to canonical form.
    stab_at_n = SPEC(n_var, stab_concl)  # stab_pred n
    stab_n_unbeta = EQ_MP(BETA_CONV(mk_app(stab_pred, n_var)), stab_at_n)
    # |- !d. nat0_lt n d ==> H d n = h n
    stab = GEN(n_var, stab_n_unbeta)
    # |- !n. !d. nat0_lt n d ==> H d n = h n
    # (under {mono})

    # Step 4. Recursion equation: !n. h n = F h n.
    # h n = H (SUC0 n) n by h_at; = F (H n) n by H_step_pt.
    # Need F (H n) n = F h n by mono with H n j = h j for j < n.
    # Use stab specialized at d := n: nat0_lt k n ==> H n k = h k.

    H_n_eq_h_at_k = MP(
        SPEC(n_var, SPEC(k_var, stab)),  # nat0_lt k n ==> H n k = h k
        ASSUME(mk_app(nat0_lt, k_var, n_var)),
    )
    # |- H n k = h k (under {nat0_lt k n, mono})
    H_n_eq_h_dischk = DISCH(mk_app(nat0_lt, k_var, n_var), H_n_eq_h_at_k)
    H_n_eq_h_forall = GEN(k_var, H_n_eq_h_dischk)

    # mono at f := H n, g := h, n := n: gives F (H n) n = F h n.
    H_n_curried = mk_app(H_term, n_var)
    h_curried = h_term
    mono_at_step = SPEC(n_var, SPEC(h_curried, SPEC(H_n_curried, mono_assume)))
    F_step_eq = MP(mono_at_step, H_n_eq_h_forall)
    # |- F (H n) n = F h n

    # Chain: h n = H (SUC0 n) n = F (H n) n = F h n.
    h_at_n_th = SPEC(n_var, h_at)  # h n = H (SUC0 n) n
    H_step_at_n_n = SPEC(n_var, SPEC(n_var, H_step_pt))  # H (SUC0 n) n = F (H n) n
    rec_eq = TRANS(TRANS(h_at_n_th, H_step_at_n_n), F_step_eq)
    # |- h n = F h n
    rec_eq_forall = GEN(n_var, rec_eq)
    # |- !n. h n = F h n

    # Witness h for ?h. !n. h n = F h n.
    exist_pred = mk_abs(
        Var("hh", nat0_to_A),
        mk_forall(
            n_var,
            mk_eq(
                mk_app(Var("hh", nat0_to_A), n_var),
                mk_app(F_var, Var("hh", nat0_to_A), n_var),
            ),
        ),
    )
    exist_th = EXISTS(exist_pred, h_term, rec_eq_forall)
    # |- ?h. !n. h n = F h n  (under {mono})

    # Discharge mono_assume + GEN F.
    final_th = DISCH(mono_term, exist_th)
    return GEN(F_var, final_th)


NUM_RECURSION_LT = _prove_num_recursion_lt()


# ---------------------------------------------------------------------------
# Step 6.  define_wf_lt -- declare a recursive function on ``nat0`` whose
# recursion is well-founded on ``nat0_lt`` (i.e. recursive calls go to
# strictly-smaller arguments).
#
# Caller provides the body F : (nat0 -> A) -> nat0 -> A and a proof that
# F's value at ``n`` only depends on f's values at ``k <_0 n`` (the
# monotonicity / well-foundedness side condition). The helper then:
#
#   1. SPECs NUM_RECURSION_LT at A and F, MPs through the mono proof to
#      get ``?h. !n. h n = F h n``.
#   2. Pulls ``h`` out via CHOOSE_WITNESS as a SELECT term.
#   3. Calls ``parser.define`` to bind the new constant to that SELECT term.
#   4. Rewrites the recursion equation through the new definition.
#
# Returns (NAME_DEF, REC) where:
#   NAME_DEF : |- name = (@h. !n. h n = F h n)         (definitional)
#   REC      : |- !n. name n = F name n                (recursion equation)
# ---------------------------------------------------------------------------


def _check_nat0_to_A(fn_ty):
    from fusion import Tyapp

    ok = isinstance(fn_ty, Tyapp) and fn_ty.tyop == "fun" and fn_ty.args[0] == nat0_ty
    if not ok:
        raise HolError(f"define_wf_lt: fn_ty must be 'nat0 -> A', got {fn_ty}")
    return fn_ty.args[1]


def define_wf_lt(name, fn_ty, F_term, mono_th, *, infix=None):
    """Declare ``name : nat0 -> A`` by well-founded recursion on nat0_lt.

    Args:
      name   -- string, the new constant.
      fn_ty  -- HOL type, must be ``nat0 -> A`` for some A.
      F_term -- term of type ``(nat0 -> A) -> nat0 -> A``: the body. The
                recursion equation will read ``name n = F_term name n``.
      mono_th -- theorem of shape
                  |- !f g n. (!k. nat0_lt k n ==> f k = g k)
                              ==> F_term f n = F_term g n.
      infix  -- forwarded to ``parser.define``.

    Returns: ``(NAME_DEF, REC_TH)``.
    """
    A_ty = _check_nat0_to_A(fn_ty)

    NR_at_A = INST_TYPE([(A_ty, aty)], NUM_RECURSION_LT)
    NR_at_F = SPEC(F_term, NR_at_A)
    exist_th = MP(NR_at_F, mono_th)
    # exist_th : |- ?hh. !n. hh n = F_term hh n

    pred_h = exist_th._concl.arg  # \hh. !n. hh n = F_term hh n
    h_props = CHOOSE_WITNESS(pred_h, exist_th)
    # h_props : |- !n. (h_w n) = F_term h_w n   where h_w = @hh. pred_h hh

    h_witness = mk_app(mk_const("@", [(fn_ty, aty)]), pred_h)
    NAME_DEF = define(name, fn_ty, h_witness, infix=infix)
    # NAME_DEF : |- name = h_witness

    REC_TH = REWRITE_RULE([SYM(NAME_DEF)], h_props)
    # REC_TH : |- !n. name n = F_term name n
    return NAME_DEF, REC_TH


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
    print("Step 4 OK -- predecessor / case-split helpers.")
    print("  NAT0_NOT_LT_ZERO   :", pp_thm(NAT0_NOT_LT_ZERO))
    print("  NAT0_NEQ_ZERO_PRED :", pp_thm(NAT0_NEQ_ZERO_PRED))
    print("  NAT0_LT_SUC0_CASES :", pp_thm(NAT0_LT_SUC0_CASES))
    print("  NAT0_LT_SUC0_INV   :", pp_thm(NAT0_LT_SUC0_INV))
    print("Step 5 OK -- NUM_RECURSION_LT (well-founded recursion existence).")
    print("  NUM_RECURSION_LT   :", pp_thm(NUM_RECURSION_LT))
