"""Self-tests for proof.py — moved out of the module body (H17).

Run as ``python proof_test.py``. Splitting the tests out of ``proof.py``
also retires the ``sys.modules.setdefault("proof", ...)`` workaround:
``proof_test`` is ``__main__`` here, while ``proof`` loads cleanly under
its own name, so ``num.py``'s ``from proof import register_induction``
finds the same module instance.
"""

import nat
from nat import (
    ADD_1, ADD_SUC, UNFOLD_LE, LT_TO_LE, SATZ_1, SATZ_16A,
    AXIOM_3, AXIOM_4, GT_DEF, UNFOLD_GT, x as VX, y as VY, z as VZ,
)
from num import ONE, num_ty, SUC_DEF
from fusion import (
    mk_var, bool_ty, Var, ASSUME, EQ_MP, REFL, MK_COMB, aconv, concl,
    mk_eq, mk_fun_ty, mk_comb, mk_app, HolError,
)
from axioms import mk_forall
from tactics import SPEC, GEN, DISCH, SYM, AP_THM, BETA_RULE, NOT_ELIM, MP
from parser import parse, pp
from proof import proof, Proof, LazyLetDef


def main():
    @proof
    def SATZ_5_NEW(p):
        p.goal("!x y z. (x + y) + z = x + (y + z)")
        p.fix("x y z")
        with p.induction("z"):
            with p.base():
                p.thus("(x + y) + 1 = x + (y + 1)")\
                    .by_rewrite([ADD_1, ADD_SUC])
            with p.step("IH"):
                p.thus("(x + y) + SUC z = x + (y + SUC z)")\
                    .by_rewrite([ADD_SUC, "IH"])

    assert aconv(concl(SATZ_5_NEW), concl(nat.SATZ_5)), \
        f"SATZ_5 mismatch:\n  new: {pp(concl(SATZ_5_NEW))}\n  old: {pp(concl(nat.SATZ_5))}"
    assert SATZ_5_NEW._asl == nat.SATZ_5._asl

    # SATZ_17: x <= y, y <= z ==> x <= z. Cases on y < z \/ y = z.
    @proof
    def SATZ_17_NEW(p):
        p.goal("!x y z. x <= y ==> y <= z ==> x <= z")
        p.fix("x y z")
        p.assume("hxy: x <= y", "hyz: y <= z")
        p.have("yz_or: (y < z) \\/ (y = z)")\
            .by_eq_mp(UNFOLD_LE(VY, VZ), "hyz")
        with p.cases_on("yz_or"):
            with p.case("y < z"):
                p.have("xz_lt: x < z").by(SATZ_16A, "x", "y", "z", "hxy", -1)
                p.thus("x <= z").by(LT_TO_LE, "xz_lt")
            with p.case("y = z"):
                p.thus("x <= z").by_rewrite_of("hxy", [-1])

    assert aconv(concl(SATZ_17_NEW), concl(nat.SATZ_17)), \
        f"SATZ_17 mismatch:\n  new: {pp(concl(SATZ_17_NEW))}\n  old: {pp(concl(nat.SATZ_17))}"
    assert SATZ_17_NEW._asl == nat.SATZ_17._asl

    # ---- _Have.by_match smoke tests ------------------------------------
    # Pure-match: AXIOM_4 = !x y. SUC x = SUC y ==> x = y.  Goal `x = y`
    # determines both forall vars, so the call site lists only the
    # antecedent fact.
    @proof
    def SATZ_1_BY_MATCH(p):
        p.goal("!x y. ~(x = y) ==> ~(SUC x = SUC y)")
        p.fix("x y")
        p.assume("hxy: ~(x = y)")
        with p.suppose("h: SUC x = SUC y"):
            p.have("xy: x = y").by_match(AXIOM_4, "h")
            p.have("imp: (x = y) ==> F").by(NOT_ELIM, "hxy")
            p.thus("F").by(MP, "imp", "xy")
    assert aconv(concl(SATZ_1_BY_MATCH), concl(nat.SATZ_1)), \
        f"SATZ_1 by_match mismatch:\n  new: {pp(concl(SATZ_1_BY_MATCH))}\n  old: {pp(concl(nat.SATZ_1))}"
    assert SATZ_1_BY_MATCH._asl == nat.SATZ_1._asl

    # Name-collide: pattern var `x` and goal's outer-fixed `x` share a
    # name; first-order match still binds pattern x to `SUC x` and
    # pattern y to the outer `x`.
    @proof
    def SATZ_2_BY_MATCH(p):
        p.goal("!x. ~(SUC x = x)")
        p.fix("x")
        with p.induction("x"):
            with p.base():
                p.thus("~(SUC 1 = 1)").by_match(AXIOM_3)
            with p.step("IH"):
                p.thus("~(SUC (SUC x) = SUC x)").by_match(SATZ_1, "IH")
    assert aconv(concl(SATZ_2_BY_MATCH), concl(nat.SATZ_2)), \
        f"SATZ_2 by_match mismatch:\n  new: {pp(concl(SATZ_2_BY_MATCH))}\n  old: {pp(concl(nat.SATZ_2))}"
    assert SATZ_2_BY_MATCH._asl == nat.SATZ_2._asl

    # Middle-var with explicit term hint: SATZ_16A = !x y z. x <= y ==>
    # y < z ==> x < z.  Goal `x < z` leaves `y` undetermined; supplying
    # it as a leading term arg still works.
    @proof
    def SATZ_17_BY_MATCH(p):
        p.goal("!x y z. x <= y ==> y <= z ==> x <= z")
        p.fix("x y z")
        p.assume("hxy: x <= y", "hyz: y <= z")
        p.have("yz_or: (y < z) \\/ (y = z)")\
            .by_eq_mp(UNFOLD_LE(VY, VZ), "hyz")
        with p.cases_on("yz_or"):
            with p.case("y < z"):
                p.have("xz_lt: x < z").by_match(SATZ_16A, "y", "hxy", -1)
                p.thus("x <= z").by(LT_TO_LE, "xz_lt")
            with p.case("y = z"):
                p.thus("x <= z").by_rewrite_of("hxy", [-1])
    assert aconv(concl(SATZ_17_BY_MATCH), concl(nat.SATZ_17)), \
        f"SATZ_17 by_match mismatch:\n  new: {pp(concl(SATZ_17_BY_MATCH))}\n  old: {pp(concl(nat.SATZ_17))}"
    assert SATZ_17_BY_MATCH._asl == nat.SATZ_17._asl

    # Antecedent matching: same proof, but `y` is now inferred from
    # ``hxy``'s type (`x <= y` matches the first antecedent and binds y),
    # so no term arg is needed.
    @proof
    def SATZ_17_BY_MATCH_ANT(p):
        p.goal("!x y z. x <= y ==> y <= z ==> x <= z")
        p.fix("x y z")
        p.assume("hxy: x <= y", "hyz: y <= z")
        p.have("yz_or: (y < z) \\/ (y = z)")\
            .by_eq_mp(UNFOLD_LE(VY, VZ), "hyz")
        with p.cases_on("yz_or"):
            with p.case("y < z"):
                p.have("xz_lt: x < z").by_match(SATZ_16A, "hxy", -1)
                p.thus("x <= z").by(LT_TO_LE, "xz_lt")
            with p.case("y = z"):
                p.thus("x <= z").by_rewrite_of("hxy", [-1])
    assert aconv(concl(SATZ_17_BY_MATCH_ANT), concl(nat.SATZ_17)), \
        f"SATZ_17 by_match (ant) mismatch:\n  new: {pp(concl(SATZ_17_BY_MATCH_ANT))}\n  old: {pp(concl(nat.SATZ_17))}"
    assert SATZ_17_BY_MATCH_ANT._asl == nat.SATZ_17._asl

    # Error: fact concl does not match the antecedent's pattern.
    p_err = Proof()
    p_err.goal("!x y z. x <= y ==> y < z ==> x < z")
    p_err.fix("x y z")
    p_err.assume("hxy: x <= y", "hyz: y < z")
    try:
        # Swapped order: hyz (y < z) cannot match first antecedent
        # `x <= y`, so this is a step-3 (ordered) failure.
        p_err.have("xz: x < z").by_match(SATZ_16A, "hyz", "hxy")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for antecedent mismatch")

    # Error: conclusion of justification cannot match goal at all.
    p_err2 = Proof()
    p_err2.goal("1 = 1")
    try:
        p_err2.thus("1 = 1").by_match(AXIOM_4)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for unmatchable conclusion")

    # ---- p.let smoke tests (Isabelle-style) ----------------------------

    # (1) Basic round-trip via the lazy let: ``M 1`` (folded) is bridged
    # to ``1 = 1`` (REFL) through conversion-on-match in _finish.
    @proof
    def LET_REFL(p):
        p.goal("1 = 1")
        p.let("M(x) := x = x")
        p.thus("M 1").by_thm(REFL(ONE))
    assert aconv(concl(LET_REFL), parse("1 = 1"))

    # (2) Let-name in have-term, body closes over fix-var 'a'.
    @proof
    def LET_FIX(p):
        p.goal("!a. a = a")
        p.fix("a")
        p.let("M(x) := x = a")
        p.thus("M a").by_thm(REFL(mk_var("a", num_ty)))
    assert aconv(concl(LET_FIX), parse("!a. a = a"))

    # (3) Collision with fix-var refused.
    pp_proof = Proof()
    pp_proof.goal("!x. x = x")
    pp_proof.fix("x")
    try:
        pp_proof.let("x(y) := y = y")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for let/fix-var collision")

    # (4) Multi-arg let: ``R(a, b) := a + b = b + a`` proves
    # ``R 1 1`` from REFL of ``1 + 1`` via conversion-on-match.
    @proof
    def LET_MULTI(p):
        p.goal("1 + 1 = 1 + 1")
        p.let("R(a, b) := a + b = b + a")
        p.thus("R 1 1").by_thm(REFL(parse("1 + 1")))
    assert aconv(concl(LET_MULTI), parse("1 + 1 = 1 + 1"))

    # (5) by_select with a multi-arg let: trivial 2-ary HO axiom
    # ``|- !Q. Q 1 1 ==> Q 1 1`` at ``R(a, b) := a = b``.
    Q2_ty = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))
    Q2_var = mk_var("Q", Q2_ty)
    Q2_at_11 = mk_app(Q2_var, ONE, ONE)
    trivial_HO_2 = GEN(Q2_var, DISCH(Q2_at_11, ASSUME(Q2_at_11)))
    @proof
    def BY_SELECT_MULTI(p):
        p.goal("1 = 1")
        p.let("R(a, b) := a = b")
        p.have("R_11: R 1 1").by_thm(REFL(ONE))
        p.thus("R 1 1").by_select(trivial_HO_2, "R", "R_11")
    assert aconv(concl(BY_SELECT_MULTI), parse("1 = 1"))

    # (6) Bad spec rejected.
    try:
        Proof().let("R(a b) := a = b")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for malformed multi-arg spec")

    # (7) Duplicate argument names rejected.
    try:
        Proof().let("R(a, a) := a = a")
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for duplicate let arg names")

    # ---- p.unfold smoke test --------------------------------------------
    # Unary def: SUC_DEF : |- SUC = \n. mk_num (IND_SUC (dest_num n)).
    x_v = mk_var("x", num_ty)
    expected_unary = BETA_RULE(AP_THM(SUC_DEF, x_v))
    got_unary = Proof().unfold(SUC_DEF, x_v)
    assert aconv(got_unary._concl, expected_unary._concl), \
        "p.unfold (unary): mismatch"
    assert got_unary._asl == expected_unary._asl

    # Binary def: GT_DEF : |- > = \x y. ?u. x = y + u (defined in nat).
    expected_binary = UNFOLD_GT(VX, VY)
    got_binary = Proof().unfold(GT_DEF, VX, VY)
    assert aconv(got_binary._concl, expected_binary._concl), \
        "p.unfold (binary): mismatch"

    # String form: parses argument in current scope.
    p_str = Proof()
    p_str.goal("!x. x = x")
    p_str.fix("x")
    got_str = p_str.unfold(SUC_DEF, "x")
    assert aconv(got_str._concl, expected_unary._concl)

    # ---- _Have.by_select smoke test -------------------------------------
    # Build a tiny HO lemma `|- !P. P 1 ==> P 1` and apply by_select with a
    # let-defined predicate plus a witness fact, verifying the SPEC + BETA_RULE
    # + MP chain produces the right theorem.
    P_var = mk_var("P", mk_fun_ty(num_ty, bool_ty))
    P_1   = mk_comb(P_var, ONE)
    trivial_HO = GEN(P_var, DISCH(P_1, ASSUME(P_1)))   # |- !P. P 1 ==> P 1

    @proof
    def BY_SELECT_TEST(p):
        p.goal("1 = 1")
        p.let("M(x) := x = x")
        p.have("M_1: M 1").by_thm(REFL(ONE))
        p.thus("M 1").by_select(trivial_HO, "M", "M_1")
    assert aconv(concl(BY_SELECT_TEST), parse("1 = 1"))

    # ---- lazy-let registry smoke test -----------------------------------
    p_lazy = Proof()
    a_v = Var("a", num_ty)
    body_aa = mk_eq(a_v, a_v)                    # body: a = a (bool)
    ld = p_lazy._register_lazy_let("MX", [a_v], body_aa)
    # Carrier: Var named "MX" with type num -> bool.
    assert isinstance(ld.carrier, Var) and ld.carrier.name == "MX"
    assert ld.carrier.ty == mk_fun_ty(num_ty, bool_ty)
    # Equation conclusion: !a. MX a = (a = a).
    expected_eq = mk_forall(a_v, mk_eq(mk_comb(ld.carrier, a_v), body_aa))
    assert aconv(ld.eq_th._concl, expected_eq), \
        f"lazy-let eq mismatch: {pp(ld.eq_th._concl)} vs {pp(expected_eq)}"
    # Equation hypothesis: same as conclusion (introduced via ASSUME).
    assert len(ld.eq_th._asl) == 1 and aconv(ld.eq_th._asl[0], expected_eq), \
        f"lazy-let hyp mismatch: {ld.eq_th._asl}"
    # Lookup: scope chain finds it.
    assert p_lazy._lookup_lazy_let("MX") is ld
    assert p_lazy._lookup_lazy_let("missing") is None
    # Re-registration on the same frame raises.
    try:
        p_lazy._register_lazy_let("MX", [a_v], body_aa)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError on duplicate lazy-let register")
    # Multi-arg: MX2(a, b) := a = b.
    b_v = Var("b", num_ty)
    body_ab = mk_eq(a_v, b_v)
    ld2 = p_lazy._register_lazy_let("MX2", [a_v, b_v], body_ab)
    expected_ty2 = mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty))
    assert ld2.carrier.ty == expected_ty2
    expected_eq2 = mk_forall(a_v, mk_forall(b_v,
        mk_eq(mk_app(ld2.carrier, a_v, b_v), body_ab)))
    assert aconv(ld2.eq_th._concl, expected_eq2), \
        f"lazy-let multi-arg eq mismatch: {pp(ld2.eq_th._concl)}"

    # ---- lazy by_select smoke test --------------------------------------
    p_bsl = Proof()
    a_v_l = Var("x", num_ty)
    body_xx = mk_eq(a_v_l, a_v_l)
    lz = p_bsl._register_lazy_let("MZ", [a_v_l], body_xx)
    p_bsl.goal("MZ 1")
    eq_at_1 = SPEC(ONE, lz.eq_th)
    mz_1_th = EQ_MP(SYM(eq_at_1), REFL(ONE))
    p_bsl.have("MZ_1: MZ 1").by_thm(mz_1_th)
    p_bsl.thus("MZ 1").by_select(trivial_HO, "MZ", "MZ_1")
    assert p_bsl._cur.result is not None
    assert aconv(p_bsl._cur.result._concl, parse("MZ 1",
                                                  _env_bindings={"MZ": lz.carrier})), \
        f"lazy by_select: unexpected concl {pp(p_bsl._cur.result._concl)}"

    # ---- p.unfold_let / p.fold_let smoke test ---------------------------
    p_ul = Proof()
    x_v_u = Var("x", num_ty)
    plus_x_x = parse("x + x", _env_bindings={"x": x_v_u})
    lz_n = p_ul._register_lazy_let("MN", [x_v_u], plus_x_x)
    eq_at_one = p_ul.unfold_let("MN", ONE)
    expected = mk_eq(mk_comb(lz_n.carrier, ONE), parse("1 + 1"))
    assert aconv(eq_at_one._concl, expected), \
        f"unfold_let: {pp(eq_at_one._concl)} vs {pp(expected)}"
    p_ul.goal("MN 1 = 1 + 1")
    eq_str = p_ul.unfold_let("MN", "1")
    assert aconv(eq_str._concl, expected)
    try:
        p_ul.unfold_let("MN", ONE, ONE)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for unfold_let arity mismatch")
    try:
        p_ul.unfold_let("nope", ONE)
    except HolError:
        pass
    else:
        raise AssertionError("expected HolError for unfold_let missing name")
    eq_folded = p_ul.fold_let("MN", ONE)
    expected_fold = mk_eq(parse("1 + 1"), mk_comb(lz_n.carrier, ONE))
    assert aconv(eq_folded._concl, expected_fold), \
        f"fold_let: {pp(eq_folded._concl)} vs {pp(expected_fold)}"

    # ---- lazy let end-to-end smoke test --------------------------------
    @proof
    def LAZY_LET_END2END(p):
        p.let("MK(x) := x = x")
        p.goal("MK 1")
        p.thus("MK 1").by_eq_mp(p.fold_let("MK", ONE), REFL(ONE))
    assert LAZY_LET_END2END._asl == [], \
        f"lazy let: dangling hyp on result: {LAZY_LET_END2END._asl}"
    assert aconv(LAZY_LET_END2END._concl, parse("1 = 1")), \
        f"lazy let: unexpected concl {pp(LAZY_LET_END2END._concl)}"

    # ---- conversion-on-match smoke tests -------------------------------
    @proof
    def MATCH_FOLDED_TGT(p):
        p.let("MK(x) := x = x")
        p.goal("MK 1")
        p.thus("MK 1").by_thm(REFL(ONE))
    assert MATCH_FOLDED_TGT._asl == []
    assert aconv(MATCH_FOLDED_TGT._concl, parse("1 = 1"))

    @proof
    def MATCH_UNFOLDED_TGT(p):
        p.let("MK(x) := x = x")
        p.goal("1 = 1")
        p.have("MK_1: MK 1").by_eq_mp(p.fold_let("MK", ONE), REFL(ONE))
        p.thus("1 = 1").by_thm(p.fact("MK_1"))
    assert MATCH_UNFOLDED_TGT._asl == []
    assert aconv(MATCH_UNFOLDED_TGT._concl, parse("1 = 1"))

    # Non-terminating-rewrite guard: a synthetic self-referential lazy let
    # must not loop; conversion-on-match returns failure cleanly.
    p_loop = Proof()
    yv = Var("y", num_ty)
    M_carrier = Var("M", mk_fun_ty(num_ty, bool_ty))
    self_ref_body = mk_comb(M_carrier, yv)
    eq_term_loop = mk_forall(yv,
        mk_eq(mk_comb(M_carrier, yv), self_ref_body))
    p_loop._cur.lazy_lets["M"] = LazyLetDef(
        "M", [yv], self_ref_body, M_carrier, ASSUME(eq_term_loop))
    th_dummy = REFL(ONE)
    target_loop = parse("M 1", _env_bindings={"M": M_carrier})
    assert p_loop.simp_match(target_loop, th_dummy) is None, \
        "self-ref lazy let: match must fail cleanly"

    # ---- H13: assume preserves user surface form -----------------------
    @proof
    def H13_SURFACE(p):
        p.let("MK(x) := x = x")
        p.goal("MK 1 ==> MK 1")
        p.assume("h: MK 1")
        # User-facing fact's _concl is the surface form they wrote.
        assert aconv(p.fact("h")._concl,
                     parse("MK 1", _env_bindings=p._scope_env())), \
            f"H13: surface form not preserved: {pp(p.fact('h')._concl)}"
        p.thus("MK 1").by_thm(p.fact("h"))
    # Closed theorem matches the unfolded goal exactly.
    assert H13_SURFACE._asl == []
    assert aconv(H13_SURFACE._concl, parse("(1 = 1) ==> (1 = 1)"))

    print("proof.py self-tests passed.")


if __name__ == "__main__":
    main()
