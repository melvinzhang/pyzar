import unittest
import fusion
from fusion import (
    Tyvar, Tyapp, Var, Const, Comb, Abs,
    bool_ty, aty,
    mk_type,
    tyvars, type_subst,
    types, get_type_arity, new_type,
    constants, get_const_type, new_constant,
    mk_comb,
    type_of, frees, freesin, vfree_in,
    type_vars_in_term, variant, vsubst, inst,
    alphaorder,
    dest_thm, hyp, concl,
    REFL, TRANS, MK_COMB, ABS, BETA, ASSUME, EQ_MP,
    DEDUCT_ANTISYM_RULE, INST_TYPE, INST,
    axioms, new_axiom, definitions, new_basic_definition,
    new_basic_type_definition,
)
from basics import (
    bty,
    mk_vartype, dest_type, dest_vartype, is_type, is_vartype,
    mk_var, mk_const, mk_abs,
    dest_var, dest_const, dest_comb, dest_abs,
    is_var, is_const, is_abs, is_comb,
    freesl,
    rator, rand, dest_eq,
    aconv,
    mk_fun_ty, is_eq, mk_eq, equals_thm,
)


# ---------------------------------------------------------------------------
# Sanity check — fast end-to-end composition test that fails loudly if any
# primitive interaction is broken. Runs first so a misbuilt kernel surfaces
# before the per-primitive suites.
# ---------------------------------------------------------------------------

class TestKernelSanity(unittest.TestCase):

    def test_primitives_compose_into_a_derivation(self):
        # Derive   |- (\x. f x) x = f x   by BETA on the trivial redex
        # (the only one this kernel admits), then transport an assumption
        # through it with EQ_MP, exercising:
        # mk_var/mk_const/mk_abs/mk_comb, type_of, REFL, BETA, TRANS,
        # ASSUME, EQ_MP, term_union, alphaorder.
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        x = mk_var("x", bool_ty)
        redex = mk_comb(mk_abs(x, mk_comb(f, x)), x)   # (\x. f x) x
        beta_th = BETA(redex)                          # |- (\x. f x) x = f x
        lhs, rhs = dest_eq(concl(beta_th))
        self.assertEqual(lhs, redex)
        self.assertEqual(rhs, mk_comb(f, x))
        # Chain BETA with REFL via TRANS — middle terms must alpha-match.
        chained = TRANS(beta_th, REFL(mk_comb(f, x)))
        self.assertTrue(aconv(concl(chained), concl(beta_th)))
        # Use the equation to transport a hypothesis: {redex} |- f x.
        transported = EQ_MP(beta_th, ASSUME(redex))
        self.assertEqual(concl(transported), mk_comb(f, x))
        self.assertEqual(hyp(transported), [redex])

    def test_alpha_and_capture_avoidance_cooperate(self):
        # INST replacing x with y inside (\y. x) must rename the binder,
        # and the result must be alpha-equivalent to (\z. y) for fresh z.
        x = mk_var("x", bool_ty)
        y = mk_var("y", bool_ty)
        ab = mk_abs(y, x)
        renamed = INST([(y, x)], REFL(ab))
        lhs, rhs = dest_eq(concl(renamed))
        bv, body = dest_abs(lhs)
        self.assertNotEqual(bv, y)
        self.assertEqual(body, y)
        self.assertTrue(aconv(lhs, rhs))

    def test_inst_type_threads_through_kernel(self):
        # |- x:A = x:A  instantiated with A := bool  must yield  |- x:bool = x:bool.
        x_a = mk_var("x", aty)
        th = INST_TYPE([(bool_ty, aty)], REFL(x_a))
        x_b = mk_var("x", bool_ty)
        self.assertTrue(aconv(concl(th), mk_eq(x_b, x_b)))


class KernelStateTestCase(unittest.TestCase):
    """Base class that saves and restores kernel global state."""

    def setUp(self):
        self._saved_types = list(fusion.the_type_constants)
        self._saved_terms = list(fusion.the_term_constants)
        self._saved_axioms = list(fusion.the_axioms)
        self._saved_defs = list(fusion.the_definitions)

    def tearDown(self):
        fusion.the_type_constants[:] = self._saved_types
        fusion.the_term_constants[:] = self._saved_terms
        fusion.the_axioms[:] = self._saved_axioms
        fusion.the_definitions[:] = self._saved_defs


# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

class TestTypes(unittest.TestCase):

    def test_bool_ty_is_tyapp(self):
        self.assertIsInstance(bool_ty, Tyapp)
        self.assertEqual(bool_ty.tyop, "bool")
        self.assertEqual(list(bool_ty.args), [])

    def test_aty_is_tyvar(self):
        self.assertIsInstance(aty, Tyvar)
        self.assertEqual(aty.name, "A")

    def test_mk_vartype(self):
        tv = mk_vartype("X")
        self.assertIsInstance(tv, Tyvar)
        self.assertEqual(tv.name, "X")

    def test_mk_type_known(self):
        ty = mk_type("fun", [bool_ty, bool_ty])
        self.assertIsInstance(ty, Tyapp)
        self.assertEqual(ty.tyop, "fun")
        self.assertEqual(list(ty.args), [bool_ty, bool_ty])

    def test_mk_type_unknown(self):
        with self.assertRaises(Exception):
            mk_type("nosuchtype", [])

    def test_mk_type_wrong_arity(self):
        with self.assertRaises(Exception):
            mk_type("fun", [bool_ty])  # fun needs 2 args

    def test_dest_type(self):
        ty = mk_type("fun", [bool_ty, aty])
        name, args = dest_type(ty)
        self.assertEqual(name, "fun")
        self.assertEqual(args, [bool_ty, aty])

    def test_dest_type_on_tyvar_fails(self):
        with self.assertRaises(Exception):
            dest_type(aty)

    def test_dest_vartype(self):
        self.assertEqual(dest_vartype(aty), "A")

    def test_dest_vartype_on_tyapp_fails(self):
        with self.assertRaises(Exception):
            dest_vartype(bool_ty)

    def test_is_type(self):
        self.assertTrue(is_type(bool_ty))
        self.assertFalse(is_type(aty))

    def test_is_vartype(self):
        self.assertTrue(is_vartype(aty))
        self.assertFalse(is_vartype(bool_ty))

    def test_tyvars_tyvar(self):
        self.assertEqual(tyvars(aty), [aty])

    def test_tyvars_tyapp_no_vars(self):
        self.assertEqual(tyvars(bool_ty), [])

    def test_tyvars_tyapp_with_vars(self):
        ty = mk_fun_ty(aty, bty)
        result = tyvars(ty)
        self.assertIn(aty, result)
        self.assertIn(bty, result)

    def test_type_subst_tyvar(self):
        result = type_subst([(bool_ty, aty)], aty)
        self.assertEqual(result, bool_ty)

    def test_type_subst_no_match(self):
        b = mk_vartype("B")
        result = type_subst([(bool_ty, aty)], b)
        self.assertEqual(result, b)

    def test_type_subst_empty(self):
        result = type_subst([], aty)
        self.assertIs(result, aty)

    def test_type_subst_inside_tyapp(self):
        ty = mk_fun_ty(aty, bool_ty)
        result = type_subst([(bool_ty, aty)], ty)
        self.assertEqual(result, mk_fun_ty(bool_ty, bool_ty))

    def test_mk_fun_ty(self):
        ty = mk_fun_ty(bool_ty, aty)
        self.assertEqual(dest_type(ty), ("fun", [bool_ty, aty]))

    def test_type_equality(self):
        self.assertEqual(mk_vartype("X"), mk_vartype("X"))
        self.assertNotEqual(mk_vartype("X"), mk_vartype("Y"))
        self.assertEqual(mk_fun_ty(bool_ty, bool_ty), mk_fun_ty(bool_ty, bool_ty))


class TestTypeRegistry(KernelStateTestCase):

    def test_types_contains_builtins(self):
        ts = dict(types())
        self.assertIn("bool", ts)
        self.assertIn("fun", ts)
        self.assertEqual(ts["bool"], 0)
        self.assertEqual(ts["fun"], 2)

    def test_get_type_arity(self):
        self.assertEqual(get_type_arity("bool"), 0)
        self.assertEqual(get_type_arity("fun"), 2)

    def test_get_type_arity_unknown_raises(self):
        with self.assertRaises(Exception):
            get_type_arity("nosuchtype")

    def test_new_type(self):
        new_type("mylist", 1)
        self.assertEqual(get_type_arity("mylist"), 1)

    def test_new_type_duplicate_raises(self):
        new_type("mylist2", 1)
        with self.assertRaises(Exception):
            new_type("mylist2", 1)

    def test_new_type_usable_in_mk_type(self):
        new_type("pair", 2)
        ty = mk_type("pair", [bool_ty, aty])
        self.assertEqual(ty.tyop, "pair")


# ---------------------------------------------------------------------------
# Terms
# ---------------------------------------------------------------------------

class TestTerms(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)
        self.f_ty = mk_fun_ty(bool_ty, bool_ty)
        self.f = mk_var("f", self.f_ty)

    def test_mk_var(self):
        v = mk_var("z", bool_ty)
        self.assertIsInstance(v, Var)
        self.assertEqual(v.name, "z")
        self.assertEqual(v.ty, bool_ty)

    def test_mk_const(self):
        c = mk_const("=", [(bool_ty, aty)])
        self.assertIsInstance(c, Const)
        self.assertEqual(c.name, "=")

    def test_mk_const_unknown_raises(self):
        with self.assertRaises(Exception):
            mk_const("nosuchconst", [])

    def test_mk_abs(self):
        ab = mk_abs(self.x, self.y)
        self.assertIsInstance(ab, Abs)

    def test_mk_abs_non_var_raises(self):
        with self.assertRaises(Exception):
            mk_abs(mk_comb(self.f, self.x), self.x)

    def test_mk_comb(self):
        tm = mk_comb(self.f, self.x)
        self.assertIsInstance(tm, Comb)

    def test_mk_comb_type_mismatch_raises(self):
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            mk_comb(self.f, x_a)  # f : bool->bool, x_a : A

    def test_dest_var(self):
        name, ty = dest_var(self.x)
        self.assertEqual(name, "x")
        self.assertEqual(ty, bool_ty)

    def test_dest_var_non_var_raises(self):
        with self.assertRaises(Exception):
            dest_var(mk_comb(self.f, self.x))

    def test_dest_const(self):
        c = mk_const("=", [(bool_ty, aty)])
        name, ty = dest_const(c)
        self.assertEqual(name, "=")

    def test_dest_const_non_const_raises(self):
        with self.assertRaises(Exception):
            dest_const(self.x)

    def test_dest_comb(self):
        tm = mk_comb(self.f, self.x)
        fun, arg = dest_comb(tm)
        self.assertEqual(fun, self.f)
        self.assertEqual(arg, self.x)

    def test_dest_comb_non_comb_raises(self):
        with self.assertRaises(Exception):
            dest_comb(self.x)

    def test_dest_abs(self):
        ab = mk_abs(self.x, self.y)
        bv, body = dest_abs(ab)
        self.assertEqual(bv, self.x)
        self.assertEqual(body, self.y)

    def test_dest_abs_non_abs_raises(self):
        with self.assertRaises(Exception):
            dest_abs(self.x)

    def test_discriminators(self):
        ab = mk_abs(self.x, self.y)
        co = mk_comb(self.f, self.x)
        c = mk_const("=", [(bool_ty, aty)])
        self.assertTrue(is_var(self.x))
        self.assertTrue(is_const(c))
        self.assertTrue(is_abs(ab))
        self.assertTrue(is_comb(co))
        self.assertFalse(is_var(co))
        self.assertFalse(is_const(self.x))
        self.assertFalse(is_abs(co))
        self.assertFalse(is_comb(ab))

    def test_type_of_var(self):
        self.assertEqual(type_of(self.x), bool_ty)

    def test_type_of_const(self):
        c = mk_const("=", [(bool_ty, aty)])
        self.assertEqual(type_of(c), mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty)))

    def test_type_of_comb(self):
        tm = mk_comb(self.f, self.x)
        self.assertEqual(type_of(tm), bool_ty)

    def test_type_of_abs(self):
        ab = mk_abs(self.x, self.y)
        self.assertEqual(type_of(ab), mk_fun_ty(bool_ty, bool_ty))

    def test_rator_rand(self):
        tm = mk_comb(self.f, self.x)
        self.assertEqual(rator(tm), self.f)
        self.assertEqual(rand(tm), self.x)

    def test_rator_non_comb_raises(self):
        with self.assertRaises(Exception):
            rator(self.x)

    def test_rand_non_comb_raises(self):
        with self.assertRaises(Exception):
            rand(self.x)

    def test_term_equality(self):
        self.assertEqual(mk_var("x", bool_ty), mk_var("x", bool_ty))
        self.assertNotEqual(mk_var("x", bool_ty), mk_var("y", bool_ty))
        self.assertNotEqual(mk_var("x", bool_ty), mk_var("x", aty))


class TestTermRegistry(KernelStateTestCase):

    def test_constants_has_equality(self):
        cs = dict(constants())
        self.assertIn("=", cs)

    def test_get_const_type(self):
        ty = get_const_type("=")
        self.assertEqual(ty, mk_fun_ty(aty, mk_fun_ty(aty, bool_ty)))

    def test_get_const_type_unknown_raises(self):
        with self.assertRaises(Exception):
            get_const_type("nosuchconst")

    def test_new_constant(self):
        new_constant("myc", bool_ty)
        self.assertEqual(get_const_type("myc"), bool_ty)

    def test_new_constant_duplicate_raises(self):
        new_constant("myc2", bool_ty)
        with self.assertRaises(Exception):
            new_constant("myc2", bool_ty)


# ---------------------------------------------------------------------------
# Free variables and related
# ---------------------------------------------------------------------------

class TestFreeVars(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)
        self.f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))

    def test_frees_var(self):
        self.assertEqual(frees(self.x), [self.x])

    def test_frees_const(self):
        c = mk_const("=", [(bool_ty, aty)])
        self.assertEqual(frees(c), [])

    def test_frees_abs_binds(self):
        ab = mk_abs(self.x, self.x)
        self.assertEqual(frees(ab), [])

    def test_frees_abs_free_body(self):
        ab = mk_abs(self.x, self.y)
        self.assertEqual(frees(ab), [self.y])

    def test_frees_comb(self):
        tm = mk_comb(self.f, self.x)
        result = frees(tm)
        self.assertIn(self.f, result)
        self.assertIn(self.x, result)

    def test_freesl(self):
        result = freesl([self.x, mk_abs(self.x, self.y)])
        self.assertIn(self.x, result)
        self.assertIn(self.y, result)

    def test_freesin_closed(self):
        self.assertTrue(freesin([], mk_abs(self.x, self.x)))

    def test_freesin_open(self):
        self.assertFalse(freesin([], self.x))
        self.assertTrue(freesin([self.x], self.x))

    def test_vfree_in_direct(self):
        self.assertTrue(vfree_in(self.x, self.x))
        self.assertFalse(vfree_in(self.x, self.y))

    def test_vfree_in_comb(self):
        tm = mk_comb(self.f, self.x)
        self.assertTrue(vfree_in(self.x, tm))
        self.assertFalse(vfree_in(self.y, tm))

    def test_vfree_in_abs_bound(self):
        ab = mk_abs(self.x, self.x)
        self.assertFalse(vfree_in(self.x, ab))

    def test_vfree_in_abs_free(self):
        ab = mk_abs(self.x, self.y)
        self.assertTrue(vfree_in(self.y, ab))

    def test_type_vars_in_term(self):
        x_a = mk_var("x", aty)
        result = type_vars_in_term(x_a)
        self.assertIn(aty, result)

    def test_type_vars_in_term_no_vars(self):
        self.assertEqual(type_vars_in_term(self.x), [])

    def test_variant_no_conflict(self):
        v = variant([], self.x)
        self.assertIs(v, self.x)

    def test_variant_conflict(self):
        v = variant([self.x], self.x)
        self.assertNotEqual(v, self.x)
        self.assertEqual(v.ty, bool_ty)
        self.assertFalse(vfree_in(v, self.x))


# ---------------------------------------------------------------------------
# Substitution and instantiation
# ---------------------------------------------------------------------------

class TestVsubst(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)
        self.z = mk_var("z", bool_ty)

    def test_empty_theta_is_identity(self):
        subst = vsubst([])
        self.assertIs(subst(self.x), self.x)

    def test_simple_substitution(self):
        subst = vsubst([(self.y, self.x)])   # replace x with y
        result = subst(self.x)
        self.assertEqual(result, self.y)

    def test_no_capture_in_abs(self):
        # (\y. x) [x := y]  ->  (\y'. y)  (y must be renamed)
        ab = mk_abs(self.y, self.x)
        subst = vsubst([(self.y, self.x)])
        result = subst(ab)
        self.assertIsInstance(result, Abs)
        bv, body = dest_abs(result)
        self.assertNotEqual(bv, self.y)        # y renamed to avoid capture
        self.assertEqual(body, self.y)         # x replaced by y in body

    def test_bound_var_not_substituted(self):
        ab = mk_abs(self.x, self.x)
        subst = vsubst([(self.y, self.x)])
        result = subst(ab)
        self.assertIsInstance(result, Abs)
        bv, body = dest_abs(result)
        self.assertEqual(bv, self.x)
        self.assertEqual(body, self.x)  # x is bound, not replaced

    def test_wrong_type_raises(self):
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            vsubst([(x_a, self.x)])  # type_of(x_a)=A ≠ bool=x.ty

    def test_non_var_in_pair_raises(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        with self.assertRaises(Exception):
            vsubst([(self.y, mk_comb(f, self.x))])  # second element not Var


class TestInst(unittest.TestCase):

    def setUp(self):
        self.x_a = mk_var("x", aty)
        self.x_b = mk_var("x", bool_ty)

    def test_empty_tyin_is_identity(self):
        fn = inst([])
        self.assertIs(fn(self.x_a), self.x_a)

    def test_instantiate_tyvar_in_var(self):
        fn = inst([(bool_ty, aty)])
        result = fn(self.x_a)
        self.assertEqual(result, self.x_b)

    def test_instantiate_in_const(self):
        c = mk_const("=", [])          # = : A -> A -> bool
        fn = inst([(bool_ty, aty)])
        result = fn(c)
        expected_ty = mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty))
        self.assertEqual(type_of(result), expected_ty)

    def test_instantiate_in_comb(self):
        f = mk_var("f", mk_fun_ty(aty, aty))
        x_a = self.x_a
        tm = mk_comb(f, x_a)
        fn = inst([(bool_ty, aty)])
        result = fn(tm)
        self.assertIsInstance(result, Comb)
        self.assertEqual(type_of(result), bool_ty)

    def test_instantiate_in_abs_no_clash(self):
        ab = mk_abs(self.x_a, self.x_a)     # \(x:A). x
        fn = inst([(bool_ty, aty)])
        result = fn(ab)
        self.assertIsInstance(result, Abs)
        bv, body = dest_abs(result)
        self.assertEqual(bv, self.x_b)
        self.assertEqual(body, self.x_b)


# ---------------------------------------------------------------------------
# Alpha order
# ---------------------------------------------------------------------------

class TestAlphaOrder(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_same_term_zero(self):
        self.assertEqual(alphaorder(self.x, self.x), 0)

    def test_different_vars_nonzero(self):
        self.assertNotEqual(alphaorder(self.x, self.y), 0)

    def test_antisymmetry(self):
        c = alphaorder(self.x, self.y)
        self.assertEqual(alphaorder(self.y, self.x), -c)

    def test_aconv_same(self):
        self.assertTrue(aconv(self.x, self.x))

    def test_aconv_alpha_equivalent_abs(self):
        ab1 = mk_abs(self.x, self.x)
        ab2 = mk_abs(self.y, self.y)
        self.assertTrue(aconv(ab1, ab2))

    def test_not_aconv_different_body(self):
        ab1 = mk_abs(self.x, self.x)
        ab2 = mk_abs(self.x, self.y)
        self.assertFalse(aconv(ab1, ab2))


# ---------------------------------------------------------------------------
# dest_eq / is_eq / mk_eq
# ---------------------------------------------------------------------------

class TestEqSyntax(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_mk_eq(self):
        eq = mk_eq(self.x, self.y)
        self.assertTrue(is_eq(eq))

    def test_dest_eq(self):
        eq = mk_eq(self.x, self.y)
        lhs, rhs = dest_eq(eq)
        self.assertEqual(lhs, self.x)
        self.assertEqual(rhs, self.y)

    def test_dest_eq_non_eq_raises(self):
        with self.assertRaises(Exception):
            dest_eq(self.x)

    def test_is_eq_false_for_non_eq(self):
        self.assertFalse(is_eq(self.x))


# ---------------------------------------------------------------------------
# Theorem destructors
# ---------------------------------------------------------------------------

class TestThmDestructors(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_dest_thm_refl(self):
        th = REFL(self.x)
        asl, c = dest_thm(th)
        self.assertEqual(asl, [])
        self.assertEqual(c, mk_eq(self.x, self.x))

    def test_hyp(self):
        th = ASSUME(self.x)
        self.assertEqual(hyp(th), [self.x])

    def test_concl(self):
        th = ASSUME(self.x)
        self.assertEqual(concl(th), self.x)

    def test_equals_thm(self):
        th1 = REFL(self.x)
        th2 = REFL(self.x)
        self.assertTrue(equals_thm(th1, th2))

    def test_not_equals_thm(self):
        th1 = REFL(self.x)
        th2 = REFL(self.y)
        self.assertFalse(equals_thm(th1, th2))


# ---------------------------------------------------------------------------
# REFL
# ---------------------------------------------------------------------------

class TestREFL(unittest.TestCase):

    def test_refl_var(self):
        x = mk_var("x", bool_ty)
        th = REFL(x)
        self.assertEqual(hyp(th), [])
        self.assertEqual(concl(th), mk_eq(x, x))

    def test_refl_function_type(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        th = REFL(f)
        self.assertEqual(hyp(th), [])
        self.assertEqual(concl(th), mk_eq(f, f))

    def test_refl_comb(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        x = mk_var("x", bool_ty)
        tm = mk_comb(f, x)
        th = REFL(tm)
        self.assertEqual(concl(th), mk_eq(tm, tm))

    def test_refl_abs(self):
        x = mk_var("x", bool_ty)
        y = mk_var("y", bool_ty)
        ab = mk_abs(x, y)
        th = REFL(ab)
        self.assertEqual(concl(th), mk_eq(ab, ab))

    def test_refl_generic_type(self):
        x_a = mk_var("x", aty)
        th = REFL(x_a)
        self.assertEqual(concl(th), mk_eq(x_a, x_a))


# ---------------------------------------------------------------------------
# TRANS
# ---------------------------------------------------------------------------

class TestTRANS(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)
        self.z = mk_var("z", bool_ty)

    def test_trans_refl_refl(self):
        th = TRANS(REFL(self.x), REFL(self.x))
        self.assertEqual(hyp(th), [])
        self.assertEqual(concl(th), mk_eq(self.x, self.x))

    def test_trans_chaining(self):
        # |- x=y and |- y=z  =>  |- x=z
        th1 = ASSUME(mk_eq(self.x, self.y))   # {x=y} |- x=y
        th2 = ASSUME(mk_eq(self.y, self.z))   # {y=z} |- y=z
        th = TRANS(th1, th2)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, self.x)
        self.assertEqual(rhs, self.z)

    def test_trans_merges_hypotheses(self):
        th1 = ASSUME(mk_eq(self.x, self.y))
        th2 = ASSUME(mk_eq(self.y, self.z))
        th = TRANS(th1, th2)
        h = hyp(th)
        self.assertIn(mk_eq(self.x, self.y), h)
        self.assertIn(mk_eq(self.y, self.z), h)

    def test_trans_middle_mismatch_raises(self):
        # rhs of th1 is x, lhs of th2 is z — mismatch
        th1 = REFL(self.x)
        th2 = REFL(self.z)
        with self.assertRaises(Exception):
            TRANS(th1, th2)

    def test_trans_not_equations_raises(self):
        th1 = ASSUME(self.x)  # not an equation
        th2 = REFL(self.x)
        with self.assertRaises(Exception):
            TRANS(th1, th2)

    def test_trans_alpha_equal_middle(self):
        # Trans should accept alpha-equivalent middle terms
        f_ty = mk_fun_ty(bool_ty, bool_ty)
        f = mk_var("f", f_ty)
        g = mk_var("g", f_ty)
        bv1 = mk_var("a", bool_ty)
        bv2 = mk_var("b", bool_ty)
        abs1 = mk_abs(bv1, bv1)   # \a.a : bool->bool
        abs2 = mk_abs(bv2, bv2)   # \b.b : bool->bool (alpha-equal)
        th1 = ASSUME(mk_eq(f, abs1))    # {f=\a.a} |- f=\a.a
        th2 = ASSUME(mk_eq(abs2, g))    # {\b.b=g} |- \b.b=g
        th = TRANS(th1, th2)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, f)
        self.assertEqual(rhs, g)


# ---------------------------------------------------------------------------
# MK_COMB
# ---------------------------------------------------------------------------

class TestMK_COMB(unittest.TestCase):

    def setUp(self):
        self.bb = mk_fun_ty(bool_ty, bool_ty)
        self.f = mk_var("f", self.bb)
        self.g = mk_var("g", self.bb)
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_mk_comb_refl(self):
        th = MK_COMB(REFL(self.f), REFL(self.x))
        fx = mk_comb(self.f, self.x)
        self.assertEqual(hyp(th), [])
        self.assertEqual(concl(th), mk_eq(fx, fx))

    def test_mk_comb_from_equations(self):
        # |- f=g  and  |- x=y  =>  |- f x = g y
        th1 = ASSUME(mk_eq(self.f, self.g))
        th2 = ASSUME(mk_eq(self.x, self.y))
        th = MK_COMB(th1, th2)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, mk_comb(self.f, self.x))
        self.assertEqual(rhs, mk_comb(self.g, self.y))

    def test_mk_comb_merges_hypotheses(self):
        th1 = ASSUME(mk_eq(self.f, self.g))
        th2 = ASSUME(mk_eq(self.x, self.y))
        th = MK_COMB(th1, th2)
        h = hyp(th)
        self.assertIn(mk_eq(self.f, self.g), h)
        self.assertIn(mk_eq(self.x, self.y), h)

    def test_mk_comb_type_mismatch_raises(self):
        # f : bool->bool, x_a : A  — types don't match
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            MK_COMB(REFL(self.f), REFL(x_a))

    def test_mk_comb_not_equation_raises(self):
        with self.assertRaises(Exception):
            MK_COMB(ASSUME(self.x), REFL(self.x))

    def test_mk_comb_fun_not_function_type_raises(self):
        # Both are bool-typed variables — f is not a function
        with self.assertRaises(Exception):
            MK_COMB(REFL(self.x), REFL(self.y))


# ---------------------------------------------------------------------------
# ABS
# ---------------------------------------------------------------------------

class TestABS(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_abs_refl(self):
        # |- y=y  =>  |- (\x.y) = (\x.y)
        th = ABS(self.x, REFL(self.y))
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, mk_abs(self.x, self.y))
        self.assertEqual(rhs, mk_abs(self.x, self.y))
        self.assertEqual(hyp(th), [])

    def test_abs_with_body_equation(self):
        # |- x=y  (after ASSUME)  =>  |- (\z.x) = (\z.y)
        z = mk_var("z", bool_ty)
        th_eq = ASSUME(mk_eq(self.x, self.y))   # {x=y} |- x=y
        th = ABS(z, th_eq)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, mk_abs(z, self.x))
        self.assertEqual(rhs, mk_abs(z, self.y))

    def test_abs_preserves_hypotheses(self):
        z = mk_var("z", bool_ty)
        th_eq = ASSUME(mk_eq(self.x, self.y))
        th = ABS(z, th_eq)
        self.assertIn(mk_eq(self.x, self.y), hyp(th))

    def test_abs_var_free_in_hyp_raises(self):
        # x is free in the hypothesis {x=y}, so ABS(x, ...) must fail
        th_eq = ASSUME(mk_eq(self.x, self.y))   # hyp contains x
        with self.assertRaises(Exception):
            ABS(self.x, th_eq)

    def test_abs_non_var_raises(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        with self.assertRaises(Exception):
            ABS(mk_comb(f, self.x), REFL(self.y))

    def test_abs_conclusion_not_eq_raises(self):
        with self.assertRaises(Exception):
            ABS(self.x, ASSUME(self.x))


# ---------------------------------------------------------------------------
# BETA
# ---------------------------------------------------------------------------

class TestBETA(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)

    def test_beta_identity(self):
        # (\x.x) x  =>  |- (\x.x) x = x
        tm = mk_comb(mk_abs(self.x, self.x), self.x)
        th = BETA(tm)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, tm)
        self.assertEqual(rhs, self.x)
        self.assertEqual(hyp(th), [])

    def test_beta_constant_body(self):
        # (\x.y) x  =>  |- (\x.y) x = y
        tm = mk_comb(mk_abs(self.x, self.y), self.x)
        th = BETA(tm)
        _, rhs = dest_eq(concl(th))
        self.assertEqual(rhs, self.y)

    def test_beta_non_trivial_raises(self):
        # (\x.x) y  where y ≠ x — not a trivial redex
        tm = mk_comb(mk_abs(self.x, self.x), self.y)
        with self.assertRaises(Exception):
            BETA(tm)

    def test_beta_not_comb_raises(self):
        with self.assertRaises(Exception):
            BETA(self.x)

    def test_beta_not_abs_raises(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        # (f x) is a comb but fun part is not Abs
        tm = mk_comb(f, self.x)
        with self.assertRaises(Exception):
            BETA(tm)


# ---------------------------------------------------------------------------
# ASSUME
# ---------------------------------------------------------------------------

class TestASSUME(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)

    def test_assume_bool(self):
        th = ASSUME(self.x)
        self.assertEqual(hyp(th), [self.x])
        self.assertEqual(concl(th), self.x)

    def test_assume_equation(self):
        eq = mk_eq(self.x, self.x)
        th = ASSUME(eq)
        self.assertEqual(concl(th), eq)
        self.assertIn(eq, hyp(th))

    def test_assume_non_bool_raises(self):
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            ASSUME(x_a)

    def test_assume_function_type_raises(self):
        f = mk_var("f", mk_fun_ty(bool_ty, bool_ty))
        with self.assertRaises(Exception):
            ASSUME(f)


# ---------------------------------------------------------------------------
# EQ_MP
# ---------------------------------------------------------------------------

class TestEQ_MP(unittest.TestCase):

    def setUp(self):
        self.p = mk_var("p", bool_ty)
        self.q = mk_var("q", bool_ty)

    def test_eq_mp_basic(self):
        # {p=q} |- p=q  and  {p} |- p  =>  {p=q, p} |- q
        th_eq = ASSUME(mk_eq(self.p, self.q))
        th_p = ASSUME(self.p)
        th = EQ_MP(th_eq, th_p)
        self.assertEqual(concl(th), self.q)

    def test_eq_mp_merges_hypotheses(self):
        th_eq = ASSUME(mk_eq(self.p, self.q))
        th_p = ASSUME(self.p)
        th = EQ_MP(th_eq, th_p)
        h = hyp(th)
        self.assertIn(mk_eq(self.p, self.q), h)
        self.assertIn(self.p, h)

    def test_eq_mp_with_refl(self):
        # |- x=x and |- x  =>  |- x
        th_refl = REFL(self.p)
        th_p = ASSUME(self.p)
        th = EQ_MP(th_refl, th_p)
        self.assertEqual(concl(th), self.p)
        self.assertEqual(hyp(th), hyp(th_p))

    def test_eq_mp_lhs_mismatch_raises(self):
        th_eq = ASSUME(mk_eq(self.p, self.q))
        th_q = ASSUME(self.q)   # lhs of eq is p, but conclusion is q
        with self.assertRaises(Exception):
            EQ_MP(th_eq, th_q)

    def test_eq_mp_first_not_eq_raises(self):
        with self.assertRaises(Exception):
            EQ_MP(ASSUME(self.p), ASSUME(self.p))

    def test_eq_mp_alpha_match(self):
        # EQ_MP should accept alpha-equal lhs
        bv1 = mk_var("a", bool_ty)
        bv2 = mk_var("b", bool_ty)
        ab1 = mk_abs(bv1, bv1)   # \a.a  : bool->bool
        ab2 = mk_abs(bv2, bv2)   # \b.b  (alpha-equal)
        # Make bool-typed terms via application
        z = mk_var("z", bool_ty)
        lhs = mk_comb(ab1, z)
        rhs = mk_comb(ab2, z)
        th_eq = ASSUME(mk_eq(lhs, rhs))   # {lhs=rhs} |- lhs=rhs
        th_lhs = ASSUME(lhs)
        th = EQ_MP(th_eq, th_lhs)
        self.assertEqual(concl(th), rhs)


# ---------------------------------------------------------------------------
# DEDUCT_ANTISYM_RULE
# ---------------------------------------------------------------------------

class TestDEDUCT_ANTISYM_RULE(unittest.TestCase):

    def setUp(self):
        self.p = mk_var("p", bool_ty)
        self.q = mk_var("q", bool_ty)

    def test_basic_result_is_equation(self):
        th1 = ASSUME(self.p)
        th2 = ASSUME(self.q)
        th = DEDUCT_ANTISYM_RULE(th1, th2)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, self.p)
        self.assertEqual(rhs, self.q)

    def test_cancels_conclusions_from_hypotheses(self):
        # If concl(th2)=q is in hyp(th1), it gets removed, and vice versa
        # ASSUME(p): {p} |- p  and  ASSUME(q): {q} |- q
        # DEDUCT: remove q from {p} -> {p}; remove p from {q} -> {q}
        # hyps = {p} ∪ {q}
        th1 = ASSUME(self.p)
        th2 = ASSUME(self.q)
        th = DEDUCT_ANTISYM_RULE(th1, th2)
        h = hyp(th)
        # Both p and q remain since neither appears in the other's hyps
        self.assertIn(self.p, h)
        self.assertIn(self.q, h)

    def test_full_cancellation(self):
        # Build  q |- p  and  p |- q  so conclusions cancel completely
        # q |- p:  EQ_MP(ASSUME(q=p), ASSUME(q))
        th_qp = ASSUME(mk_eq(self.q, self.p))   # {q=p} |- q=p
        th_q  = ASSUME(self.q)
        th1   = EQ_MP(th_qp, th_q)             # {q=p, q} |- p

        th_pq = ASSUME(mk_eq(self.p, self.q))
        th_p  = ASSUME(self.p)
        th2   = EQ_MP(th_pq, th_p)             # {p=q, p} |- q

        th = DEDUCT_ANTISYM_RULE(th1, th2)
        # concl(th1)=p removed from hyp(th2); concl(th2)=q removed from hyp(th1)
        h = hyp(th)
        self.assertNotIn(self.p, h)
        self.assertNotIn(self.q, h)

    def test_conclusion_is_biconditional(self):
        th1 = ASSUME(self.p)
        th2 = ASSUME(self.p)   # same term both sides
        th = DEDUCT_ANTISYM_RULE(th1, th2)
        lhs, rhs = dest_eq(concl(th))
        self.assertEqual(lhs, rhs)
        self.assertEqual(lhs, self.p)
        # p appears as concl of th2 and is removed from hyp(th1)=[p]
        self.assertEqual(hyp(th), [])


# ---------------------------------------------------------------------------
# INST_TYPE
# ---------------------------------------------------------------------------

class TestINST_TYPE(unittest.TestCase):

    def setUp(self):
        self.x_a = mk_var("x", aty)
        self.x_b = mk_var("x", bool_ty)

    def test_empty_theta_identity(self):
        th = REFL(self.x_a)
        th2 = INST_TYPE([], th)
        self.assertTrue(equals_thm(th, th2))

    def test_instantiate_conclusion(self):
        th = REFL(self.x_a)   # |- x_A = x_A
        th2 = INST_TYPE([(bool_ty, aty)], th)
        self.assertEqual(concl(th2), mk_eq(self.x_b, self.x_b))

    def test_instantiate_hypotheses(self):
        th = ASSUME(mk_eq(self.x_a, self.x_a))   # {x_A=x_A} |- x_A=x_A
        th2 = INST_TYPE([(bool_ty, aty)], th)
        expected_hyp = mk_eq(self.x_b, self.x_b)
        self.assertIn(expected_hyp, hyp(th2))
        self.assertEqual(concl(th2), expected_hyp)

    def test_instantiate_multiple_vars(self):
        b = mk_vartype("B")
        x_a = self.x_a
        x_b_var = mk_var("y", b)
        ab = mk_abs(x_a, x_b_var)   # \(x:A). (y:B)  : A->B
        th = REFL(ab)
        th2 = INST_TYPE([(bool_ty, aty), (bool_ty, b)], th)
        lhs, _ = dest_eq(concl(th2))
        bv, body = dest_abs(lhs)
        self.assertEqual(bv.ty, bool_ty)
        self.assertEqual(body.ty, bool_ty)

    def test_no_free_tyvars_unchanged(self):
        th = REFL(self.x_b)   # |- x_bool = x_bool (no type vars)
        th2 = INST_TYPE([(aty, bty)], th)
        self.assertTrue(equals_thm(th, th2))


# ---------------------------------------------------------------------------
# INST
# ---------------------------------------------------------------------------

class TestINST(unittest.TestCase):

    def setUp(self):
        self.x = mk_var("x", bool_ty)
        self.y = mk_var("y", bool_ty)
        self.z = mk_var("z", bool_ty)

    def test_empty_theta_identity(self):
        th = REFL(self.x)
        th2 = INST([], th)
        self.assertTrue(equals_thm(th, th2))

    def test_instantiate_conclusion(self):
        th = REFL(self.x)   # |- x=x
        th2 = INST([(self.y, self.x)], th)   # replace x with y
        self.assertEqual(concl(th2), mk_eq(self.y, self.y))
        self.assertEqual(hyp(th2), [])

    def test_instantiate_hypotheses(self):
        th = ASSUME(self.x)   # {x} |- x
        th2 = INST([(self.y, self.x)], th)
        self.assertEqual(concl(th2), self.y)
        self.assertIn(self.y, hyp(th2))

    def test_instantiate_multiple_vars(self):
        eq = mk_eq(self.x, self.y)
        th = ASSUME(eq)   # {x=y} |- x=y
        th2 = INST([(self.z, self.x), (self.x, self.y)], th)
        lhs, rhs = dest_eq(concl(th2))
        self.assertEqual(lhs, self.z)
        self.assertEqual(rhs, self.x)

    def test_inst_does_not_capture(self):
        # |- (\y. x) = (\y. x) ; replace x with y should rename binder
        ab = mk_abs(self.y, self.x)   # \y. x
        th = REFL(ab)
        th2 = INST([(self.y, self.x)], th)
        # lhs should be alpha-renaming of \y. y, i.e., \z. z for some z
        lhs, _ = dest_eq(concl(th2))
        bv, body = dest_abs(lhs)
        self.assertNotEqual(bv, self.y)   # binder renamed away from y
        self.assertEqual(body, self.y)    # body is now y

    def test_wrong_type_raises(self):
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            INST([(x_a, self.x)], REFL(self.x))  # type mismatch


# ---------------------------------------------------------------------------
# Axioms
# ---------------------------------------------------------------------------

class TestAxioms(KernelStateTestCase):

    def setUp(self):
        super().setUp()
        self.p = mk_var("p", bool_ty)

    def test_new_axiom_returns_thm(self):
        th = new_axiom(self.p)
        self.assertEqual(concl(th), self.p)
        self.assertEqual(hyp(th), [])

    def test_new_axiom_appears_in_axioms(self):
        th = new_axiom(self.p)
        self.assertIn(th, axioms())

    def test_new_axiom_non_bool_raises(self):
        x_a = mk_var("x", aty)
        with self.assertRaises(Exception):
            new_axiom(x_a)

    def test_axioms_returns_copy(self):
        before = len(axioms())
        new_axiom(self.p)
        self.assertEqual(len(axioms()), before + 1)


# ---------------------------------------------------------------------------
# Definitions
# ---------------------------------------------------------------------------

class TestDefinitions(KernelStateTestCase):

    def test_new_basic_definition(self):
        ty = mk_fun_ty(bool_ty, bool_ty)
        x = mk_var("x", bool_ty)
        rhs = mk_abs(x, x)   # \x. x
        defn_tm = mk_eq(mk_var("myid", ty), rhs)
        th = new_basic_definition(defn_tm)
        self.assertEqual(hyp(th), [])
        lhs, r = dest_eq(concl(th))
        self.assertIsInstance(lhs, Const)
        self.assertEqual(lhs.name, "myid")
        self.assertEqual(r, rhs)

    def test_new_basic_definition_appears_in_definitions(self):
        x = mk_var("x", bool_ty)
        defn_tm = mk_eq(mk_var("myidb", mk_fun_ty(bool_ty, bool_ty)), mk_abs(x, x))
        th = new_basic_definition(defn_tm)
        self.assertIn(th, definitions())

    def test_new_basic_definition_registers_constant(self):
        x = mk_var("x", bool_ty)
        defn_tm = mk_eq(mk_var("myidc", mk_fun_ty(bool_ty, bool_ty)), mk_abs(x, x))
        new_basic_definition(defn_tm)
        self.assertEqual(get_const_type("myidc"), mk_fun_ty(bool_ty, bool_ty))

    def test_new_basic_definition_open_term_raises(self):
        y = mk_var("y", bool_ty)
        # rhs contains free variable y
        defn_tm = mk_eq(mk_var("myfn", bool_ty), y)
        with self.assertRaises(Exception):
            new_basic_definition(defn_tm)

    def test_new_basic_definition_bad_form_raises(self):
        x = mk_var("x", bool_ty)
        with self.assertRaises(Exception):
            new_basic_definition(x)   # not an equation


# ---------------------------------------------------------------------------
# Type definitions
# ---------------------------------------------------------------------------

class TestNewBasicTypeDefinition(KernelStateTestCase):

    def _build_existence_thm(self):
        # Build  |- (\b:bool. b=b) w  using new_axiom
        b = mk_var("b", bool_ty)
        w = mk_var("w", bool_ty)
        P = mk_abs(b, mk_eq(b, b))
        return new_axiom(mk_comb(P, w)), P, w

    def test_returns_two_theorems(self):
        ex, P, w = self._build_existence_thm()
        result = new_basic_type_definition("myty1", ("myabs1", "myrep1"), ex)
        self.assertIsInstance(result, tuple)
        self.assertEqual(len(result), 2)

    def test_th1_abs_rep_identity(self):
        # th1: |- abs(rep a) = a
        ex, P, w = self._build_existence_thm()
        th1, th2 = new_basic_type_definition("myty2", ("myabs2", "myrep2"), ex)
        self.assertEqual(hyp(th1), [])
        lhs, rhs = dest_eq(concl(th1))
        # lhs = abs(rep a), rhs = a
        self.assertIsInstance(rhs, Var)
        self.assertEqual(rhs.name, "a")

    def test_th2_rep_abs_characterisation(self):
        # th2: |- P r = (rep(abs r) = r)
        ex, P, w = self._build_existence_thm()
        th1, th2 = new_basic_type_definition("myty3", ("myabs3", "myrep3"), ex)
        self.assertEqual(hyp(th2), [])
        lhs, _rhs = dest_eq(concl(th2))
        # lhs = P r
        self.assertIsInstance(lhs, Comb)

    def test_registers_new_type(self):
        ex, P, w = self._build_existence_thm()
        new_basic_type_definition("myty4", ("myabs4", "myrep4"), ex)
        self.assertIn("myty4", dict(types()))

    def test_registers_new_constants(self):
        ex, P, w = self._build_existence_thm()
        new_basic_type_definition("myty5", ("myabs5", "myrep5"), ex)
        self.assertIsNotNone(get_const_type("myabs5"))
        self.assertIsNotNone(get_const_type("myrep5"))

    def test_existing_constant_raises(self):
        ex, P, w = self._build_existence_thm()
        new_basic_type_definition("myty6", ("myabs6", "myrep6"), ex)
        ex2, _, _ = self._build_existence_thm()
        with self.assertRaises(Exception):
            new_basic_type_definition("myty7", ("myabs6", "myrep7"), ex2)

    def test_assumptions_in_thm_raises(self):
        b = mk_var("b", bool_ty)
        w = mk_var("w", bool_ty)
        P = mk_abs(b, mk_eq(b, b))
        # ASSUME gives a theorem WITH hypotheses
        ex = ASSUME(mk_comb(P, w))
        with self.assertRaises(Exception):
            new_basic_type_definition("myty8", ("myabs8", "myrep8"), ex)

    def test_non_combination_conclusion_raises(self):
        # The existence theorem must be a combination P t
        ex = new_axiom(mk_var("p", bool_ty))   # concl is a Var, not Comb
        with self.assertRaises(Exception):
            new_basic_type_definition("myty9", ("myabs9", "myrep9"), ex)


if __name__ == "__main__":
    unittest.main()
