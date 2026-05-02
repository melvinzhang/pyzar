import unittest

from fusion import (
    aty, bool_ty,
    Abs, Var, mk_const, mk_comb, type_of,
    concl, hyp, axioms, definitions, get_const_type,
)
from basics import mk_fun_ty
import axioms as ax
from axioms import (
    T, F, mk_and, mk_or, mk_imp, mk_not, mk_forall, mk_exists, mk_select,
    is_conj, dest_conj, is_disj, dest_disj, is_imp, dest_imp,
    is_neg, dest_neg, is_forall, dest_forall, is_exists, dest_exists,
    ETA_AX, SELECT_AX, INFINITY_AX,
    T_DEF, AND_DEF, IMP_DEF, FORALL_DEF, EXISTS_DEF, OR_DEF, F_DEF, NOT_DEF,
    ONE_ONE_DEF, ONTO_DEF,
)
from parser import DEFAULT_SIG, parse, pp


class TestBooleanConstants(unittest.TestCase):
    """The 8 boolean connectives are registered with the expected types."""

    def test_nullary_connective_types(self):
        self.assertEqual(get_const_type("T"), bool_ty)
        self.assertEqual(get_const_type("F"), bool_ty)

    def test_binary_connective_types(self):
        bbb = mk_fun_ty(bool_ty, mk_fun_ty(bool_ty, bool_ty))
        for name in ("/\\", "\\/", "==>"):
            self.assertEqual(get_const_type(name), bbb)

    def test_unary_connective_types(self):
        self.assertEqual(get_const_type("~"), mk_fun_ty(bool_ty, bool_ty))

    def test_binder_connective_types(self):
        # Quantifiers and Hilbert choice all live at (A->bool) -> ...
        abty = mk_fun_ty(aty, bool_ty)
        self.assertEqual(get_const_type("!"), mk_fun_ty(abty, bool_ty))
        self.assertEqual(get_const_type("?"), mk_fun_ty(abty, bool_ty))
        self.assertEqual(get_const_type("@"), mk_fun_ty(abty, aty))


class TestAxiomsRegistered(unittest.TestCase):
    """The 3 HOL Light axioms are present, hypothesis-free, and bool-typed."""

    def test_axioms_in_kernel_registry(self):
        registered = axioms()
        for th in (ETA_AX, SELECT_AX, INFINITY_AX):
            self.assertIn(th, registered)

    def test_axioms_have_no_hypotheses(self):
        for th in (ETA_AX, SELECT_AX, INFINITY_AX):
            self.assertEqual(hyp(th), [])

    def test_axiom_conclusions_are_boolean(self):
        for th in (ETA_AX, SELECT_AX, INFINITY_AX):
            self.assertEqual(type_of(concl(th)), bool_ty)


class TestDefinitionsRegistered(unittest.TestCase):
    """Each defining equation lives in the kernel definitions list."""

    def test_all_boolean_definitions_present(self):
        registered = definitions()
        for d in (T_DEF, AND_DEF, IMP_DEF, FORALL_DEF, EXISTS_DEF,
                  OR_DEF, F_DEF, NOT_DEF, ONE_ONE_DEF, ONTO_DEF):
            self.assertIn(d, registered)


class TestShapeHelpers(unittest.TestCase):
    """is_*/dest_* round-trip with the matching mk_* constructor."""

    def setUp(self):
        self.p = Var("p", bool_ty)
        self.q = Var("q", bool_ty)
        self.x = Var("x", aty)

    def test_conj_roundtrip(self):
        tm = mk_and(self.p, self.q)
        self.assertTrue(is_conj(tm))
        self.assertEqual(dest_conj(tm), (self.p, self.q))

    def test_disj_roundtrip(self):
        tm = mk_or(self.p, self.q)
        self.assertTrue(is_disj(tm))
        self.assertEqual(dest_disj(tm), (self.p, self.q))

    def test_imp_roundtrip(self):
        tm = mk_imp(self.p, self.q)
        self.assertTrue(is_imp(tm))
        self.assertEqual(dest_imp(tm), (self.p, self.q))

    def test_neg_roundtrip(self):
        tm = mk_not(self.p)
        self.assertTrue(is_neg(tm))
        self.assertEqual(dest_neg(tm), self.p)

    def test_forall_roundtrip(self):
        body = mk_comb(Var("P", mk_fun_ty(aty, bool_ty)), self.x)
        tm = mk_forall(self.x, body)
        self.assertTrue(is_forall(tm))
        abs_ = dest_forall(tm)
        self.assertIsInstance(abs_, Abs)
        self.assertEqual(abs_.bvar, self.x)
        self.assertEqual(abs_.body, body)

    def test_exists_roundtrip(self):
        body = mk_comb(Var("P", mk_fun_ty(aty, bool_ty)), self.x)
        tm = mk_exists(self.x, body)
        self.assertTrue(is_exists(tm))
        abs_ = dest_exists(tm)
        self.assertIsInstance(abs_, Abs)
        self.assertEqual(abs_.bvar, self.x)
        self.assertEqual(abs_.body, body)

    def test_helpers_reject_other_shapes(self):
        # A conjunction must not look like a disjunction, etc.
        conj = mk_and(self.p, self.q)
        self.assertFalse(is_disj(conj))
        self.assertFalse(is_imp(conj))
        self.assertFalse(is_neg(conj))
        self.assertFalse(is_forall(conj))
        self.assertFalse(is_exists(conj))

    def test_select_constructs_correctly_typed_term(self):
        body = mk_comb(Var("P", mk_fun_ty(aty, bool_ty)), self.x)
        tm = mk_select(self.x, body)
        self.assertEqual(type_of(tm), aty)


class TestSurfaceSyntaxRegistered(unittest.TestCase):
    """DEFAULT_SIG knows about every operator axioms.py defines."""

    def test_parse_uses_registered_operators(self):
        # Mixed-fixity expression exercising binders, prefix, and three
        # different infix precedences on a single parse.
        tm = parse("!x:bool. ~x \\/ x ==> x /\\ x")
        self.assertEqual(type_of(tm), bool_ty)

    def test_pp_round_trip_propositional(self):
        # Propositional fragment round-trips cleanly because pp omits the
        # binder type annotations needed by the parser, so binder cases live
        # in test_parse_uses_registered_operators above.
        cases = [
            ("p /\\ q", {"p": bool_ty, "q": bool_ty}),
            ("p \\/ q", {"p": bool_ty, "q": bool_ty}),
            ("p ==> q", {"p": bool_ty, "q": bool_ty}),
            ("~p",      {"p": bool_ty}),
        ]
        for src, env in cases:
            tm = parse(src, **env)
            self.assertEqual(parse(pp(tm), **env), tm)


if __name__ == "__main__":
    unittest.main()
