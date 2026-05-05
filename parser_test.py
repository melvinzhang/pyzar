import unittest

# Importing nat triggers the full chain of registrations
# (axioms -> classical -> num -> nat) on DEFAULT_SIG.
import nat  # noqa: F401

from fusion import (
    Const,
    mk_comb,
)
from basics import (
    aconv, dest_eq, mk_abs, mk_app, mk_const, mk_eq, mk_fun_ty, mk_var,
)
from axioms import (
    bool_ty, mk_and, mk_or, mk_imp, mk_not, mk_forall, mk_exists, mk_select,
)
from num import x as VX, y as VY, z as VZ, mk_suc, num_ty, ONE
from parser import (
    DEFAULT_SIG, ParseError, Signature, define, parse, parse_type,
)
from fusion import Tyvar, Tyapp


def _binop(name):
    def _b(a, b):
        return mk_app(mk_const(name, []), a, b)
    return _b


_add, _mul, _gt = _binop("+"), _binop("*"), _binop(">")
P_ty = mk_fun_ty(num_ty, bool_ty)
P, Q, R = mk_var("P", P_ty), mk_var("Q", P_ty), mk_var("R", P_ty)


class TestSurface(unittest.TestCase):
    """Lark grammar + DEFAULT_SIG produce the expected kernel terms."""

    def test_arithmetic_and_application(self):
        self.assertTrue(aconv(parse("1 + 1"), _add(ONE, ONE)))
        self.assertTrue(aconv(parse("SUC 1"), mk_suc(ONE)))
        self.assertTrue(aconv(
            parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y"),
            mk_eq(_mul(mk_suc(VX), mk_suc(VY)),
                  _add(_mul(VX, mk_suc(VY)), mk_suc(VY)))))
        self.assertTrue(aconv(parse("x + y * z = z"),
                              mk_eq(_add(VX, _mul(VY, VZ)), VZ)))

    def test_left_associative_plus(self):
        self.assertTrue(aconv(parse("x + y + z"),
                              _add(_add(VX, VY), VZ)))

    def test_right_associative_and(self):
        env = {"P": P_ty, "Q": P_ty, "R": P_ty}
        self.assertTrue(aconv(
            parse("P x /\\ Q x /\\ R x", **env),
            mk_and(mk_comb(P, VX),
                   mk_and(mk_comb(Q, VX), mk_comb(R, VX)))))

    def test_quantifiers_and_lambda(self):
        self.assertTrue(aconv(
            parse("!x y z. (x + y) + z = x + (y + z)"),
            mk_forall(VX, mk_forall(VY, mk_forall(VZ,
                mk_eq(_add(_add(VX, VY), VZ),
                      _add(VX, _add(VY, VZ))))))))
        self.assertTrue(aconv(
            parse("!x y. x > y ==> x + 1 > y + 1"),
            mk_forall(VX, mk_forall(VY,
                mk_imp(_gt(VX, VY),
                       _gt(_add(VX, ONE), _add(VY, ONE)))))))
        self.assertTrue(aconv(parse("\\x. x + 1"),
                              mk_abs(VX, _add(VX, ONE))))
        self.assertTrue(aconv(parse("!x. P x", P=P_ty),
                              mk_forall(VX, mk_comb(P, VX))))
        u = mk_var("u", num_ty)
        self.assertTrue(aconv(
            parse("!x. ~(x = 1) ==> ?u. x = SUC u"),
            mk_forall(VX,
                mk_imp(mk_not(mk_eq(VX, ONE)),
                       mk_exists(u, mk_eq(VX, mk_suc(u)))))))

    def test_binder_type_annotation(self):
        # `bool` is registered as a type so `!p:bool. ...` parses.
        p = mk_var("p", bool_ty)
        self.assertTrue(aconv(parse("!p:bool. ~~p ==> p"),
                              mk_forall(p, mk_imp(mk_not(mk_not(p)), p))))

    def test_binder_full_type_expression(self):
        # Annotation accepts any arrow_type (no need for an env alias).
        Pv = mk_var("P", P_ty)
        self.assertTrue(aconv(
            parse("!P:num->bool. P x"),
            mk_forall(Pv, mk_comb(Pv, VX))))
        # Parenthesised compound types are accepted (postfix tyapp / nested).
        self.assertTrue(aconv(
            parse("!P:(num->bool). P x"),
            mk_forall(Pv, mk_comb(Pv, VX))))
        # Mixed annotated/bare var_decls juxtaposed.
        Qn = mk_var("Q", num_ty)
        self.assertTrue(aconv(
            parse("!P:num->bool Q. P Q"),
            mk_forall(Pv, mk_forall(Qn, mk_comb(Pv, Qn)))))

    def test_non_associative_eq_rejected(self):
        with self.assertRaises(ParseError):
            parse("x = y = z")


class TestAntiquotation(unittest.TestCase):
    """`${name}` splices a Python kernel term into the source string."""

    def test_basic_splice(self):
        self.assertTrue(aconv(parse("${a} + ${b}", a=VX, b=VY),
                              _add(VX, VY)))

    def test_repeated_antiquote_reuses_term(self):
        self.assertTrue(aconv(parse("${a} + ${a}", a=VX), _add(VX, VX)))

    def test_antiquote_inside_binder(self):
        u = mk_var("u", num_ty)
        self.assertTrue(aconv(
            parse("\\u. ${a} = SUC u", a=VX),
            mk_abs(u, mk_eq(VX, mk_suc(u)))))

    def test_satz_9_shape(self):
        u = mk_var("u", num_ty)
        v = mk_var("v", num_ty)
        self.assertTrue(aconv(
            parse("${a} = ${b} \\/ (?u. ${a} = ${b} + u) "
                  "\\/ (?v. ${b} = ${a} + v)", a=VX, b=VY),
            mk_or(mk_eq(VX, VY),
                  mk_or(mk_exists(u, mk_eq(VX, _add(VY, u))),
                        mk_exists(v, mk_eq(VY, _add(VX, v)))))))

    def test_missing_binding_errors(self):
        with self.assertRaises(ParseError):
            parse("${a} + 1")

    def test_extra_antiquote_binding_errors(self):
        with self.assertRaises(ParseError):
            parse("${a} + 1", a=VX, b=VY)

    def test_unused_bare_binding_errors(self):
        with self.assertRaises(ParseError):
            parse("x + y", f=P_ty)

    def test_referenced_bare_binding_ok(self):
        self.assertTrue(aconv(parse("f 1", f=P_ty),
                              mk_comb(mk_var("f", P_ty), ONE)))


class TestRuntimeExtension(unittest.TestCase):
    """Operators added to DEFAULT_SIG after construction parse correctly."""

    def test_add_infix_at_runtime(self):
        DEFAULT_SIG.add_infix("&&", 55, mk_and, assoc="left")
        try:
            got = parse("P x && Q x", P=P_ty, Q=P_ty)
            self.assertTrue(aconv(
                got, mk_and(mk_comb(P, VX), mk_comb(Q, VX))))
        finally:
            del DEFAULT_SIG.infix["&&"]


class TestFreshSignature(unittest.TestCase):
    """A minimal Signature only knows what it has been told."""

    def setUp(self):
        self.sig = Signature(default_var_ty=num_ty)
        self.sig.add_infix("=", 40, mk_eq, assoc="non")
        self.sig.add_infix("+", 50, _add, assoc="left")

    def test_known_operators_parse(self):
        a, b, c = (mk_var(n, num_ty) for n in "abc")
        self.assertTrue(aconv(parse("a + b = c", sig=self.sig),
                              mk_eq(_add(a, b), c)))

    def test_unknown_infix_rejected(self):
        with self.assertRaises(ParseError):
            parse("a * b", sig=self.sig)

    def test_unknown_prefix_rejected(self):
        with self.assertRaises(ParseError):
            parse("~a", sig=self.sig)

    def test_no_default_var_type_rejects_free_var(self):
        bare = Signature()
        bare.add_infix("=", 40, mk_eq, assoc="non")
        with self.assertRaises(ParseError):
            parse("a = b", sig=bare)


class TestDefine(unittest.TestCase):
    """define() registers a constant + optional infix and round-trips."""

    def test_infix_registration_round_trips(self):
        sig = Signature(default_var_ty=num_ty)
        sig.add_infix("=", 40, mk_eq, assoc="non")
        sig.add_infix("+", 50, _add, assoc="left")
        sig.add_binder("\\", mk_abs)
        sig.add_type("num", num_ty)
        op = "++"  # parser's OP token only accepts symbolic names
        op_def = define(op, "num -> num -> num", "\\a b. a + b", sig=sig,
                        prec=50, assoc="left")
        op_lhs, _ = dest_eq(op_def._concl)
        self.assertIsInstance(op_lhs, Const)
        self.assertEqual(op_lhs.name, op)
        self.assertIn(op, sig.const)
        self.assertIn(op, sig.infix)
        a, b = mk_var("a", num_ty), mk_var("b", num_ty)
        self.assertTrue(aconv(parse(f"a {op} b", sig=sig),
                              mk_app(sig.const[op], a, b)))


class TestSigLookup(unittest.TestCase):
    """`sig["op"]` returns the constant auto-registered by add_infix/prefix."""

    def test_lookup_returns_const(self):
        for name in ("\\/", "~", "+"):
            self.assertTrue(aconv(DEFAULT_SIG[name], mk_const(name, [])))


class TestSelectBinder(unittest.TestCase):
    """`@v. body` parses to an Eps/Hilbert SELECT term."""

    def test_single_var_select(self):
        # Multi-var doesn't typecheck since `@v. body` has type `v.ty`,
        # not bool, so it can't compose under another `@`.
        u = mk_var("u", num_ty)
        self.assertTrue(aconv(parse("@u. x = SUC u"),
                              mk_select(u, mk_eq(VX, mk_suc(u)))))


class TestParseType(unittest.TestCase):
    """parse_type produces kernel types from surface syntax."""

    def test_registered_zero_ary(self):
        self.assertEqual(parse_type("bool"), bool_ty)
        self.assertEqual(parse_type("num"), num_ty)

    def test_single_uppercase_is_tyvar(self):
        self.assertEqual(parse_type("A"), Tyvar("A"))
        self.assertEqual(parse_type("Z"), Tyvar("Z"))

    def test_arrow_right_associative(self):
        self.assertEqual(
            parse_type("A -> B -> C"),
            mk_fun_ty(Tyvar("A"), mk_fun_ty(Tyvar("B"), Tyvar("C"))))

    def test_parens_group(self):
        self.assertEqual(
            parse_type("(A -> B) -> C"),
            mk_fun_ty(mk_fun_ty(Tyvar("A"), Tyvar("B")), Tyvar("C")))

    def test_mixed_constructor_and_tyvar(self):
        self.assertEqual(
            parse_type("num -> num -> bool"),
            mk_fun_ty(num_ty, mk_fun_ty(num_ty, bool_ty)))
        self.assertEqual(
            parse_type("A -> bool"),
            mk_fun_ty(Tyvar("A"), bool_ty))

    def test_unknown_constructor_errors(self):
        with self.assertRaises(ParseError):
            parse_type("nosuchtype")

    def test_applying_tyvar_errors(self):
        # `B A` would mean "apply `A` to constructor `B`", but `B` is a
        # type variable, not a constructor.
        with self.assertRaises(ParseError):
            parse_type("B A")

    def test_registered_single_letter_beats_tyvar_rule(self):
        # If a theory registers a single-letter type (set theory uses
        # ``V``), parse_type must resolve to that constructor, not a
        # fresh Tyvar.
        sig = Signature()
        from fusion import new_type, mk_type
        try:
            new_type("X", 0)
        except Exception:
            pass
        X = mk_type("X", [])
        sig.add_type("X", X)
        self.assertEqual(parse_type("X", sig=sig), X)
        self.assertEqual(
            parse_type("X -> X", sig=sig), mk_fun_ty(X, X))

    def test_non_arrow_op_errors(self):
        with self.assertRaises(ParseError):
            parse_type("A + B")


if __name__ == "__main__":
    unittest.main()
