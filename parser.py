"""Lark-based parser for HOL terms in our num/bool signature.

Usage:
    from parser import parse
    target = parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y")

Supported syntax:
  - Numerals:    1
  - Successor:   SUC e
  - Arithmetic:  e + e, e * e
  - Comparison:  =, <, >, <=, >=
  - Logical:     ~, /\\, \\/, ==>
  - Quantifiers: !x. body, ?x. body, !x y z. body, !x:num. body
  - Lambda:      \\x. body
  - Application: f x

Free variables default to type `num`; pass `env={name: ty}` to override.
Identifiers `SUC` and `1` are reserved as kernel constants.
"""

from lark import Lark
from lark.visitors import Interpreter

from fusion import Var, Const, Comb, Abs, mk_var, mk_abs, mk_comb, mk_const, mk_eq
from axioms import (
    bool_ty, mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)
from logic import mk_or
from num import num_ty, ONE, SUC


def _binop(name):
    """Builder for an infix kernel constant, looked up lazily so the parser
    module is importable before `nat.py` has registered `+`, `*`, etc."""
    def _mk(a, b):
        return mk_comb(mk_comb(mk_const(name, []), a), b)
    return _mk


_mk_add = _binop("+")
_mk_mul = _binop("*")
_mk_gt  = _binop(">")
_mk_lt  = _binop("<")
_mk_ge  = _binop(">=")
_mk_le  = _binop("<=")


_TYPES = {"num": num_ty, "bool": bool_ty}


_GRAMMAR = r"""
?start: term

?term: "!" varlist "." term        -> forall_
     | "?" varlist "." term        -> exists_
     | "\\" varlist "." term       -> abs_
     | imp_term

?imp_term: or_term "==>" term      -> imp_
         | or_term

?or_term: and_term "\\/" or_term   -> or_
        | and_term

?and_term: not_term "/\\" and_term -> and_
         | not_term

?not_term: "~" not_term            -> not_
         | rel_term

?rel_term: add_term "="  add_term  -> eq_
         | add_term "<=" add_term  -> le_
         | add_term ">=" add_term  -> ge_
         | add_term "<"  add_term  -> lt_
         | add_term ">"  add_term  -> gt_
         | add_term

?add_term: add_term "+" mul_term   -> add_
         | mul_term

?mul_term: mul_term "*" app_term   -> mul_
         | app_term

?app_term: app_term atom           -> app_
         | atom

?atom: "(" term ")"
     | "1"                         -> one
     | NAME                        -> name

varlist: var_decl+
var_decl: NAME (":" TYPE)?

TYPE.2: "num" | "bool"
NAME: /[A-Za-z_][A-Za-z0-9_]*/

%ignore /[ \t\r\n]+/
"""


_PARSER = Lark(_GRAMMAR, parser="lalr", start="start")


class _Builder(Interpreter):
    def __init__(self, env):
        super().__init__()
        self.env = dict(env or {})
        self.scope = []          # stack of {name: Var}

    def _lookup(self, name):
        for s in reversed(self.scope):
            if name in s:
                return s[name]
        if name == "SUC":
            return SUC
        binding = self.env.get(name, num_ty)
        # `env` may map a name to a kernel term (Var / Const / Comb / Abs) for
        # direct substitution, or to a `hol_type` to create a variable.
        if isinstance(binding, (Var, Const, Comb, Abs)):
            return binding
        return mk_var(name, binding)

    def _decls(self, varlist_tree):
        out = []
        for vd in varlist_tree.children:
            n = str(vd.children[0])
            ty = num_ty
            if len(vd.children) > 1:
                ty = _TYPES[str(vd.children[1])]
            out.append((n, ty))
        return out

    def _binder(self, tree, wrap):
        decls = self._decls(tree.children[0])
        body_tree = tree.children[1]
        scope = {}
        vars_ = []
        for name, ty in decls:
            v = mk_var(name, ty)
            scope[name] = v
            vars_.append(v)
        self.scope.append(scope)
        body = self.visit(body_tree)
        self.scope.pop()
        for v in reversed(vars_):
            body = wrap(v, body)
        return body

    # Atoms.
    def name(self, tree):
        return self._lookup(str(tree.children[0]))

    def one(self, _tree):
        return ONE

    # Application + arithmetic + comparison + logic.
    def app_(self, tree):
        f, a = self.visit(tree.children[0]), self.visit(tree.children[1])
        # `SUC x` parses as application of SUC constant to x. mk_comb handles it.
        return mk_comb(f, a)

    def add_(self, tree):
        return _mk_add(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def mul_(self, tree):
        return _mk_mul(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def eq_(self, tree):
        return mk_eq(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def lt_(self, tree):
        return _mk_lt(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def gt_(self, tree):
        return _mk_gt(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def le_(self, tree):
        return _mk_le(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def ge_(self, tree):
        return _mk_ge(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def not_(self, tree):
        return mk_not(self.visit(tree.children[0]))

    def and_(self, tree):
        return mk_and(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def or_(self, tree):
        return mk_or(self.visit(tree.children[0]), self.visit(tree.children[1]))

    def imp_(self, tree):
        return mk_imp(self.visit(tree.children[0]), self.visit(tree.children[1]))

    # Binders.
    def forall_(self, tree):
        return self._binder(tree, mk_forall)

    def exists_(self, tree):
        return self._binder(tree, mk_exists)

    def abs_(self, tree):
        return self._binder(tree, mk_abs)


def parse(s, env=None):
    """Parse `s` into a kernel term.

    `env` maps free-variable names either to their `hol_type` (when the
    default `num` is wrong, e.g. `{"P": mk_fun_ty(num_ty, bool_ty)}`) or
    directly to a kernel term to substitute for that name."""
    tree = _PARSER.parse(s)
    return _Builder(env).visit(tree)


# ---------------------------------------------------------------------------
# Self-tests.
# ---------------------------------------------------------------------------

def _selftest():
    import nat  # noqa: F401  -- registers +, *, >, <, etc. as kernel constants
    from fusion import aconv, mk_fun_ty
    from num import x as VX, y as VY, z as VZ, mk_suc

    # Numerals + arithmetic.
    assert aconv(parse("1 + 1"), _mk_add(ONE, ONE))
    assert aconv(parse("SUC 1"), mk_suc(ONE))
    assert aconv(parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y"),
                 mk_eq(_mk_mul(mk_suc(VX), mk_suc(VY)),
                       _mk_add(_mk_mul(VX, mk_suc(VY)), mk_suc(VY))))

    # Precedence: + binds tighter than =, * tighter than +.
    assert aconv(parse("x + y * z = z"),
                 mk_eq(_mk_add(VX, _mk_mul(VY, VZ)), VZ))

    # Quantifiers, multi-var, type annotation pass-through.
    assert aconv(parse("!x y z. (x + y) + z = x + (y + z)"),
                 mk_forall(VX, mk_forall(VY, mk_forall(VZ,
                     mk_eq(_mk_add(_mk_add(VX, VY), VZ),
                           _mk_add(VX, _mk_add(VY, VZ)))))))

    # Logical ops + comparison.
    assert aconv(parse("!x y. x > y ==> x + 1 > y + 1"),
                 mk_forall(VX, mk_forall(VY,
                     mk_imp(_mk_gt(VX, VY),
                            _mk_gt(_mk_add(VX, ONE), _mk_add(VY, ONE))))))

    # Lambda.
    abs_t = parse("\\x. x + 1")
    assert aconv(abs_t, mk_abs(VX, _mk_add(VX, ONE)))

    # Free var with custom type via env.
    P_ty = mk_fun_ty(num_ty, bool_ty)
    P = mk_var("P", P_ty)
    assert aconv(parse("!x. P x", env={"P": P_ty}),
                 mk_forall(VX, mk_comb(P, VX)))

    # Nested quantifiers and negation.
    assert aconv(parse("!x. ~(x = 1) ==> ?u. x = SUC u"),
                 mk_forall(VX,
                     mk_imp(mk_not(mk_eq(VX, ONE)),
                            mk_exists(mk_var("u", num_ty),
                                mk_eq(VX, mk_suc(mk_var("u", num_ty)))))))


if __name__ == "__main__":
    _selftest()
    print("parser.py self-tests passed.")
