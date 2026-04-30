"""Lark-based parser for HOL terms with an extensible operator registry.

Usage:
    from parser import parse
    target = parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y")

The default signature covers the operators used in chapter 1:
  - Numerals:    1
  - Successor:   SUC e
  - Arithmetic:  e + e, e * e
  - Comparison:  =, <, >, <=, >=
  - Logical:     ~, /\\, \\/, ==>
  - Quantifiers: !x. body, ?x. body, !x y z. body, !x:num. body
  - Lambda:      \\x. body
  - Application: f x

To add a new operator without editing this file:

    from parser import DEFAULT_SIG, parse
    DEFAULT_SIG.add_infix("-", 50, mk_sub, assoc="left")
    DEFAULT_SIG.add_const("0", ZERO)
    parse("x - 0 = x")

Or build a private `Signature` and pass it via `parse(s, sig=my_sig)`.

Free variables default to type `num`; pass `env={name: ty}` (or a kernel term)
to override.
"""

from lark import Lark
from lark.visitors import Interpreter

from fusion import (
    Var, Const, Comb, Abs, mk_var, mk_abs, mk_comb, mk_const, mk_eq,
)
from axioms import (
    bool_ty, mk_and, mk_imp, mk_forall, mk_exists, mk_not,
)
from logic import mk_or
from num import num_ty, ONE, SUC


class ParseError(Exception):
    pass


# ---------------------------------------------------------------------------
# Operator / constant registry.
# ---------------------------------------------------------------------------

class Signature:
    """Mutable registry of infix operators, prefix operators, and constants.

    `add_infix(op, prec, builder, assoc="left")`:
        op       -- the operator symbol as it appears in source.
        prec     -- numeric precedence (higher = binds tighter).
        builder  -- a Python function `(lhs_term, rhs_term) -> term`.
        assoc    -- "left", "right", or "non".

    `add_prefix(op, builder)`:
        builder  -- a function `term -> term`.

    `add_const(name, term)`:
        Maps a parsed identifier (or numeric literal) to a kernel term.
    """
    __slots__ = ("infix", "prefix", "const")

    def __init__(self):
        self.infix  = {}   # op_symbol -> (prec, assoc, builder)
        self.prefix = {}   # op_symbol -> builder
        self.const  = {}   # name      -> kernel term

    def add_infix(self, op, prec, builder, assoc="left"):
        if assoc not in ("left", "right", "non"):
            raise ValueError(f"assoc must be left/right/non, got {assoc!r}")
        self.infix[op] = (prec, assoc, builder)

    def add_prefix(self, op, builder):
        self.prefix[op] = builder

    def add_const(self, name, term):
        self.const[name] = term


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


DEFAULT_SIG = Signature()
# Logical connectives (lowest precedence first; right-assoc by HOL Light convention).
DEFAULT_SIG.add_infix("==>", 10, mk_imp,  assoc="right")
DEFAULT_SIG.add_infix("\\/", 20, mk_or,   assoc="right")
DEFAULT_SIG.add_infix("/\\", 30, mk_and,  assoc="right")
# Comparisons (non-associative).
DEFAULT_SIG.add_infix("=",  40, mk_eq,    assoc="non")
DEFAULT_SIG.add_infix("<",  40, _mk_lt,   assoc="non")
DEFAULT_SIG.add_infix(">",  40, _mk_gt,   assoc="non")
DEFAULT_SIG.add_infix("<=", 40, _mk_le,   assoc="non")
DEFAULT_SIG.add_infix(">=", 40, _mk_ge,   assoc="non")
# Arithmetic (left-associative).
DEFAULT_SIG.add_infix("+",  50, _mk_add,  assoc="left")
DEFAULT_SIG.add_infix("*",  60, _mk_mul,  assoc="left")
# Prefix.
DEFAULT_SIG.add_prefix("~", mk_not)
# Constants.
DEFAULT_SIG.add_const("SUC", SUC)
DEFAULT_SIG.add_const("1", ONE)


# ---------------------------------------------------------------------------
# Grammar (static -- operator semantics live in the registry, not here).
# ---------------------------------------------------------------------------

_TYPES = {"num": num_ty, "bool": bool_ty}

_GRAMMAR = r"""
?start: term

?term: binder | infix_chain

binder: "!" varlist "." term       -> forall_
      | "?" varlist "." term       -> exists_
      | "\\" varlist "." term      -> abs_

infix_chain: prefix_term (OP rhs_term)*

?rhs_term: binder | prefix_term

?prefix_term: OP prefix_term       -> prefix_app
            | app_term

?app_term: app_term atom            -> app_
         | atom

?atom: "(" term ")"
     | NUM                          -> num_
     | NAME                         -> name

varlist: var_decl+
var_decl: NAME (":" TYPE)?

TYPE.2: "num" | "bool"
NAME: /[A-Za-z_][A-Za-z0-9_]*/
NUM:  /[0-9]+/
OP:   /[+\-*=<>^&|\/\\]+|~/

%ignore /[ \t\r\n]+/
"""

_PARSER = Lark(_GRAMMAR, parser="lalr", start="start")


# ---------------------------------------------------------------------------
# Visitor: builds kernel terms by consulting the registry.
# ---------------------------------------------------------------------------

class _Builder(Interpreter):
    def __init__(self, sig, env):
        super().__init__()
        self.sig = sig
        self.env = dict(env or {})
        self.scope = []          # stack of {name: Var}

    # ----- atom resolution -----

    def _lookup(self, name):
        # Bound variable shadows everything else.
        for s in reversed(self.scope):
            if name in s:
                return s[name]
        # Then registered constants.
        if name in self.sig.const:
            return self.sig.const[name]
        # Then env-provided binding (kernel term or hol_type).
        binding = self.env.get(name, num_ty)
        if isinstance(binding, (Var, Const, Comb, Abs)):
            return binding
        return mk_var(name, binding)

    def name(self, tree):
        return self._lookup(str(tree.children[0]))

    def num_(self, tree):
        s = str(tree.children[0])
        if s in self.sig.const:
            return self.sig.const[s]
        raise ParseError(f"unknown numeric literal {s!r}")

    # ----- application + binders -----

    def app_(self, tree):
        f, a = self.visit(tree.children[0]), self.visit(tree.children[1])
        return mk_comb(f, a)

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

    def forall_(self, tree): return self._binder(tree, mk_forall)
    def exists_(self, tree): return self._binder(tree, mk_exists)
    def abs_(self,    tree): return self._binder(tree, mk_abs)

    # ----- prefix + flat infix chain -----

    def prefix_app(self, tree):
        op = str(tree.children[0])
        builder = self.sig.prefix.get(op)
        if builder is None:
            raise ParseError(f"unknown prefix operator {op!r}")
        return builder(self.visit(tree.children[1]))

    def infix_chain(self, tree):
        # Children alternate: term, OP, term, OP, ..., term.
        children = tree.children
        if len(children) == 1:
            return self.visit(children[0])
        # Build the alternating sequence.
        terms = [self.visit(children[0])]
        ops_with_meta = []
        for i in range(1, len(children), 2):
            op = str(children[i])
            meta = self.sig.infix.get(op)
            if meta is None:
                raise ParseError(f"unknown infix operator {op!r}")
            ops_with_meta.append((op, *meta))      # (op, prec, assoc, builder)
            terms.append(self.visit(children[i + 1]))
        return _climb(terms, ops_with_meta)


def _climb(terms, ops):
    """Precedence-climbing reducer for a flat infix chain.

    `terms`: list of N kernel terms.
    `ops`:   list of N-1 tuples `(op, prec, assoc, builder)`.
    Returns the single combined term.
    """
    # Output stack of partial terms; op_stack of (op, prec, assoc, builder).
    out = [terms[0]]
    op_stack = []

    def reduce_top():
        op, prec, assoc, builder = op_stack.pop()
        rhs = out.pop()
        lhs = out.pop()
        out.append(builder(lhs, rhs))

    for (op, prec, assoc, builder), rhs in zip(ops, terms[1:]):
        while op_stack:
            top_op, top_prec, top_assoc, _ = op_stack[-1]
            if top_prec > prec or (top_prec == prec and top_assoc == "left"):
                reduce_top()
                continue
            if top_prec == prec and top_assoc == "non":
                raise ParseError(
                    f"non-associative operator {op!r} cannot chain with {top_op!r}")
            break
        out.append(rhs)
        op_stack.append((op, prec, assoc, builder))

    while op_stack:
        reduce_top()
    return out[0]


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------

def parse(s, env=None, sig=None):
    """Parse `s` into a kernel term.

    `env` maps free-variable names either to their `hol_type` (when the
    default `num` is wrong, e.g. `{"P": mk_fun_ty(num_ty, bool_ty)}`) or
    directly to a kernel term to substitute for that name.

    `sig` is a `Signature`; defaults to `DEFAULT_SIG`."""
    tree = _PARSER.parse(s)
    return _Builder(sig or DEFAULT_SIG, env).visit(tree)


# ---------------------------------------------------------------------------
# Self-tests.
# ---------------------------------------------------------------------------

def _selftest():
    import nat  # noqa: F401  -- registers +, *, >, <, etc. as kernel constants
    from fusion import aconv, mk_fun_ty
    from num import x as VX, y as VY, z as VZ, mk_suc

    # --- Existing surface coverage -----------------------------------------

    assert aconv(parse("1 + 1"), _mk_add(ONE, ONE))
    assert aconv(parse("SUC 1"), mk_suc(ONE))
    assert aconv(parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y"),
                 mk_eq(_mk_mul(mk_suc(VX), mk_suc(VY)),
                       _mk_add(_mk_mul(VX, mk_suc(VY)), mk_suc(VY))))

    # Precedence: + binds tighter than =, * tighter than +.
    assert aconv(parse("x + y * z = z"),
                 mk_eq(_mk_add(VX, _mk_mul(VY, VZ)), VZ))

    # Left-associativity: a + b + c -> (a + b) + c.
    assert aconv(parse("x + y + z"),
                 _mk_add(_mk_add(VX, VY), VZ))

    # Right-associativity: a /\ b /\ c -> a /\ (b /\ c).
    P_ty = mk_fun_ty(num_ty, bool_ty)
    P = mk_var("P", P_ty)
    Q = mk_var("Q", P_ty)
    R = mk_var("R", P_ty)
    env_pqr = {"P": P_ty, "Q": P_ty, "R": P_ty}
    assert aconv(parse("P x /\\ Q x /\\ R x", env=env_pqr),
                 mk_and(mk_comb(P, VX),
                        mk_and(mk_comb(Q, VX), mk_comb(R, VX))))

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
    assert aconv(parse("\\x. x + 1"), mk_abs(VX, _mk_add(VX, ONE)))

    # Free var with custom type via env.
    assert aconv(parse("!x. P x", env={"P": P_ty}),
                 mk_forall(VX, mk_comb(P, VX)))

    # Nested quantifiers and negation.
    assert aconv(parse("!x. ~(x = 1) ==> ?u. x = SUC u"),
                 mk_forall(VX,
                     mk_imp(mk_not(mk_eq(VX, ONE)),
                            mk_exists(mk_var("u", num_ty),
                                mk_eq(VX, mk_suc(mk_var("u", num_ty)))))))

    # Non-associativity: a = b = c should error.
    try:
        parse("x = y = z")
    except ParseError:
        pass
    else:
        raise AssertionError("expected ParseError for chained '='")

    # --- Extension: register a new infix operator on DEFAULT_SIG -----------
    # `&&` builds a fictitious term using mk_and (chosen so we can verify
    # without dragging in a fresh kernel constant).  Precedence between * and +.
    DEFAULT_SIG.add_infix("&&", 55, mk_and, assoc="left")
    try:
        # We need a P, Q : bool to feed mk_and; reuse predicate-applied vars.
        got = parse("P x && Q x", env=env_pqr)
        assert aconv(got, mk_and(mk_comb(P, VX), mk_comb(Q, VX)))
    finally:
        del DEFAULT_SIG.infix["&&"]   # don't leak into other tests

    # --- Extension: build a fresh, minimal Signature -----------------------
    fresh = Signature()
    fresh.add_infix("=", 40, mk_eq,    assoc="non")
    fresh.add_infix("+", 50, _mk_add,  assoc="left")
    a = mk_var("a", num_ty)
    b = mk_var("b", num_ty)
    c = mk_var("c", num_ty)
    assert aconv(parse("a + b = c", sig=fresh),
                 mk_eq(_mk_add(a, b), c))
    # `*` is unknown to `fresh` -- should raise.
    try:
        parse("a * b", sig=fresh)
    except ParseError:
        pass
    else:
        raise AssertionError("expected ParseError for unknown '*' in fresh sig")

    # `~` is unknown as a prefix in `fresh` -- should raise.
    try:
        parse("~a", sig=fresh)
    except ParseError:
        pass
    else:
        raise AssertionError("expected ParseError for unknown '~' in fresh sig")


if __name__ == "__main__":
    _selftest()
    print("parser.py self-tests passed.")
