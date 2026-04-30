"""Lark-based parser for HOL terms, with an extensible operator registry.

The parser itself is agnostic about which operators, constants, and types
exist: those are registered by the modules that introduce them.  By the time
you `import nat`, the default signature (`DEFAULT_SIG`) has been populated
transitively:

  - ``axioms.py`` registers ``=``, ``/\\``, ``==>``, ``~``, and the ``bool`` type.
  - ``logic.py``  registers ``\\/``.
  - ``num.py``    registers ``1``, ``SUC``, and the ``num`` type.
  - ``nat.py``    registers ``+``, ``*``, ``>``, ``<``, ``>=``, ``<=``.

Then `parse(...)` works for the chapter-1 surface:

    from parser import parse
    target = parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y")

Adding a new operator is a single registration call in the module that
introduces the kernel constant; nothing in `parser.py` needs to change:

    DEFAULT_SIG.add_infix("-", 50, mk_sub, assoc="left")
    DEFAULT_SIG.add_const("0", ZERO)
    parse("x - 0 = x")

Or build a private `Signature` and pass it via `parse(s, sig=my_sig)`.

Free variables default to type `num` if a ``num`` type is registered, else
they have no default and `env={name: ty}` (or a kernel term) is required.
"""

from lark import Lark
from lark.visitors import Interpreter

from fusion import Var, Const, Comb, Abs, mk_var, mk_comb


class ParseError(Exception):
    pass


# ---------------------------------------------------------------------------
# Operator / constant / type registry.
# ---------------------------------------------------------------------------

class Signature:
    """Mutable registry of infix operators, prefix operators, named constants,
    and type names referenced in binder annotations.

    `add_infix(op, prec, builder, assoc="left")`:
        op       -- the operator symbol as it appears in source.
        prec     -- numeric precedence (higher = binds tighter).
        builder  -- ``(lhs_term, rhs_term) -> term``.
        assoc    -- ``"left"``, ``"right"``, or ``"non"``.

    `add_prefix(op, builder)`:
        builder  -- ``term -> term``.

    `add_const(name, term)`:
        Maps a parsed identifier (or numeric literal) directly to a kernel term.

    `add_type(name, ty)`:
        Registers a type name usable in binder annotations like ``!x:num. ...``.

    `add_binder(symbol, wrap)`:
        Registers a binder keyword (``"!"``, ``"?"``, ``"\\"``).
        ``wrap(var, body) -> term`` builds the bound term.
    """
    __slots__ = ("infix", "prefix", "const", "type", "binder", "default_var_ty")

    def __init__(self, default_var_ty=None):
        self.infix  = {}    # op_symbol -> (prec, assoc, builder)
        self.prefix = {}    # op_symbol -> builder
        self.const  = {}    # name      -> kernel term
        self.type   = {}    # type-name -> hol_type
        self.binder = {}    # binder-keyword -> wrap(var, body) -> term
        # The fallback type for a free variable that's neither in `env` nor
        # in `const`.  Set by whoever registers the "default" type (typically
        # `num.py`).  None means "free vars without a type are an error."
        self.default_var_ty = default_var_ty

    def add_infix(self, op, prec, builder, assoc="left"):
        if assoc not in ("left", "right", "non"):
            raise ValueError(f"assoc must be left/right/non, got {assoc!r}")
        self.infix[op] = (prec, assoc, builder)

    def add_prefix(self, op, builder):
        self.prefix[op] = builder

    def add_const(self, name, term):
        self.const[name] = term

    def add_type(self, name, ty):
        self.type[name] = ty

    def add_binder(self, symbol, wrap):
        if symbol not in ("!", "?", "\\"):
            raise ValueError(
                f"binder must be one of !, ?, \\\\ (got {symbol!r}); "
                "the grammar reserves only those three keywords")
        self.binder[symbol] = wrap


DEFAULT_SIG = Signature()


# ---------------------------------------------------------------------------
# Grammar (static -- operator semantics live in the registry, not here).
# ---------------------------------------------------------------------------

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
var_decl: NAME (":" NAME)?

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
        if name in self.env:
            binding = self.env[name]
            if isinstance(binding, (Var, Const, Comb, Abs)):
                return binding
            return mk_var(name, binding)
        # Otherwise a free variable at the registry's default type.
        ty = self.sig.default_var_ty
        if ty is None:
            raise ParseError(
                f"unknown identifier {name!r} (no default type registered; "
                "pass via `env=` or register a const/default type)")
        return mk_var(name, ty)

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
            ty = self.sig.default_var_ty
            if len(vd.children) > 1:
                ty_name = str(vd.children[1])
                if ty_name not in self.sig.type:
                    raise ParseError(f"unknown type name {ty_name!r}")
                ty = self.sig.type[ty_name]
            if ty is None:
                raise ParseError(
                    f"binder for {n!r} has no type and no default type "
                    "is registered")
            out.append((n, ty))
        return out

    def _binder(self, tree, symbol):
        wrap = self.sig.binder.get(symbol)
        if wrap is None:
            raise ParseError(f"binder {symbol!r} is not registered")
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

    def forall_(self, tree): return self._binder(tree, "!")
    def exists_(self, tree): return self._binder(tree, "?")
    def abs_(self,    tree): return self._binder(tree, "\\")

    # ----- prefix + flat infix chain -----

    def prefix_app(self, tree):
        op = str(tree.children[0])
        builder = self.sig.prefix.get(op)
        if builder is None:
            raise ParseError(f"unknown prefix operator {op!r}")
        return builder(self.visit(tree.children[1]))

    def infix_chain(self, tree):
        children = tree.children
        if len(children) == 1:
            return self.visit(children[0])
        terms = [self.visit(children[0])]
        ops = []
        for i in range(1, len(children), 2):
            op = str(children[i])
            meta = self.sig.infix.get(op)
            if meta is None:
                raise ParseError(f"unknown infix operator {op!r}")
            ops.append((op, *meta))           # (op, prec, assoc, builder)
            terms.append(self.visit(children[i + 1]))
        return _climb(terms, ops)


def _climb(terms, ops):
    """Precedence-climbing reducer for a flat infix chain.

    `terms`: N kernel terms.   `ops`: N-1 tuples ``(op, prec, assoc, builder)``.
    """
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
    default isn't right) or directly to a kernel term to substitute.

    `sig` is a `Signature`; defaults to `DEFAULT_SIG`."""
    tree = _PARSER.parse(s)
    return _Builder(sig or DEFAULT_SIG, env).visit(tree)


# ---------------------------------------------------------------------------
# Self-tests.
# ---------------------------------------------------------------------------

def _selftest():
    # Importing nat triggers the full chain of registrations
    # (axioms -> logic -> num -> nat) on DEFAULT_SIG.
    import nat  # noqa: F401
    from fusion import aconv, mk_const, mk_eq, mk_fun_ty
    from axioms import (
        bool_ty, mk_and, mk_imp, mk_not, mk_forall, mk_exists,
    )
    from fusion import mk_abs
    from num import x as VX, y as VY, z as VZ, mk_suc, num_ty, ONE

    def _mk(name):
        def _b(a, b):
            return mk_comb(mk_comb(mk_const(name, []), a), b)
        return _b
    _add, _mul, _gt = _mk("+"), _mk("*"), _mk(">")

    # --- existing surface ---------------------------------------------------

    assert aconv(parse("1 + 1"), _add(ONE, ONE))
    assert aconv(parse("SUC 1"), mk_suc(ONE))
    assert aconv(parse("(SUC x) * (SUC y) = x * (SUC y) + SUC y"),
                 mk_eq(_mul(mk_suc(VX), mk_suc(VY)),
                       _add(_mul(VX, mk_suc(VY)), mk_suc(VY))))
    assert aconv(parse("x + y * z = z"),
                 mk_eq(_add(VX, _mul(VY, VZ)), VZ))
    assert aconv(parse("x + y + z"), _add(_add(VX, VY), VZ))    # left-assoc

    # right-assoc /\
    P_ty = mk_fun_ty(num_ty, bool_ty)
    P, Q, R = mk_var("P", P_ty), mk_var("Q", P_ty), mk_var("R", P_ty)
    env_pqr = {"P": P_ty, "Q": P_ty, "R": P_ty}
    assert aconv(parse("P x /\\ Q x /\\ R x", env=env_pqr),
                 mk_and(mk_comb(P, VX),
                        mk_and(mk_comb(Q, VX), mk_comb(R, VX))))

    # quantifiers, binders on rhs of ==>
    assert aconv(parse("!x y z. (x + y) + z = x + (y + z)"),
                 mk_forall(VX, mk_forall(VY, mk_forall(VZ,
                     mk_eq(_add(_add(VX, VY), VZ),
                           _add(VX, _add(VY, VZ)))))))
    assert aconv(parse("!x y. x > y ==> x + 1 > y + 1"),
                 mk_forall(VX, mk_forall(VY,
                     mk_imp(_gt(VX, VY),
                            _gt(_add(VX, ONE), _add(VY, ONE))))))
    assert aconv(parse("\\x. x + 1"), mk_abs(VX, _add(VX, ONE)))
    assert aconv(parse("!x. P x", env={"P": P_ty}),
                 mk_forall(VX, mk_comb(P, VX)))
    assert aconv(parse("!x. ~(x = 1) ==> ?u. x = SUC u"),
                 mk_forall(VX,
                     mk_imp(mk_not(mk_eq(VX, ONE)),
                            mk_exists(mk_var("u", num_ty),
                                mk_eq(VX, mk_suc(mk_var("u", num_ty)))))))

    # binder annotations work via the registered `bool` type.
    assert aconv(parse("!p:bool. ~~p ==> p"),
                 mk_forall(mk_var("p", bool_ty),
                     mk_imp(mk_not(mk_not(mk_var("p", bool_ty))),
                            mk_var("p", bool_ty))))

    # non-associativity error
    try:
        parse("x = y = z")
    except ParseError:
        pass
    else:
        raise AssertionError("expected ParseError for chained '='")

    # --- extension at runtime ----------------------------------------------
    DEFAULT_SIG.add_infix("&&", 55, mk_and, assoc="left")
    try:
        got = parse("P x && Q x", env=env_pqr)
        assert aconv(got, mk_and(mk_comb(P, VX), mk_comb(Q, VX)))
    finally:
        del DEFAULT_SIG.infix["&&"]

    # --- fresh, minimal Signature -----------------------------------------
    fresh = Signature(default_var_ty=num_ty)
    fresh.add_infix("=", 40, mk_eq,   assoc="non")
    fresh.add_infix("+", 50, _add,    assoc="left")
    a, b, c = mk_var("a", num_ty), mk_var("b", num_ty), mk_var("c", num_ty)
    assert aconv(parse("a + b = c", sig=fresh), mk_eq(_add(a, b), c))
    for bad, kind in [("a * b", "infix"), ("~a", "prefix")]:
        try:
            parse(bad, sig=fresh)
        except ParseError:
            pass
        else:
            raise AssertionError(f"expected ParseError for unknown {kind}")

    # bare Signature has no default var type -> free var without env errors.
    bare = Signature()
    bare.add_infix("=", 40, mk_eq, assoc="non")
    try:
        parse("a = b", sig=bare)
    except ParseError:
        pass
    else:
        raise AssertionError("expected ParseError when no default var type")


if __name__ == "__main__":
    # When run as `python parser.py`, this file is `__main__`.  Sibling
    # modules (axioms, logic, num, nat) register operators on the
    # `DEFAULT_SIG` of the *imported* `parser` module, which is a separate
    # instance.  Re-import here so the test reads from the same instance.
    import parser as _p
    _p._selftest()
    print("parser.py self-tests passed.")
