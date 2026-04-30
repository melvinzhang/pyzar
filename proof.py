"""Hybrid Isar declarative proof DSL.

Each ``have`` produces one kernel theorem; the ``Proof`` object tracks named
facts and discharges blocks via the existing primitives (``INDUCT_PROVE``,
``DISJ_CASES``, ``DISCH`` / ``GEN``, ``REWRITE_PROVE``, ``MP_LIST``).

Usage:

    from proof import proof
    from nat import ADD_1, ADD_SUC

    @proof
    def SATZ_5(p):
        p.goal("!x y z. (x + y) + z = x + (y + z)")
        p.fix("x y z")
        with p.induction("z"):
            with p.base():
                p.thus("(x + y) + 1 = x + (y + 1)")\
                    .by_rewrite([ADD_1, ADD_SUC])
            with p.step("IH"):
                p.thus("(x + y) + SUC z = x + (y + SUC z)")\
                    .by_rewrite([ADD_SUC, "IH"])

The decorator runs the script and returns the resulting kernel theorem.
"""

import re

from fusion import (
    Const, Comb, Abs, thm,
    aconv, concl, HolError, ASSUME, EQ_MP,
)
from logic import pp, SPEC, GEN, DISCH, MP_LIST, DISJ_CASES, _subst_term
from tactics import REWRITE_PROVE, REWRITE_RULE, AC_PROVE, REWRITE_AC_PROVE
from parser import parse, ParseError
from num import INDUCT_PROVE, mk_suc, ONE


# ---------------------------------------------------------------------------
# Frame: a single open scope (root, induction body, base/step, case).
# ---------------------------------------------------------------------------

class _Frame:
    __slots__ = ("goal", "kind", "vars_added", "hyps_added",
                 "facts_added", "data", "result")

    def __init__(self, goal=None, kind="root"):
        self.goal = goal
        self.kind = kind
        self.vars_added = []      # for fix(): GEN at close
        self.hyps_added = []      # for assume(): list of (label, term); DISCH at close
        self.facts_added = []     # labels added at this frame; popped on exit
        self.data = {}            # block-specific scratch
        self.result = None        # the theorem proving `goal`


# ---------------------------------------------------------------------------
# Proof object: stack of frames + name->thm registry.
# ---------------------------------------------------------------------------

class Proof:
    def __init__(self):
        self._frames = [_Frame(kind="root")]
        self._facts = {}          # label -> thm
        self._fact_order = []     # insertion order for negative-index lookup
        self._anon = 0

    @property
    def _cur(self):
        return self._frames[-1]

    # ---- env / parsing ---------------------------------------------------

    def _scope_env(self):
        env = {}
        for fr in self._frames:
            for v in fr.vars_added:
                env[v.name] = v
        return env

    def _parse(self, s):
        return parse(s, env=self._scope_env())

    _LABEL_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z_0-9]*)\s*:\s*(.+)$", re.DOTALL)

    def _split_label(self, spec):
        """Parse 'label: term' or 'term'.

        Returns ``(label_or_None, kernel_term)``. Tries label-form first; if
        the remainder fails to parse, falls back to treating the whole spec
        as a term (so ``"!x:num. x = x"`` survives).
        """
        m = self._LABEL_RE.match(spec)
        if m:
            label = m.group(1)
            rest = m.group(2)
            try:
                return label, self._parse(rest)
            except ParseError:
                pass
        return None, self._parse(spec)

    def _fresh_label(self, prefix="h"):
        while True:
            self._anon += 1
            name = f"_{prefix}{self._anon}"
            if name not in self._facts:
                return name

    # ---- facts -----------------------------------------------------------

    def _register_fact(self, label, th):
        if label in self._facts:
            raise HolError(f"duplicate fact label: {label!r}")
        self._facts[label] = th
        self._fact_order.append(label)
        self._cur.facts_added.append(label)

    def _drop_facts(self, labels):
        for label in labels:
            self._facts.pop(label, None)
        if labels:
            drop = set(labels)
            self._fact_order = [l for l in self._fact_order if l not in drop]

    def _resolve_fact(self, ref):
        """Resolve `ref` to a theorem.

        Accepts a ``thm`` directly, a string label, or a negative integer
        (index into insertion order)."""
        if isinstance(ref, thm):
            return ref
        if isinstance(ref, str):
            if ref in self._facts:
                return self._facts[ref]
            raise HolError(f"unknown fact label: {ref!r}")
        if isinstance(ref, int):
            try:
                return self._facts[self._fact_order[ref]]
            except IndexError:
                raise HolError(f"fact index out of range: {ref}")
        raise HolError(f"cannot resolve fact reference: {ref!r}")

    def fact(self, ref):
        """Public accessor: returns the theorem associated with a label or index."""
        return self._resolve_fact(ref)

    def _resolve_fact_or_term(self, ref):
        """Like _resolve_fact but a non-fact string is parsed as a term."""
        if isinstance(ref, thm):
            return ref
        if isinstance(ref, int):
            return self._resolve_fact(ref)
        if isinstance(ref, str):
            if ref in self._facts:
                return self._facts[ref]
            return self._parse(ref)
        return ref

    # ---- public API: opening declarations --------------------------------

    def goal(self, spec):
        if self._cur.goal is not None:
            raise HolError("goal: already set on current frame")
        self._cur.goal = self._parse(spec)

    def fix(self, names):
        if isinstance(names, str):
            names = names.split()
        for nm in names:
            g = self._cur.goal
            if not (isinstance(g, Comb) and isinstance(g.fun, Const)
                    and g.fun.name == "!" and isinstance(g.arg, Abs)):
                raise HolError(f"fix({nm!r}): goal is not a forall: {pp(g)}")
            v = g.arg.bvar
            if v.name != nm:
                raise HolError(
                    f"fix: name mismatch -- binder is {v.name!r}, given {nm!r}")
            self._cur.goal = g.arg.body
            self._cur.vars_added.append(v)

    def assume(self, *labelled):
        for spec in labelled:
            label, term = self._split_label(spec)
            if label is None:
                label = self._fresh_label("h")
            g = self._cur.goal
            if not (isinstance(g, Comb) and isinstance(g.fun, Comb)
                    and isinstance(g.fun.fun, Const)
                    and g.fun.fun.name == "==>"):
                raise HolError(f"assume: goal is not an implication: {pp(g)}")
            ant = g.fun.arg
            cons = g.arg
            if not aconv(ant, term):
                raise HolError(
                    "assume: hypothesis does not match antecedent\n"
                    f"  antecedent: {pp(ant)}\n  given:      {pp(term)}")
            self._cur.goal = cons
            self._cur.hyps_added.append((label, ant))
            self._register_fact(label, ASSUME(ant))

    # ---- have / thus -----------------------------------------------------

    def have(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=False)

    def thus(self, spec):
        label, term = self._split_label(spec)
        return _Have(self, label, term, is_thus=True)

    # ---- block constructs ------------------------------------------------

    def induction(self, var_name):
        env = self._scope_env()
        if var_name not in env:
            raise HolError(f"induction: unknown variable {var_name!r}")
        var = env[var_name]
        body = self._cur.goal
        if body is None:
            raise HolError("induction: no current goal")
        return _InductionCtx(self, var, body)

    def base(self):
        fr = self._cur
        if fr.kind != "_induction":
            raise HolError("base() outside induction()")
        var = fr.data["var"]
        body = fr.data["body"]
        sub_goal = _subst_term(var, ONE, body)

        def on_close(th):
            fr.data["base_th"] = th

        return _SubFrameCtx(self, sub_goal, kind="ind_base",
                             on_close=on_close)

    def step(self, ih_label="IH"):
        fr = self._cur
        if fr.kind != "_induction":
            raise HolError("step() outside induction()")
        var = fr.data["var"]
        body = fr.data["body"]
        sub_goal = _subst_term(var, mk_suc(var), body)

        def on_close(th):
            fr.data["step_th"] = th

        return _SubFrameCtx(self, sub_goal, kind="ind_step",
                             on_close=on_close,
                             extra_facts=[(ih_label, ASSUME(body))])

    def cases_on(self, ref):
        or_th = self._resolve_fact(ref)
        c = or_th._concl
        # Expect (p \/ q) at the top.
        if not (isinstance(c, Comb) and isinstance(c.fun, Comb)
                and isinstance(c.fun.fun, Const)
                and c.fun.fun.name == "\\/"):
            raise HolError(f"cases_on: not a disjunction: {pp(c)}")
        return _CasesCtx(self, or_th)

    def case(self, branch_spec):
        fr = self._cur
        if fr.kind != "_cases":
            raise HolError("case() outside cases_on()")
        branch_term = self._parse(branch_spec)
        outer_goal = fr.data["goal"]
        if aconv(branch_term, fr.data["left"]):
            slot = "left"
        elif aconv(branch_term, fr.data["right"]):
            slot = "right"
        else:
            raise HolError(
                f"case: branch {pp(branch_term)} does not match either disjunct\n"
                f"  left:  {pp(fr.data['left'])}\n"
                f"  right: {pp(fr.data['right'])}")

        def on_close(th):
            fr.data[slot + "_th"] = (branch_term, th)

        return _SubFrameCtx(self, outer_goal, kind="case",
                             on_close=on_close,
                             extra_facts=[(None, ASSUME(branch_term))])


# ---------------------------------------------------------------------------
# Have / Thus: justification dispatchers.
# ---------------------------------------------------------------------------

class _Have:
    __slots__ = ("p", "label", "term", "is_thus")

    def __init__(self, p, label, term, is_thus):
        self.p = p
        self.label = label
        self.term = term
        self.is_thus = is_thus

    # ----- finishing: alpha-check, register, optionally close goal -----

    def _finish(self, th):
        if not aconv(concl(th), self.term):
            raise HolError(
                "have: justification produced wrong conclusion\n"
                f"  expected: {pp(self.term)}\n"
                f"  got:      {pp(concl(th))}")
        label = self.label or self.p._fresh_label("h")
        self.p._register_fact(label, th)
        if self.is_thus:
            cur = self.p._cur
            if cur.goal is None or not aconv(cur.goal, self.term):
                raise HolError(
                    "thus: term does not match current goal\n"
                    f"  goal: {pp(cur.goal) if cur.goal is not None else 'None'}\n"
                    f"  thus: {pp(self.term)}")
            cur.result = th
        return th

    # ----- justification methods -----

    def by_thm(self, th):
        """Direct: the supplied theorem already proves the have-term."""
        return self._finish(th)

    def by(self, justification, *args):
        """SPEC/MP chain (if `justification` is a theorem) or a callable.

        - ``thm + args``: each arg is dispatched via MP_LIST -- a Term arg
          becomes ``SPEC``, a Theorem arg becomes ``MP``. Strings are
          interpreted as fact labels (theorem) when known, else parsed as
          terms.
        - ``callable + args``: each arg is resolved as a fact (string label,
          negative index, or theorem); the callable is invoked on them.
        """
        if isinstance(justification, thm):
            resolved = [self.p._resolve_fact_or_term(a) for a in args]
            return self._finish(MP_LIST(justification, resolved))
        if callable(justification):
            resolved = [self.p._resolve_fact(a) for a in args]
            return self._finish(justification(*resolved))
        raise HolError(
            f"by: not a theorem or callable: {justification!r}")

    def by_rewrite(self, rules):
        """REWRITE_PROVE with the given rules.

        Each rule may be a Theorem or a string label naming a fact in scope.
        """
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        return self._finish(REWRITE_PROVE(rule_thms, self.term))

    def by_rewrite_of(self, ref, rules):
        """Rewrite an existing fact `ref` with `rules` to obtain the have-term."""
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        fact_th = self.p._resolve_fact(ref)
        return self._finish(REWRITE_RULE(rule_thms, fact_th))

    def by_eq_mp(self, eq_th, ref):
        """``EQ_MP(eq_th, fact)`` -- rewrite a fact through an equation."""
        return self._finish(EQ_MP(eq_th, self.p._resolve_fact(ref)))

    def by_ac(self, op, assoc, comm):
        """AC_PROVE under ``(op, assoc, comm)`` for the (equation) have-term."""
        return self._finish(AC_PROVE(op, assoc, comm, self.term))

    def by_rewrite_ac(self, rules, op, assoc, comm, ac_rules=()):
        """REWRITE_AC_PROVE -- rewrite both sides under ``rules`` (and optional
        ``ac_rules`` for canonicalisation), then close by AC over ``op``."""
        rule_thms = [self.p._resolve_fact(r) if not isinstance(r, thm) else r
                     for r in rules]
        ac_thms = tuple(self.p._resolve_fact(r) if not isinstance(r, thm) else r
                        for r in ac_rules)
        return self._finish(REWRITE_AC_PROVE(rule_thms, op, assoc, comm,
                                              self.term, ac_rules=ac_thms))


# ---------------------------------------------------------------------------
# Sub-frame context manager: pushes a frame with a sub-goal, on exit verifies
# discharge and reports the result back to the parent via ``on_close``.
# ---------------------------------------------------------------------------

class _SubFrameCtx:
    def __init__(self, p, goal, kind, on_close, extra_facts=()):
        self.p = p
        self.goal = goal
        self.kind = kind
        self.on_close = on_close
        self.extra_facts = list(extra_facts)

    def __enter__(self):
        fr = _Frame(goal=self.goal, kind=self.kind)
        self.p._frames.append(fr)
        for label, th in self.extra_facts:
            if label is None:
                label = self.p._fresh_label("h")
            self.p._register_fact(label, th)
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        if fr.result is None:
            raise HolError(
                f"{self.kind}: block did not discharge sub-goal via thus")
        self.p._drop_facts(fr.facts_added)
        self.on_close(fr.result)
        return False


# ---------------------------------------------------------------------------
# Induction block: pushes an "_induction" frame whose .base() / .step()
# children fill in base_th / step_th. On exit, INDUCT_PROVE composes them and
# the result is set as the parent frame's .result, after SPEC'ing the
# induction variable so the resulting term matches the parent's body-shaped
# goal (the outer fix() will GEN it back).
# ---------------------------------------------------------------------------

class _InductionCtx:
    def __init__(self, p, var, body):
        self.p = p
        self.var = var
        self.body = body

    def __enter__(self):
        fr = _Frame(goal=None, kind="_induction")
        fr.data = {"var": self.var, "body": self.body,
                   "base_th": None, "step_th": None}
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        d = fr.data
        if d["base_th"] is None:
            raise HolError("induction: missing base()")
        if d["step_th"] is None:
            raise HolError("induction: missing step()")
        # User's step_th already contains ASSUME(body) as a hypothesis (under
        # the IH label). INDUCT_PROVE wraps that with DISCH(body, ...) and
        # GEN(var, ...) to produce |- !var. body. We SPEC var back out so the
        # parent's body-shaped goal matches.
        forall_th = INDUCT_PROVE(self.var, self.body, d["base_th"],
                                  lambda IH: d["step_th"])
        body_th = SPEC(self.var, forall_th)
        self.p._drop_facts(fr.facts_added)
        parent = self.p._cur
        if parent.goal is None or not aconv(parent.goal, body_th._concl):
            raise HolError(
                "induction: produced wrong conclusion\n"
                f"  goal: {pp(parent.goal) if parent.goal else 'None'}\n"
                f"  got:  {pp(body_th._concl)}")
        parent.result = body_th
        return False


# ---------------------------------------------------------------------------
# cases_on block: pushes a "_cases" frame; .case() children supply each
# branch's proof under an extra hypothesis. On exit, DISJ_CASES composes them.
# ---------------------------------------------------------------------------

class _CasesCtx:
    def __init__(self, p, or_th):
        self.p = p
        self.or_th = or_th
        c = or_th._concl
        self.left = c.fun.arg
        self.right = c.arg

    def __enter__(self):
        fr = _Frame(goal=self.p._cur.goal, kind="_cases")
        # The "_cases" frame inherits the parent's goal so case() can see it.
        fr.data = {"goal": self.p._cur.goal,
                   "left": self.left, "right": self.right,
                   "left_th": None, "right_th": None}
        self.p._frames.append(fr)
        return self.p

    def __exit__(self, exc_type, *_):
        if exc_type is not None:
            return False
        fr = self.p._frames.pop()
        d = fr.data
        if d["left_th"] is None or d["right_th"] is None:
            raise HolError("cases_on: missing one or both case() blocks")
        l_term, l_th = d["left_th"]
        r_term, r_th = d["right_th"]
        branch_l = DISCH(l_term, l_th)
        branch_r = DISCH(r_term, r_th)
        result = DISJ_CASES(self.or_th, branch_l, branch_r)
        self.p._drop_facts(fr.facts_added)
        parent = self.p._cur
        if parent.goal is None or not aconv(parent.goal, result._concl):
            raise HolError(
                "cases_on: produced wrong conclusion\n"
                f"  goal: {pp(parent.goal) if parent.goal else 'None'}\n"
                f"  got:  {pp(result._concl)}")
        parent.result = result
        return False


# ---------------------------------------------------------------------------
# Decorator: runs the script function and returns the kernel theorem.
# ---------------------------------------------------------------------------

def proof(fn):
    p = Proof()
    fn(p)
    if len(p._frames) != 1:
        raise HolError(
            f"proof({fn.__name__}): unbalanced frames at end ({len(p._frames)} open)")
    fr = p._frames[0]
    if fr.result is None:
        raise HolError(
            f"proof({fn.__name__}): no result -- did you forget thus or close a block?")
    th = fr.result
    for label, term in reversed(fr.hyps_added):
        th = DISCH(term, th)
    for v in reversed(fr.vars_added):
        th = GEN(v, th)
    return th


# ---------------------------------------------------------------------------
# Self-test: port SATZ_5 (induction + rewrite) and SATZ_17 (cases_on) and
# verify they alpha-equal the existing theorems in nat.py.
# ---------------------------------------------------------------------------

def _selftest():
    import nat
    from nat import (
        ADD_1, ADD_SUC, UNFOLD_LE, LT_TO_LE, SATZ_16A,
    )

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
    from nat import x as VX, y as VY, z as VZ

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


if __name__ == "__main__":
    _selftest()
    print("proof.py self-tests passed.")
