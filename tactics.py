"""Higher-level tactics built on the kernel + logic.py.

Public API:
  REWRITE_CONV(rules, tm)  -- |- tm = tm', rewriting tm with the given equation
                              theorems to fixpoint, bottom-up.
  REWRITE_RULE(rules, th)  -- rewrite th's conclusion.
  REWRITE_PROVE(rules, eq) -- prove an equation `lhs = rhs` by reducing both
                              sides to a common normal form.

A "rule" is any theorem of the form  |- !v1...vn. lhs = rhs  (outer foralls
are stripped; the freed vars become pattern variables).  Theorems with no
outer forall are usable too: their free vars act as literal pattern atoms,
which lets you pass an induction hypothesis as a rewrite directly.

First-order matching only.  Lambdas in patterns must alpha-match exactly.
"""

from fusion import (
    Var, Const, Comb, Abs,
    type_of, dest_eq, rand, aconv, HolError,
    REFL, TRANS, MK_COMB, EQ_MP, INST,
)
from logic import SPEC, SYM


# ---------------------------------------------------------------------------
# Internal: rule preparation and matching.
# ---------------------------------------------------------------------------

def _strip_forall(th):
    """Strip outer (!v. ...) layers from th, returning (vars, th_body)."""
    vs = []
    while True:
        c = th._concl
        if (isinstance(c, Comb) and isinstance(c.fun, Const)
                and c.fun.name == "!" and isinstance(c.arg, Abs)):
            v = c.arg.bvar
            th = SPEC(v, th)
            vs.append(v)
        else:
            break
    return vs, th


def _prepare_rule(th):
    """Strip foralls, extract LHS/RHS.  Returns (vars, lhs, rhs, eq_th) or None."""
    vs, body = _strip_forall(th)
    try:
        lhs, rhs = dest_eq(body._concl)
    except Exception:
        return None
    return vs, lhs, rhs, body


def _term_match(pat, tgt, vars_set, subst):
    """First-order match of pat against tgt.
       pat-vars in vars_set are match variables; others must match literally.
       Returns extended subst dict, or None on failure."""
    if isinstance(pat, Var) and pat in vars_set:
        if pat in subst:
            return subst if aconv(subst[pat], tgt) else None
        if type_of(pat) != type_of(tgt):
            return None
        s = dict(subst); s[pat] = tgt
        return s
    if isinstance(pat, Var) and isinstance(tgt, Var):
        return subst if (pat.name == tgt.name and pat.ty == tgt.ty) else None
    if isinstance(pat, Const) and isinstance(tgt, Const):
        return subst if (pat.name == tgt.name and pat.ty == tgt.ty) else None
    if isinstance(pat, Comb) and isinstance(tgt, Comb):
        s = _term_match(pat.fun, tgt.fun, vars_set, subst)
        if s is None: return None
        return _term_match(pat.arg, tgt.arg, vars_set, s)
    if isinstance(pat, Abs) and isinstance(tgt, Abs):
        if pat.bvar.name == tgt.bvar.name and pat.bvar.ty == tgt.bvar.ty:
            return _term_match(pat.body, tgt.body, vars_set, subst)
        return None
    return None


def _try_rules_at(rules, tm):
    """Try each rule at the root of tm.  Returns |- tm = tm' or None."""
    for vs, lhs, rhs, body in rules:
        subst = _term_match(lhs, tm, set(vs), {})
        if subst is None:
            continue
        pairs = [(subst[v], v) for v in vs if v in subst]
        return INST(pairs, body) if pairs else body
    return None


def _bottom_up(rules, tm):
    """One bottom-up pass: rewrite children once, then iterate rules at the root
       (without descending into the new RHS — that's what the outer fixpoint loop
       in REWRITE_CONV is for).  Returns |- tm = tm' or None if unchanged."""
    if isinstance(tm, Comb):
        l_step = _bottom_up(rules, tm.fun)
        r_step = _bottom_up(rules, tm.arg)
        if l_step is None and r_step is None:
            inner = REFL(tm)
            inner_changed = False
        else:
            l_eq = l_step if l_step is not None else REFL(tm.fun)
            r_eq = r_step if r_step is not None else REFL(tm.arg)
            inner = MK_COMB(l_eq, r_eq)
            inner_changed = True
    else:
        inner = REFL(tm)
        inner_changed = False

    # Iterate at root only — bounded to detect cyclic rule sets early.
    for _ in range(256):
        cur = rand(inner._concl)
        root_step = _try_rules_at(rules, cur)
        if root_step is None:
            break
        inner = TRANS(inner, root_step)
        inner_changed = True
    else:
        raise HolError("REWRITE: root rule fired 256 times — likely non-terminating")

    return inner if inner_changed else None


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------

def REWRITE_CONV(rules_thms, tm, max_passes=64):
    """Rewrite tm with the given equation theorems to fixpoint, bottom-up.
       Raises HolError if no fixpoint reached after max_passes outer passes
       (likely a non-terminating rule set)."""
    rules = [r for r in (_prepare_rule(t) for t in rules_thms) if r is not None]
    if not rules:
        return REFL(tm)
    th = REFL(tm)
    for _ in range(max_passes):
        cur = rand(th._concl)
        step = _bottom_up(rules, cur)
        if step is None:
            return th
        th = TRANS(th, step)
    raise HolError(f"REWRITE_CONV: did not reach fixpoint in {max_passes} passes "
                   "(rules likely non-terminating)")


def REWRITE_RULE(rules_thms, th):
    """Rewrite th's conclusion with the given equation theorems."""
    eq = REWRITE_CONV(rules_thms, th._concl)
    lhs, rhs = dest_eq(eq._concl)
    return th if aconv(lhs, rhs) else EQ_MP(eq, th)


def REWRITE_PROVE(rules_thms, target_eq):
    """Prove target_eq (= mk_eq(lhs, rhs)) by reducing both sides to a common
       normal form under the rewrite rules."""
    lhs, rhs = dest_eq(target_eq)
    eq_l = REWRITE_CONV(rules_thms, lhs)
    eq_r = REWRITE_CONV(rules_thms, rhs)
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if not aconv(nl, nr):
        raise HolError(
            "REWRITE_PROVE: normal forms differ\n"
            f"  LHS reduces to: {nl}\n"
            f"  RHS reduces to: {nr}"
        )
    return TRANS(eq_l, SYM(eq_r))
