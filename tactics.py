"""Higher-level tactics built on the kernel + logic.py.

Public API:
  REWRITE_CONV(rules, tm)   -- |- tm = tm', rewriting tm with the given
                               equation theorems to fixpoint, bottom-up.
  REWRITE_RULE(rules, th)   -- rewrite th's conclusion.
  REWRITE_PROVE(rules, eq)  -- prove an equation `lhs = rhs` by reducing both
                               sides to a common normal form.
  AC_NORM(op_const, assoc_thm, comm_thm, tm)
                            -- |- tm = canonical(tm) under associativity +
                               commutativity of op_const.  assoc_thm must be
                               of the form  |- !x y z. op (op x y) z = op x (op y z)
                               and comm_thm  |- !x y. op x y = op y x.
  AC_PROVE(op_const, assoc_thm, comm_thm, target_eq)
                            -- prove `lhs = rhs` by reducing both sides under AC
                               and checking syntactic equality of the canonicals.

A "rule" is any theorem of the form  |- !v1...vn. lhs = rhs  (outer foralls
are stripped; the freed vars become pattern variables).  Theorems with no
outer forall are usable too: their free vars act as literal pattern atoms,
which lets you pass an induction hypothesis as a rewrite directly.

First-order matching only.  Lambdas in patterns must alpha-match exactly.
"""

from fusion import (
    Var, Const, Comb, Abs,
    type_of, dest_eq, rand, aconv, mk_comb, HolError,
    REFL, TRANS, MK_COMB, EQ_MP, INST,
)
from logic import SPEC, SYM, AP_TERM, AP_THM, TRANS_CHAIN


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


# ---------------------------------------------------------------------------
# AC normalization: flatten an AC operator, canonical-sort the leaves, emit
# a kernel proof showing the original equals the sorted form.
# ---------------------------------------------------------------------------

def _term_key(tm):
    """Stable structural ordering on terms (used to canonical-sort AC leaves)."""
    if isinstance(tm, Var):
        return (0, tm.name, str(tm.ty))
    if isinstance(tm, Const):
        return (1, tm.name, str(tm.ty))
    if isinstance(tm, Comb):
        return (2, _term_key(tm.fun), _term_key(tm.arg))
    if isinstance(tm, Abs):
        return (3, tm.bvar.name, str(tm.bvar.ty), _term_key(tm.body))
    return (4, str(tm))


def _is_op_app(op_const, tm):
    """True iff tm = op a b for the given op_const."""
    return (isinstance(tm, Comb) and isinstance(tm.fun, Comb)
            and tm.fun.fun == op_const)


def _right_assoc_conv(op_const, assoc_thm, tm):
    """ |- tm = right_assoc(tm).   Repeatedly applies assoc_thm L→R at the root
        whenever the LHS of the root op is itself an op-application."""
    if not _is_op_app(op_const, tm):
        return REFL(tm)
    left, right = tm.fun.arg, tm.arg
    if not _is_op_app(op_const, left):
        # Just right-associate the right side.
        return AP_TERM(mk_comb(op_const, left),
                       _right_assoc_conv(op_const, assoc_thm, right))
    a, b = left.fun.arg, left.arg
    step = SPEC(right, SPEC(b, SPEC(a, assoc_thm)))   # (a*b)*right = a*(b*right)
    return TRANS(step, _right_assoc_conv(op_const, assoc_thm, rand(step._concl)))


def _flatten_right_assoc(op_const, tm):
    """List of leaves of a right-associated op-tree, in left-to-right order."""
    leaves = []
    while _is_op_app(op_const, tm):
        leaves.append(tm.fun.arg)
        tm = tm.arg
    leaves.append(tm)
    return leaves


def _build_right_assoc(op_const, leaves):
    """Build right-associated op-tree from a non-empty list of leaves."""
    result = leaves[-1]
    for leaf in reversed(leaves[:-1]):
        result = mk_comb(mk_comb(op_const, leaf), result)
    return result


def _swap_at(op_const, assoc_thm, comm_thm, leaves, idx):
    """ |- right_assoc(leaves) = right_assoc(swap(leaves, idx, idx+1)).
        Swap is purely on the inner two leaves; outer wrapping handled via AP_TERM."""
    a, b = leaves[idx], leaves[idx + 1]
    rest = leaves[idx + 2:]
    if not rest:
        # Bottom case: just (a op b) -> (b op a).
        swap_eq = SPEC(b, SPEC(a, comm_thm))
    else:
        rest_term = _build_right_assoc(op_const, rest)
        # a*(b*rest) = (a*b)*rest = (b*a)*rest = b*(a*rest)
        swap_eq = TRANS_CHAIN([
            SYM(SPEC(rest_term, SPEC(b, SPEC(a, assoc_thm)))),
            AP_THM(AP_TERM(op_const, SPEC(b, SPEC(a, comm_thm))), rest_term),
            SPEC(rest_term, SPEC(a, SPEC(b, assoc_thm))),
        ])
    # Wrap with prefix leaves[:idx] (each layer adds an `l +` on both sides).
    for leaf in reversed(leaves[:idx]):
        swap_eq = AP_TERM(mk_comb(op_const, leaf), swap_eq)
    return swap_eq


def _selection_sort_proof(op_const, assoc_thm, comm_thm, leaves):
    """ |- right_assoc(leaves) = right_assoc(sorted_leaves).
        Selection sort over the list, emitting one swap chain per move."""
    cur = list(leaves)
    eq = REFL(_build_right_assoc(op_const, cur))
    n = len(cur)
    for i in range(n - 1):
        # Find min in cur[i:].
        min_idx = i
        for j in range(i + 1, n):
            if _term_key(cur[j]) < _term_key(cur[min_idx]):
                min_idx = j
        # Bubble cur[min_idx] up to position i.
        while min_idx > i:
            eq = TRANS(eq, _swap_at(op_const, assoc_thm, comm_thm, cur, min_idx - 1))
            cur[min_idx - 1], cur[min_idx] = cur[min_idx], cur[min_idx - 1]
            min_idx -= 1
    return eq


def AC_NORM(op_const, assoc_thm, comm_thm, tm):
    """Returns |- tm = canonical(tm) under AC of op_const.
       assoc_thm: |- !x y z. op (op x y) z = op x (op y z)
       comm_thm:  |- !x y. op x y = op y x"""
    eq1 = _right_assoc_conv(op_const, assoc_thm, tm)
    rhs1 = rand(eq1._concl)
    leaves = _flatten_right_assoc(op_const, rhs1)
    if len(leaves) <= 1:
        return eq1
    eq2 = _selection_sort_proof(op_const, assoc_thm, comm_thm, leaves)
    return TRANS(eq1, eq2)


def AC_PROVE(op_const, assoc_thm, comm_thm, target_eq):
    """Prove `lhs = rhs` by AC-normalizing both sides under op_const."""
    lhs, rhs = dest_eq(target_eq)
    eq_l = AC_NORM(op_const, assoc_thm, comm_thm, lhs)
    eq_r = AC_NORM(op_const, assoc_thm, comm_thm, rhs)
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if not aconv(nl, nr):
        raise HolError(
            "AC_PROVE: AC normal forms differ\n"
            f"  LHS canonical: {nl}\n"
            f"  RHS canonical: {nr}"
        )
    return TRANS(eq_l, SYM(eq_r))


def REWRITE_AC_PROVE(rules, op_const, assoc_thm, comm_thm, target_eq, *, ac_rules=()):
    """Combined: reduce both sides under `rules`, optionally a second pass with
       `ac_rules` (e.g. SUC→+1 to canonicalize before AC), then close with AC.
       Falls back to TRANS+SYM if normal forms already match exactly."""
    from fusion import mk_eq as _mk_eq
    lhs, rhs = dest_eq(target_eq)
    eq_l = REWRITE_CONV(rules, lhs)
    eq_r = REWRITE_CONV(rules, rhs)
    if ac_rules:
        eq_l = TRANS(eq_l, REWRITE_CONV(ac_rules, rand(eq_l._concl)))
        eq_r = TRANS(eq_r, REWRITE_CONV(ac_rules, rand(eq_r._concl)))
    nl, nr = rand(eq_l._concl), rand(eq_r._concl)
    if aconv(nl, nr):
        return TRANS(eq_l, SYM(eq_r))
    eq_ac = AC_PROVE(op_const, assoc_thm, comm_thm, _mk_eq(nl, nr))
    return TRANS(eq_l, TRANS(eq_ac, SYM(eq_r)))
