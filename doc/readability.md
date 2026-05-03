# Readability of `nat.py` vs Grundlagen Chapter 1

Each Satz below cites Landau (`grundlagen-1.0/landau/1.tex`) on the left and
`nat.py` on the right. The order is roughly worst-offender-first: where the
gap between Landau's prose and the kernel-flavoured DSL is largest. Each
entry ends with a concrete syntax/tactic that would close the gap.

---

## 1. Inequation rewriting (Sätze 1, 7, 8) — ✅ shipped

**Landau:** chains `≠` like `=`. Satz 7 (1.tex:316–333):

```
1 ≠ x',
1 ≠ x + 1.
…
y' ≠ (x + y)',
y' ≠ x + y'.
```

The `x' = x+1` and `(x+y)' = x+y'` rewrites are silently absorbed into the
≠-chain. No bookkeeping.

**`nat.py` (before):** every rewrite on a `≠`-side had to be hand-fed:

```python
p.thus("~(1 = x + 1)")\
    .by_rewrite_ne("ne1", [REFL(ONE), SYM(SPEC(x, ADD_1))])
…
p.thus("~(SUC y = x + SUC y)")\
    .by_rewrite_ne("ne_succ",
                   [REFL(mk_suc(y)), SYM(SPECL([x, y], ADD_SUC))])
```

The `REFL(ONE)` and `REFL(mk_suc(y))` were no-op left-hand sides only there
because the (then-separate) `by_rewrite_ne` wanted two witnesses; the
`SYM(SPEC(...))` re-oriented `ADD_1` and `ADD_SUC` because the rewriter was
one-directional.

**Fix landed.** `~(=)` shapes are now handled by the unified two-sided
`by_rewrite_of` (see §5): the bottom-up rewriter descends through `~` and
`=` naturally, so source and target are normalized to a common form and
bridged via `EQ_MP`. The four call sites in `nat.py` (SATZ_7 base/step,
SATZ_8 base/step) are now one-liners:

```python
p.thus("~(1 = x + 1)").by_rewrite_of("ne1", [ADD_1])
p.thus("~(SUC y = x + SUC y)").by_rewrite_of("ne_succ", [ADD_SUC])
p.thus("~(1 + y = 1 + z)").by_rewrite_of("ne_suc", [ONE_PLUS])
p.thus("~(SUC x + y = SUC x + z)").by_rewrite_of("ne_sum", [SUC_PLUS])
```

---

## 2. Trichotomy-driven inversion (Sätze 20, 33) — ✅ shipped

**Landau:** Satz 20 is one sentence (1.tex:606–608):

> *Folgt aus Satz 19, da die drei Fälle beide Male sich ausschließen und
> alle Möglichkeiten erschöpfen.*

Satz 33 is the same template with multiplication.

**`nat.py` (before):** every inverse direction was its own ~13-line manual
proof opening `cases_on(SATZ_10, "x", "y")`, calling
`by_match(forward, ...)` and `absurd().auto(...)` per non-matching branch
and `by_thm(p.fact(...))` in the matching branch. ~80 lines across the
six theorems.

**Fix landed.** New `by_trichotomy_invert` tactic on `_Have`:

```python
.by_trichotomy_invert(trichotomy, comparands, source, *forwards)
```

specializes the trichotomy at `comparands`, splits its disjunction, and
for each disjunct: returns the case fact directly when it alpha-matches
the goal, else uses the corresponding `forward` to lift the case fact to
the source's shape and closes via the registered contra finder. The
forward's third forall (the lifting parameter `z`) is inferred by
matching the forward's consequent against the lifted shape derived from
`source`'s operands -- callers don't have to specialize.

The six call sites collapse to three lines each:

```python
p.thus("x > y").by_trichotomy_invert(
    SATZ_10, ["x", "y"], "h_a", SATZ_19B, SATZ_19A, SATZ_19C)
```

Forwards are listed in trichotomy disjunct order; the one matching the
goal is unused. The same template handles SATZ_20A/B/C (with SATZ_19A/B/C)
and SATZ_33A/B/C (with SATZ_32A/B/C). frac.py's SATZ_63 / SATZ_73 share
the shape but operate over 4-ary fraction relations with manual UNFOLD
bridges into num-level absurd; extending the tactic to those would
require unfolder-aware lifting and is left for a future pass.

---

## 3. CONTRA_LT_GT and friends — closure-CPS for `?u. …`

**Landau:** Satz 9 part A (1.tex:373–378):

```
x = y + u = (x + v) + u = x + (v + u) = (v + u) + x.
```

Five terms, four equalities, conclusion is `x = (v+u) + x` which contradicts
Satz 7. One line of math.

**`nat.py`:** `CONTRA_LT_GT` (758–771) needs nested closures because each
existential elimination is CPS:

```python
def CONTRA_LT_GT(a_t, b_t, h_lt, h_gt):
    def _inner_v(eq_v, v0):
        def _inner_u(eq_u, u0):
            rhs_eq = REWRITE_PROVE([eq_u, SATZ_5],
                          parse("${a} + ${v0} = ${b} + (${u0} + ${v0})", …))
            chain = TRANS(eq_v, rhs_eq)
            ne   = SPECL([mk_add(u0, v0), b_t], SATZ_7)
            ne_f = REWRITE_NE(ne, REFL(b_t), SPECL([mk_add(u0, v0), b_t], SATZ_6))
            return MP(NOT_ELIM(ne_f), chain)
        return CHOOSE_GT(h_gt, _inner_u)
    return CHOOSE_LT(h_lt, _inner_v)
```

Then this gets registered as a contra finder via `register_contra_finder`
so call sites can write `p.absurd().auto(h_lt, h_gt)`. The whole 70-line
block at 758–829 (three `CONTRA_*` + three `_contra_*` adapters + three
registrations) is plumbing for what Landau does in one equation chain.

**Fix.** A declarative `@proof` of Satz 9 part A that uses the existing
`p.choose` (which is the proof-DSL surface for ELIM_EX) instead of nested
CPS callbacks:

```python
@proof
def CONTRA_LT_GT_THM(p):
    p.goal("!a b. a < b /\\ a > b ==> F")
    p.fix("a b")
    p.assume("h: a < b /\\ a > b")
    p.split_conj("h", "h_lt", "h_gt")
    p.choose("v: b = a + v", from_="h_lt")
    p.choose("u: a = b + u", from_="h_gt")
    p.have("chain: b = b + (u + v)").by_rewrite_ac(["v_eq", "u_eq"], …)
    p.absurd().by_match(SATZ_7, "chain")  # b = (u+v) + b after one comm
```

Then `_contra_lt_gt` becomes `SPECL([a, b], CONTRA_LT_GT_THM)` and the
nested-closure trio collapses.

The deeper fix is making `p.choose` available as a free-standing kernel
combinator on raw theorems, not just inside `@proof` bodies. That would
also clean up `CHOOSE_GT`/`CHOOSE_LT` themselves (425–446).

---

## 4. SATZ_27 (well-ordering)

**Landau:** 1.tex:685–706, ~20 lines of running prose. Defines
`𝔐 := {x : x ≤ every n in 𝔑}` casually, observes 1 ∈ 𝔐 (Satz 24),
observes 𝔐 misses some x because y+1 ∉ 𝔐 for y ∈ 𝔑, applies Axiom 5
contrapositively to get a boundary m, and concludes m ∈ 𝔑 by
contradiction.

**`nat.py`:** 1029 → 1027 across **three sub-lemmas** plus the main proof:

- `_SATZ_27_NOT_M_SUCC` (878–891): "y ∈ 𝔑 ⟹ y+1 ∉ 𝔐" — 14 lines.
- `_SATZ_27_EXISTS_M` (903–941): the abstract Axiom-5-contrapositive
  kernel — 39 lines, includes a manual induction with an `ADD_1` ↔ `SUC`
  bridge (`SYM(SPEC(x, ADD_1))`) and two `EXCLUDED_MIDDLE` calls.
- `_SATZ_27_FROM_M` (951–982): the contradictory case for `m ∈ 𝔑` — 32
  lines, including manual `EXCLUDED_MIDDLE`.
- `SATZ_27` itself (992–1026): wires the three together via
  `p.let("M(x) := !n. N n ==> x <= n")` and `by_select`.

The three sub-lemmas are not really sub-lemmas in Landau's mind — they're
three sentences. The split exists to localise BETA bridges and
`by_select` plumbing.

**Pain points:**

1. **`p.let` / `by_select` for predicates** — Landau's "𝔐 is the set of
   …" is direct; `by_select` requires materialising the let-bound macro as
   a kernel lambda, BETA-normalising back, and MPing premises. The boundary
   between the let macro and the unfolded body is structural noise.

2. **Manual `ADD_1` / `SUC` bridge inside induction.** In
   `_SATZ_27_EXISTS_M` (931–932):
   ```python
   p.have("hnP1: ~ P (x + 1)")
       .by_rewrite_of("hnPS", [SYM(SPEC(x, ADD_1))])
   ```
   `induction` produces a `SUC x` step, but the predicate is in `+1` form.
   A user shouldn't have to choose; either form should work.

3. **`EXCLUDED_MIDDLE` manually invoked twice** for what Landau states as
   a contrapositive. A `p.by_contradiction("hnex: ~ goal"): …` block
   would absorb the `cases_on(EXCLUDED_MIDDLE, …)` ceremony.

**Fix.** Three separate ones:
- A `p.set("M(x) := …")` that auto-unfolds at every `M t` site without
  needing `by_select`.
- Make `induction` accept a predicate stated in either `SUC x` or `x + 1`
  form — internally normalize via `ADD_1`.
- A `p.by_contradiction("h: ~ goal")` block as sugar for the
  `cases_on(EXCLUDED_MIDDLE, goal)` + trivial branch + non-trivial branch
  pattern.

---

## 5. Equality substitution under an order op (Sätze 22, 35) — ✅ shipped

**Landau:** Satz 22 (1.tex:632–633): "*Mit dem Gleichheitszeichen in der
Voraussetzung durch Satz 19, sonst durch Satz 21 erledigt.*" One clause.

**`nat.py` (before):** SATZ_22A's equality branch built `|- y + z = x + z`
by hand using `AP_THM(AP_TERM(PLUS, SYM h), z)`; same pattern in SATZ_22B,
SATZ_35A, SATZ_35B.

```python
p.thus("x + z > y + u").by_rewrite_of(
    "yz_gt_yu",
    [AP_THM(AP_TERM(PLUS, SYM(p.fact("hxy"))), z)])
```

**Fix landed.** `by_rewrite_of` is now two-sided: it normalizes the source
fact's conclusion *and* the have-term under the supplied rules and bridges
the result via ``EQ_MP``. A plain equality fact ``hxy: x = y`` can be
supplied directly even when only one side of the bridge contains the
matchable subterm — the rewriter normalizes both ends and the over-
application cancels. The four manual surgical sites collapse to one-liners:

```python
p.thus("x + z > y + u").by_rewrite_of("yz_gt_yu", ["hxy"])
p.thus("x + z > y + u").by_rewrite_of("xz_gt_yz", ["hzu"])
p.thus("x * z > y * u").by_rewrite_of("yz_gt_yu", ["hxy"])
p.thus("x * z > y * u").by_rewrite_of("xz_gt_yz", ["hzu"])
```

The same upgrade also let several spots in SATZ_16A, SATZ_25, and the
SATZ_27 sub-lemmas drop their pre-orienting ``SYM(...)`` wrappers (the
forward orientation now rewrites the target side and meets the source in
the middle). `AP_THM` and `mk_comb` are no longer needed in `nat.py`.

---

## 6. RIGHT_DISTRIB and the SATZ_29 rewrite-loop

**Landau:** Satz 30 *Vorbemerkung* (1.tex:820–823):

> *Die aus Satz 30 und Satz 29 fließende Formel `(y+z)x = yx + zx` und
> ähnliche Analoga späterhin brauchen nicht besonders als Sätze formuliert
> oder auch nur aufgeschrieben zu werden.*

Effectively free.

**`nat.py`** (1153–1161):

```python
@proof
def RIGHT_DISTRIB(p):
    p.goal("!a b c. (a + b) * c = a * c + b * c")
    p.fix("a b c")
    p.have("flip: (a + b) * c = c * (a + b)").by_match(SATZ_29)
    p.have("dist: c * (a + b) = c * a + c * b").by_match(SATZ_30)
    p.have("ca: c * a = a * c").by_match(SATZ_29)
    p.have("cb: c * b = b * c").by_match(SATZ_29)
    p.thus("(a + b) * c = a * c + b * c")\
        .by_rewrite(["flip", "dist", "ca", "cb"])
```

The comment at 1149–1151 explains: *"Plain commutativity (SATZ_29) loops as
a free rewrite rule, so we name the four intermediate equations
explicitly."*

**Fix.** The AC machinery already handles `+` (via `SATZ_5`/`SATZ_6` —
e.g. `ADD_RIGHT_SWAP` at 262–265). It should equally handle `*` once
SATZ_29 + SATZ_31 are proved. With AC normalisation for `*`, RIGHT_DISTRIB
collapses to `.by_ac(TIMES, SATZ_31, SATZ_29) + .by_match(SATZ_30, …)`
or simply `by_rewrite_ac([SATZ_30], TIMES, SATZ_31, SATZ_29)`.

---

## 7. SATZ_26 — Landau uses contrapositive, nat.py uses trichotomy

**Landau** (1.tex:677–680):

```
Sonst wäre y > x, also nach Satz 25 y ≥ x + 1.
```

Two-line contrapositive of Satz 25.

**`nat.py`** SATZ_26 (838–853): forward proof via SATZ_10 (trichotomy),
splits three ways, the `y > x` branch invokes SATZ_25 then case-splits the
resulting `y ≥ x+1` into `>` and `=` and `absurd`s both. 16 lines.

**Fix.** A `p.by_contrapositive(SATZ_25, "h: y < x + 1")` tactic that
takes a target `~A ==> ~B` and discharges via the forward `B ==> A`.
Combined with the `~(y ≤ x) <=> y > x` rewrite (which doesn't exist as a
named lemma), SATZ_26 becomes ~3 lines.

---

## 8. LEMMA_PRED — needed only because `induction` can't pattern-split

**Landau:** Satz 9 base case (1.tex:383–387):

> *Für y = 1 ist nach Satz 3 entweder `x = 1 = y` (Fall 1) oder
> `x = u' = 1 + u = y + u` (Fall 2).*

Just inlines Satz 3.

**`nat.py`:** `LEMMA_PRED` (326–336) exists purely to repackage Satz 3 as
a clean disjunction `(x = 1) \/ (?u. x = SUC u)` so `cases_on` can
consume it. Then SATZ_9 uses it twice (355, 372).

**Fix.** A `p.cases_on_pred(x)` tactic that internally uses Satz 3 to
split `x` into `1` vs `SUC u` cases (and binds `u` automatically) —
exactly what Landau's prose does at sight.

---

## 9. ADD_UNIQUE / MUL_UNIQUE assume+split ceremony

**Landau:** the uniqueness halves of Satz 4 / Satz 28 (1.tex:208–233 and
730–753) state the four hypotheses inline with set-builder prose
("a₁ = x', b₁ = x', a_y' = (a_y)', b_y' = (b_y)'") and proceed.

**`nat.py`** (177–192, 1061–1075):

```python
p.assume("h: f 1 = SUC x /\\ (!y. f (SUC y) = SUC (f y)) /\\ "
            "g 1 = SUC x /\\ (!y. g (SUC y) = SUC (g y))")
p.split_conj("h", "h_f1", "h_fstep", "h_g1", "h_gstep")
```

The conjunction shape comes from `define_recursive`'s output spec, which
is one statement; the split is purely syntactic.

**Fix.** Allow `p.assume("h_f1: f 1 = SUC x", "h_fstep: …", "h_g1: …",
"h_gstep: …")` to consume an `/\\`-conjunction and bind each conjunct in
order. Today's multi-arg `p.assume` only handles `==>` chains.

---

## Summary of fixes worth landing

Ranked by impact (LOC saved across §2 of nat.py, plus how many proofs
benefit):

1. **Inequality-aware rewriting** (§1) — ✅ shipped.
2. **Order-aware rewriting** (§5) — ✅ shipped.
3. **`by_trichotomy_invert` tactic** (§2) — ✅ shipped.
4. **AC support for `*`** (§6) — RIGHT_DISTRIB shrinks; SUC_MUL becomes
   shorter; downstream multiplication AC chains stop needing ad-hoc
   commutativity rewrites.
5. **`p.choose` on free-standing theorems** (§3) — collapses
   CONTRA_LT_GT/EQ/_GT_EQ from 70 lines of nested CPS to ~30 lines of
   declarative proof, removes `register_contra_finder` plumbing.
6. **`p.set` / auto-unfolding predicate macro** (§4) — flattens SATZ_27.
7. **`p.cases_on_pred`** (§8) — kills LEMMA_PRED.
8. **`p.by_contrapositive`** (§7) — restores Landau's actual SATZ_26.
9. **Conjunctive `p.assume`** (§9) — minor but pervasive.

The first four would do the most: they hit the proofs whose Landau
versions are one-liners but whose nat.py versions are 10–30 lines, and
they're local DSL changes rather than new proof modes.
