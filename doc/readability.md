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

**Fix landed.** New `_Absurd.via(forward, case, source=...)` primitive:

```python
with p.cases_on(SATZ_10, "x", "y"):
    with p.case("h_eq: x = y"):
        p.absurd().via(SATZ_19B, "h_eq", source="h_a")
    with p.case("h_gt: x > y"):
        p.thus("x > y").by_thm(p.fact("h_gt"))
    with p.case("h_lt: x < y"):
        p.absurd().via(SATZ_19C, "h_lt", source="h_a")
```

`via` does one job: specialize `forward` so its consequent matches a
shape derived from `source`'s operands and `case`'s relation, MP with
`case`, then close as if `auto(source, lifted)` had been called. The
forward's foralls are inferred via `_term_match` on antecedent ↔ case
and consequent ↔ ``op_case(L, R)``. Callers never specialize manually.

Each non-matching `case` body collapses from a two-line
``by_match(...)``/``absurd().auto(...)`` ritual to one ``via(...)``
line. The matching case stays explicit (``thus(...).by_thm(...)``) so
the structure of the case-split remains visible.

`via` lives on ``_Absurd`` rather than as a trichotomy-specific tactic,
so it composes with anything ``cases_on`` supports (let-bound
predicates, registered disj-unfolders, custom disjunctions) and any
number of cases. frac.py's SATZ_63 / SATZ_73 will be able to use it
once contra finders are registered for fraction relations -- the 4-arity
issue dissolves because there's no auto-detection of disjunct shape.

---

## 3. CONTRA_LT_GT and friends — closure-CPS for `?u. …` — ✅ shipped

**Landau:** Satz 9 part A (1.tex:373–378):

```
x = y + u = (x + v) + u = x + (v + u) = (v + u) + x.
```

Five terms, four equalities, conclusion is `x = (v+u) + x` which contradicts
Satz 7. One line of math.

**`nat.py` (before):** `CONTRA_LT_GT`, `CONTRA_LT_EQ`, `CONTRA_GT_EQ` were
each kernel-level helpers using `CHOOSE_LT`/`CHOOSE_GT` (a CPS
``ELIM_EX`` wrapper) with nested closures per existential. The whole
~70-line block was plumbing for what Landau does in one equation chain.

**Fix landed.** Three declarative `@proof` theorems
(`_CONTRA_LT_GT`, `_CONTRA_LT_EQ`, `_CONTRA_GT_EQ`) use `p.choose` and
`p.absurd().by_conj` instead of nested CPS callbacks. The contra-finder
adapters (`_contra_lt_gt`, etc.) are now thin one-liners that ``SPECL``
the matching theorem at the operands and ``MP`` in the two hypotheses.

A new helper `SATZ_7_RIGHT` (`!x y. ~(y = y + x)`) avoids per-call-site
``SPECL`` of `SATZ_6` to commute the addend; every contradiction chain
in the three `_CONTRA_*` proofs ends with `b = b + (...)` and contradicts
`SATZ_7_RIGHT` directly via `by_match`. The CPS combinators `CHOOSE_LT`
and `CHOOSE_GT` are removed (no other callers).

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
   would absorb the `cases_on(EXCLUDED_MIDDLE, …)` ceremony. ✅ shipped.

**Fix.** Three separate ones:
- A `p.set("M(x) := …")` that auto-unfolds at every `M t` site without
  needing `by_select`.
- Make `induction` accept a predicate stated in either `SUC x` or `x + 1`
  form — internally normalize via `ADD_1`.
- A `p.by_contradiction("h: ~ goal")` block as sugar for the
  `cases_on(EXCLUDED_MIDDLE, goal)` + trivial branch + non-trivial branch
  pattern. ✅ shipped: lives on `_Have`, so both
  `p.thus(target).by_contradiction("hnex"):` and
  `p.have("Nm: N m").by_contradiction("hnN"):` work; the body opens with
  goal `F` and `~target` registered as a fact, and on close
  `NOT_NOT_ELIM` lifts to the original target. The two SATZ_27
  sub-lemma sites collapsed by 6 lines and one nesting level each.

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

## 6. RIGHT_DISTRIB and the SATZ_29 rewrite-loop — ✅ shipped

**Landau:** Satz 30 *Vorbemerkung* (1.tex:820–823):

> *Die aus Satz 30 und Satz 29 fließende Formel `(y+z)x = yx + zx` und
> ähnliche Analoga späterhin brauchen nicht besonders als Sätze formuliert
> oder auch nur aufgeschrieben zu werden.*

Effectively free.

**`nat.py` (before):**

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

Plain commutativity (SATZ_29) loops as a free rewrite rule, so the four
intermediate equations had to be named explicitly.

**Fix landed.** The bottom-up rewriter now accepts ``ac=(op, assoc, comm)``
and AC-normalizes every ``op``-application it visits *during* traversal,
not just at the top after both sides finish reducing. SATZ_30
(``x*(y+z) = x*y + x*z``) fires regardless of which side carries the sum
because the ``*``-tree is canonicalised at every node. RIGHT_DISTRIB
collapses to one line:

```python
p.thus("(a + b) * c = a * c + b * c")\
    .by_rewrite([SATZ_30], ac=(TIMES, SATZ_31, SATZ_29))
```

``by_rewrite_of`` gained the same ``ac=`` parameter; downstream
multiplication AC chains in SATZ_34, SATZ_35A, frac.py SATZ_44 and
SATZ_50 collapsed their ``SPECL([_, _], SATZ_29)``-style commutativity
rewrites and ``AC_PROVE``-built bridges to one ``ac=(TIMES, SATZ_31,
SATZ_29)`` parameter.

---

## 7. SATZ_26 — Landau uses contrapositive, nat.py uses trichotomy — ✅ shipped

**Landau** (1.tex:677–680):

```
Sonst wäre y > x, also nach Satz 25 y ≥ x + 1.
```

Two-line contrapositive of Satz 25.

**`nat.py` (before):** SATZ_26 was a forward proof via SATZ_10 (trichotomy)
that split three ways; the `y > x` branch invoked SATZ_25 and then
case-split the resulting `y ≥ x+1` into `>` and `=` and `absurd`d both.
16 lines.

**Fix landed.** Two small additions reinstate Landau's "Sonst wäre …"
move without a dedicated `by_contrapositive` tactic:

- `NOT_LE: !x y. ~(x <= y) ==> x > y` — a one-shot inversion via
  `cases_on(SATZ_10)`. Lifts a negated `<=` hypothesis to a strict `>`.
- A `(<, >=)` contra finder (`_CONTRA_LT_GE`) that defers to the existing
  `_CONTRA_LT_GT` / `_CONTRA_LT_EQ` lemmas after splitting the `>=`.
  Lets `absurd().auto` close `y < x + 1` against `y >= x + 1` directly.

SATZ_26 then collapses into the existing `by_contradiction` block (§4):

```python
p.assume("h: y < x + 1")
with p.thus("y <= x").by_contradiction("hn"):
    p.have("y_gt: y > x").by_match(NOT_LE, "hn")
    p.have("y_ge: y >= x + 1").by_match(SATZ_25, "y_gt")
    p.absurd().auto("h", "y_ge")
```

The body is three lines that mirror Landau's prose: negate the goal, lift
to `y > x`, hit Satz 25, contradict `h`. No new dedicated tactic was
needed — the proposed `by_contrapositive` would have required matching
`~(y ≤ x) ⇔ y > x` and `y < x + 1 ⇔ ~(y ≥ x + 1)` rewrites it doesn't
have, so we kept the contradiction explicit and added the two missing
primitives instead.

---

## 9. ADD_UNIQUE / MUL_UNIQUE assume+split ceremony — ✅ shipped

**Landau:** the uniqueness halves of Satz 4 / Satz 28 (1.tex:208–233 and
730–753) state the four hypotheses inline with set-builder prose
("a₁ = x', b₁ = x', a_y' = (a_y)', b_y' = (b_y)'") and proceed.

**`nat.py` (before):**

```python
p.assume("h: f 1 = SUC x /\\ (!y. f (SUC y) = SUC (f y)) /\\ "
            "g 1 = SUC x /\\ (!y. g (SUC y) = SUC (g y))")
p.split_conj("h", "h_f1", "h_fstep", "h_g1", "h_gstep")
```

The conjunction shape comes from `define_recursive`'s output spec, which
is one statement; the split is purely syntactic.

**Fix landed.** ``p.assume`` now auto-detects when its multi-arg
invocation describes a conjunction split rather than an ``==>``-chain:
when the goal antecedent is an N-ary right-associated ``/\\`` whose
conjuncts each alpha-match the user-supplied terms, the single ``==>``
is consumed once and ``CONJUNCT1`` / ``CONJUNCT2`` register each
conjunct as its own fact. The two ``ADD_UNIQUE`` / ``MUL_UNIQUE`` sites
collapse the assume + ``split_conj`` pair to a single ``p.assume`` call:

```python
p.assume("h_f1: f 1 = SUC x",
         "h_fstep: !y. f (SUC y) = SUC (f y)",
         "h_g1: g 1 = SUC x",
         "h_gstep: !y. g (SUC y) = SUC (g y)")
```

The ``==>``-chain semantics is preserved when the antecedent isn't a
matching conjunction, so existing call sites are unaffected.

---

## Summary of fixes worth landing

Ranked by impact (LOC saved across §2 of nat.py, plus how many proofs
benefit):

1. **Inequality-aware rewriting** (§1) — ✅ shipped.
2. **Order-aware rewriting** (§5) — ✅ shipped.
3. **`by_trichotomy_invert` tactic** (§2) — ✅ shipped (later swapped for
   the smaller `_Absurd.via` primitive).
4. **CONTRA closure-CPS** (§3) — ✅ shipped.
4. **AC support for `*`** (§6) — ✅ shipped.
5. **`p.choose` on free-standing theorems** (§3) — collapses
   CONTRA_LT_GT/EQ/_GT_EQ from 70 lines of nested CPS to ~30 lines of
   declarative proof, removes `register_contra_finder` plumbing.
6. **`p.set` / auto-unfolding predicate macro** (§4) — flattens SATZ_27.
8. **`NOT_LE` + `(<, >=)` contra finder** (§7) — ✅ shipped.
9. **Conjunctive `p.assume`** (§9) — ✅ shipped.

The first four would do the most: they hit the proofs whose Landau
versions are one-liners but whose nat.py versions are 10–30 lines, and
they're local DSL changes rather than new proof modes.
