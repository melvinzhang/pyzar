# `by` Variants: Forward → Backward → Auto

Catalogue of `_Have.by*` justification styles, ordered by how much the user
states explicitly. Each step trades predictability for less typing.

**Status legend:** ✅ implemented · 🟡 sketched · ⏳ not started

| # | Status | Form | Inference |
|---|--------|------|-----------|
| 1 | ✅ | `by` | none |
| 2 | ✅ | `by_match` (concl-only) | match conclusion against goal |
| 3 | ✅ | `by_match` (+ antecedents) | match conclusion *and* each antecedent against fact concl |
| 4 | ⏳ | order-free fact resolution | bipartite assignment of facts to antecedents |
| 5 | ⏳ | scope auto-discharge | search in-scope facts for antecedents |
| 6 | ⏳ | proof search (`auto`/hammer) | bounded resolution over hint set + scope |

---

## 1. `by` — pure forward chain

User supplies every SPEC and MP arg. No inference; the goal term is not
consulted to derive instantiations — `_finish` only checks the result.

```python
.by(SATZ_15, "x", "y", "z", "hxy", "hyz")
```

Implementation: `proof.py:1194` `_Have.by`. Walks `args` left-to-right;
term arg → `SPEC`, theorem arg → `simp_mp`.

## 2–3. `by_match` — match conclusion *and* antecedents

Strip the justification's outer `∀`s, peel `==>` antecedents one at a
time until the residual matches the goal. Then walk the call's
positional args under one shared substitution:

- a **fact arg** (label / negative index / theorem) is matched against
  the next peeled antecedent's pattern, then queued for MP;
- a **term arg** (string / kernel term) is assigned to the next
  still-unbound forall var.

```python
.by_match(SATZ_1, "IH")                    # foralls fully pinned by goal
.by_match(SATZ_15, "hxy", "hyz")           # y inferred from hxy's type
.by_match(SATZ_15, "y", "hxy", "hyz")      # explicit middle var still works
```

Step-by-step on `SATZ_15 = ∀x y z. x < y ==> y < z ==> x < z`, goal
`x < z`, args `("hxy", "hyz")`:

1. Match conclusion `x < z` against goal → `{x↦x, z↦z}`, `y` unbound.
2. Walk args:
   - `hxy`: match peeled antecedent `x < y` against `hxy._concl` →
     extends subst with `y`.
   - `hyz`: match `y < z` against `hyz._concl` → consistent.
3. Check completeness (no unbound vars, every peeled antecedent has a
   fact).
4. SPEC every forall, then `simp_mp` each fact in order.

Fact order matters at this step (3): `("hyz", "hxy")` fails because
`hyz._concl = y < z` does not match the first antecedent pattern
`x <= y`. Step 4 below relaxes this.

Implementation: `proof.py` `_Have.by_match`. Reuses
`tactics._term_match` (first-order matcher with alpha-aware `Abs`
handling) and `_strip_forall`.

## 4. Order-free fact resolution

Facts in any order; matcher picks which fact discharges which antecedent.

```python
.by_match(SATZ_15, "hyz", "hxy")           # same result as step 3
```

Implementation: bipartite matching between antecedent patterns and
supplied facts under one shared subst. Backtracking on ambiguity. Greedy
"match most-constrained antecedent first" works for almost all
single-conclusion lemmas; full backtracking only needed on duplicate
antecedent shapes.

## 5. Scope auto-discharge

Antecedents auto-discharged from in-scope facts when a unique match
exists.

```python
.by(SATZ_15)                               # finds hxy, hyz in scope
```

Equivalent to HOL-Light's `RESOLVE_TAC` / Lean's `apply ... <;>
assumption`. Cheap when matching nails down each pattern; thorny when
multiple in-scope facts could fit (silent wrong pick is worse than
failure).

## 6. Proof search

User names neither facts nor lemma. Bounded resolution over a hint set
plus the local context.

```python
.auto(hints=[SATZ_15])
```

Real prover territory: term ordering, fairness, indexing, timeouts.
Order-of-magnitude more code; failure modes get harder to debug.

---

## External libraries

Scanned for code we could lift instead of writing in-tree.

**General-purpose unification**

- `unification` (Matt Rocklin) — first-order, MIT, ~few hundred LOC.
  Operates on Python tuples/dicts via `~` logic vars. Bridging to your
  `Var/Const/Comb/Abs` plus re-handling `Abs` alpha-renaming is more code
  than writing the match directly.
- `kanren` / `logpy` — relational programming on top of `unification`.
  Same converter problem; heavier API.
- `pampy`, `multipledispatch.conflict` — pattern matching for dispatch,
  not term unification.

**Symbolic math**

- `sympy.unify` — first-order matching with AC awareness. Tightly coupled
  to SymPy's expression tree; pulling SymPy in for a matcher is a poor
  trade.

**Theorem-prover backends**

- `z3-solver`, `pysmt` — SMT. Heavy dep, opaque, would need proof
  reconstruction. Useful only at step 6.
- `pyres` (Schulz, educational), Vampire/E/prover9 via subprocess — full
  first-order ATPs. Only fit if going all the way to a hammer.

**Higher-order / Miller-pattern unification** — no maintained Python lib
worth trusting. Lean/Coq/Isabelle implement their own in OCaml/SML.

---

## Recommendation

Stay in-tree. The kernel's `_term_match` (`tactics.py:662`, 33 LOC,
alpha-aware) is already doing the heart of steps 2–4. Adding steps 3 + 4
is ~50 LOC total; bringing in `unification` + `kanren` would be more code
plus a dependency, with no gain in capability or trust.

Stop at **steps 3 + 4**: single-pass first-order matching against
`(goal, supplied_facts)` with multiset assignment of facts to
antecedents, no scope auto-discharge. This handles ~95% of nat.py-style
call sites and stays predictable — explicit fact lists keep proofs
grep-able and stable across edits.

Skip step 5 unless and until silent-wrong-pick risk is shown to be low
in practice. Step 6 is a separate project (sledgehammer-style), worth
considering only if proof maintenance burden outgrows manual
fact-listing.

**Soundness note.** The matcher's output is consumed only by `SPEC` and
`simp_mp`, and `_finish` aconv-checks the result against `self.term`. A
buggy or external matcher can cause spurious *failure* but cannot
produce an unsound theorem — the fusion kernel remains the trust
boundary regardless of which matcher feeds it.

---

## Higher-order axioms

A separate axis from the ladder above: how to apply axioms whose forall
binds a *predicate* variable (`!P. ... P t ...`).  First-order matching
can't infer `P`; you need either Miller-pattern unification or an
explicit predicate.  Three options, with how they map onto pyzar:

### Option A: Miller-pattern unification

Decidable HO unification when each HO var appears only as `F x₁ ... xₙ`
with the `xᵢ` distinct bound vars.  Solves `?P x ≡ φ(x)` to
`P := λx. φ(x)` automatically.

Cost: ~150–300 LOC plus tests for alpha/beta/eta interactions; subtle
edge-case failures (pattern-condition violations) produce confusing
errors.  No maintained Python library — Coq/Lean/Isabelle implement
their own.

### Option B: explicit HO arg in `by_match`

User writes the lambda inline: `by_match(AXIOM, ("P", "λx. φ x"), ...)`.
~10 LOC, no unifier needed, binder visible in proofs.

### Option C: `let` + `by_select` (current)

Predicate gets a surface name via `p.let("P(x) := body")`; `by_select`
SPECs the HO axiom at the let's carrier `Var`.  The let participates in
pretty-printing and fact references throughout the proof.

### Audit of HO call sites in pyzar

| Site | Predicate | Reuse |
|------|-----------|-------|
| `num.py:451` `by_select(NR_da_unfold, "Q", ...)` | `Q i := NUM_REP i ∧ P (mk_num i)` | used in `Q_1`, `Q_step` |
| `num.py:640,642,725,727` `by_select(..., "Qp", ...)` | recursion-uniqueness auxiliary | reused across cases |
| `nat.py:1015` `by_select(_SATZ_27_EXISTS_M, "M", ...)` | `M(x) := ∀n. N n ⇒ x ≤ n` | referenced as `M 1`, `M (y+1)`, `M m` |
| `INDUCTION` (num.py:411) | `!P. P 1 ∧ ... ⇒ !x. P x` | wrapped by `p.induction(...)` |
| `NUM_RECURSION` | HO recursion principle | wrapped by `define_recursive` |

**Every HO site falls into one of two patterns:**

1. **Standardised framework axiom** (induction, primrec) — wrapped in
   purpose-built code (`INDUCT`, `define_recursive`, `p.induction`).
   The wrapper synthesises the predicate from the user's goal once, in
   lemma-specific code.  This is hand-rolled Miller inference for one
   axiom — exactly the right factoring.
2. **Ad-hoc reused predicate** — `let` + `by_select`.  The predicate is
   *named* and used multiple times; the name does real work in
   pretty-printing and in fact references like `M 1` / `Q_step`.

**Zero one-shot HO instantiations exist in the current codebase.**  That's
the gap where Option B would help, and it's empty.

### Recommendation: don't add Miller or explicit-HO

The current factoring is already optimal for this codebase:

- Standardised HO axioms → specialised wrappers (fully automatic, no
  user-written lambdas).
- Ad-hoc reused predicates → `let` + `by_select` (named, visible,
  shareable across proof steps).

Generic Miller would replace `by_select` with anonymous λs — a
**regression** in readability, since the current scripts mention `M 1`
and `Q (IND_SUC i)` symbolically.  Generic explicit-HO would only beat
`let` for one-shot uses, of which there are none.

The honest version: Miller-pattern unification matters for codebases
with many one-shot HO instantiations (generic substitutivity, congruence,
`f_equal` chains in tactic libraries).  Pyzar is a Landau port — each
step is hand-stated and predicates are deliberate, named pieces of
structure.  The match is wrong.
