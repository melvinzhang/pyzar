## Footguns and gotchas

Things that compile but don't do what they look like, or that surprise
on first encounter. Listed roughly in order of how often they bite.

### `assume` patterns require explicit destructure syntax

```python
p.assume("h1: A", "h2: B")                # chain: A ==> B ==> C
p.assume("(h1, h2): A /\\ B")             # split: (A /\\ B) ==> C
```

Each top-level spec consumes one `==>`. To split a conjunction
antecedent into multiple facts, you must use the tuple pattern
syntax. There is no auto-split based on goal shape — the call site
unambiguously names its destructure. Mode confusion is a parse
error, not a silent reinterpretation.

If you forget the parens (`p.assume("h1: A", "h2: B")` against
`(A /\ B) ==> C`), you'll get "goal is not an implication" on the
second spec — chain mode tried to peel a second `==>` from `C`. The
fix is the tuple form.

### `fix` requires exact name match

`fix("x")` against `!a. ...` raises. There is no auto-rename. If
you're porting between proofs that use different binder names, you
must edit either the goal string or the `fix` call — and you can't
just pick a fresh name to avoid an outer-scope collision.

### `step` requires a label, `base` does not

```python
with p.base(): ...        # no label
with p.step("IH"): ...    # label required, no default
```

This asymmetry is deliberate (so nested inductions don't collide on a
shared default IH name) but is easy to forget when copy-pasting.

### Auto-choose in `case` is silent

When a `cases_on` leaf is `?v. body`, the case body gets `v` and
`v_eq` registered automatically — even if you wanted to call them
something else. Rename via the spec bvar (`with p.case("h: ?w.
body"): ...`); otherwise you'll get name collisions if the outer
scope already has `v` or `v_eq`.

### `coerce` resolves strings as labels first, terms second

If a fact named `"x"` exists, `p.coerce("x", accept_term=True)`
returns the *theorem*, not the parsed variable `x`. The
namespace-clash protection only fires across the four kernel-value
namespaces (facts, lazy-let carriers, choose witnesses, fix-vars), so
nothing prevents a fact label from shadowing a freshly-needed term
name. **Workaround**: avoid single-letter fact labels; reserve them
for variables.

### `disj` with no rules requires a tautological leaf

`p.disj()` with empty rules collapses to `REFL`. If no leaf is a
syntactic tautology, you'll get "no leaf discharged" — the simp set
*is* consulted as the default rule list, but the active simp rules
must be enough to rewrite some leaf to `T` on their own.

### `by_match` requires *every* forall to be determined

If your lemma has a forall whose binding is not pinned down by the
goal *or* any supplied fact, `by_match` raises "forall vars not
determined". You can't supply a "hint" for one forall and let the
others be inferred — once you supply a term arg, you're consuming the
next still-unbound forall in declaration order. **Workaround**:
`by(lemma, "x", "y", "h1", "h2")` makes the SPEC/MP order explicit.

### `_unfold_walk` falls back to `REFL` under binders

If a lazy-let body contains a free variable that conflicts with a
binder in the term being normalized, `simp_normalize` returns no
progress at that node (`REFL`) instead of raising — to keep
under-binder rewriting tolerant. The downstream `aconv` check then
fails with a generic shape mismatch. The let was registered
correctly; the simp pass just couldn't lift the rewrite under the
binder. **Workaround**: `materialize_let` to expose the lambda shape
when you need the body to literally appear.

### Lazy-let discharge order matters

Lazy lets are discharged in *reverse* registration order on frame
close: a later let's body may reference an earlier carrier, so
discharging the earlier one first would mutate the later let's hyp
shape. If you `let("Q(...)")` before `let("R(...)")` and `R`'s body
mentions `Q`, you cannot reorder them.

### `cases_on` requires `>= 2` cases

A degenerate single-leaf disjunction goal can't be closed with
`cases_on` — collapse the disjunction first via `by_disj` /
`disj_witness`, or use `by_eq_mp` if you have an equation.

### `goal()` errors on re-set

There is no "replace the goal" tactic. If you need to massage the
goal, do it before `goal(...)` (e.g., write the simp-equivalent form
that you actually want), or open a `.proof()` sub-frame with the
shape you want and discharge it with the original.

### `goal` `types=` is a parser hint, not a kernel binding

Names declared in `types=` are not added to any kernel-value
namespace — only the parser env. So they don't collide with fact
labels even though they look like identifiers. A subsequent `fix`
*consumes* the hint (consistent), but a fact label of the same name
also coexists silently. **Workaround**: don't reuse `types=` names
as fact labels.

### `by_match` antecedent-only matching

`by_match` peels `==>` off the lemma body until the residual matches
the goal. If your lemma has *no* implication and matching against the
goal fails, the loop raises "no antecedent shape matches goal" —
even though `by(lemma, ...term args)` would have worked. Use
`by`/`by_thm` for pure SPEC chains.

### Frame-local simp doesn't survive frame close

`p.simp(...)` registered inside a `with p.case(...):` block is gone
once the block exits. If you want the rule across the whole proof,
register it at the root frame before opening any block.

### `register_lazy_let` takes the *current* frame

If you call `p.let(...)` inside a sub-frame, the binding dies with
that sub-frame, not at proof end. There's no "register at root from
inside a block" — open the let at the outermost frame that needs
visibility.

### `proof()` decorator validates frame balance, not correctness

If you forget the closing `thus` on the root goal, `@proof` raises
"no result — did you forget thus or close a block?". But if you
discharge the *wrong* goal — say, a `thus(X)` whose `X` is
simp-equivalent to the goal but pretty-prints differently — you
won't know until reading the resulting theorem. The `_simp_require`
in `_finish` only checks shape, not your intent.
