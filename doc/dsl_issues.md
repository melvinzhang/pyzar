## Footguns and gotchas

Things that compile but don't do what they look like, or that surprise
on first encounter. Listed roughly in order of how often they bite.

### `assume` has two modes and silently picks one

```python
p.assume("h1: A", "h2: B")
```

If the goal is `A /\ B ==> C` and both terms alpha-match the
conjuncts, the single `==>` is consumed and the conjunction is split
(`/\` mode). If they *don't* alpha-match — e.g. one term has the
wrong variable — `_try_assume_conj` silently falls through to the
`==>`-chain interpretation, which then fails with a different error
(or, worse, succeeds against an unrelated `==>` shape). The decision
is invisible at the call site. **Workaround**: when you want the
split, double-check the conjunction shape; when you want a chain over
two `==>`, prefer terms that *can't* accidentally look like a
conjunction split.

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

### Negative `int` indexing into facts

`p.fact(-1)` returns the most recent fact, but the index is into
`_fact_order` — a Python list — so out-of-range raises. The
`-1`/`-2` idiom is convenient but tightly coupled to insertion
order; inserting an unrelated `have` between two uses of `-1` will
silently shift what `-1` resolves to.

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

---

## Limitations

Capabilities the DSL deliberately or incidentally lacks. Unlike the
gotchas in §13, these are not surprises that bite during use — they
are walls you'll hit when reaching for something the DSL doesn't
provide.

### Single induction strategy shipped

Only the natural-number strategy is registered out of the box (by
`num.py`). Lists, trees, well-founded recursion, mutual induction,
strong induction — all require a plugin to call `register_induction`
with a custom `induct_prove`. No multi-variable simultaneous
induction primitive.

### No conjunction-introduction block

There is no `with p.conj(): ...` to split `a /\ b` into two sub-goals.
Conjunctions are proved by `by_rewrite`, by deriving each conjunct as
a `have` and then using `CONJ_PAIR`-style assembly, or by
`by_match`-ing a lemma. The DSL is asymmetric: conjunction
*elimination* is first-class (`split_conj`, `assume`'s `/\` mode),
but introduction is not.

### Witnesses from `choose` are SELECT terms only

`p.choose("v", from_=h)` always introduces `@v. body` as the witness
term. There is no way to choose a specific witness while keeping
`choose`'s scope-binding behavior — for that, use `by_witness` /
`disj_witness` (which take a user-supplied witness but don't bind a
name into scope) or compute the witness term yourself.

### `step` substitutes only `body[succ var/var]`

Custom IH substitutions (e.g., proving `P(2*n)` by induction on `n`
with IH `P(2*n)`) require either a custom induction strategy or
manual kernel work; the shipped block always uses `strategy.succ_fn`.

### No tactic-level backward chaining

`by_match` is the closest thing — it matches a single lemma's
antecedents against the goal — but there is no `apply` / `eauto`
loop, no resolution, no congruence-aware backward search. Multi-step
backward chaining must be expressed as a sequence of `have` /
`by_match` calls.

### No incremental / partial proof capture

`@proof` returns either a complete theorem or raises. There is no
"return a `Proof` with what's been done so far so I can inspect"
mode. For interactive development, state must be reconstructed by
re-running the function or by inserting prints / breakpoints.

### Re-opening a closed frame is unsupported

Once a `with` block exits, its frame is gone. There's no "go back
into the previous case" — proofs are linear. If you discover halfway
through case 3 that case 1 needed an extra `have`, you must edit case
1 and re-run.

### No frame-spanning `assume` / `fix`

`fix` and `assume` operate on the *current* frame's goal. They can't
introduce a name into a sibling frame, and there's no Isar-style
`fixes` / `assumes` clause on a block opener. Variables and
hypotheses are introduced strictly top-down within the frame they
belong to.

### Parser is project-specific

The DSL inherits whatever grammar `parser.py` provides. There's no
extensible operator table accessible from `@proof` source — new
binders / infixes need parser-side decorators (`@infix`, `@prefix`,
`@binder`). Errors in spec strings surface as `ParseError` re-raised
as `HolError`.

### `simp` is purely rewriting

The active simp set is consumed by `REWRITE_CONV` and the lazy-let
walker. It is not a decision procedure — no congruence closure, no
arithmetic decision, no SAT/SMT. AC reasoning is opt-in per call
(`ac=` parameter), not part of the simp set.

### No goal-directed `by_witness` for nested existentials

`by_witness(w, ref)` handles a single-layer existential
(`?v. P v`) or a registered relation that unfolds to one. For
`?u. ?v. P u v` you must either nest two `have`s (one per layer) or
supply a fact whose conclusion already has the desired nested
shape — there is no `by_witness(w1, w2, ref)` arity.

### Contradiction finders are pairwise only

`absurd().auto(a, b)` consults a finder keyed on
`(rel(a), rel(b))`. There is no chain of length > 2 — three mutually
inconsistent facts must be reduced to a pair by hand (or via
`absurd().via`, which lifts one fact through an implication before
pairing).

### Frame `result` is single-shot

Each frame holds one `result` theorem. A block opener that wants to
discharge a goal multiple ways (e.g., redundant proofs for
robustness) has to commit to one — there's no way to compose two
candidate proofs into a single result.

---
