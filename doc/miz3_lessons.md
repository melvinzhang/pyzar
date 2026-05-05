# Lessons from miz3 for `proof.py`

`miz3` (Freek Wiedijk's Mizar-style declarative front-end for HOL Light;
`miz3/miz3.ml`, `miz3/miz3_of_hol.ml`, `miz3/grammar/miz3.y`) is a
mature, hand-rolled cousin of what `proof.py` is doing. Reading it
surfaces a handful of design choices that are worth importing or
deliberately rejecting.

## 1. A configurable "horizon" for implicit context

miz3 has a `horizon := <n>` knob that controls how many of the most
recently-derived facts a `by ...` justification sees *implicitly*, in
addition to whatever labels the user names. `horizon := 0` is strict
("name everything"), `horizon := 1` is the typical Mizar-light setting
("the previous step is in scope"), `horizon := -1` accepts everything.
Sample files set this per-proof (`Samples/sample.ml`,
`Samples/lagrange1.ml`, `Samples/forster.ml`).

We have no equivalent. Every `by(...)` / `by_rewrite([...])` argument is
explicit. There is real value in that — labels are checkable
documentation — but the cost is visible in `frac.py` / `rat_int.py`
where lemma names dominate every line. Worth considering:

- A `p.recent()` helper (or `"-"` ref like miz3) returning the last
  registered fact's label, so `.by("h", "-")` saves one rename.
- A frame-scoped `p.simp(...)` already exists for default rewrite
  rules; an analogous `p.context(*labels)` that adds those labels to
  every subsequent `by` chain in the frame would compress repetitive
  bookkeeping without losing the ability to see the dependencies in
  the source.

Take care: miz3's horizon defaults to 1 globally, which makes proofs
order-sensitive and brittle under refactor. Any analogue should be
opt-in, scoped, and visible at the call site.

## 2. `... .= ...` equational chains

miz3 supports Mizar-style equational chains:

```
e = x**(y**i(y))**i(x)  by 1,4,5,22;
  .= ((x**y)**i(y))**i(x)  by 1,2,3,22;
```

(`Samples/lagrange1.ml:84`). Each `.=` line is a `have`/`thus` whose
LHS is reused from the previous line; the chain composes via TRANS at
the end. This is *the* idiom for medium-length algebraic manipulations
and we don't have it. In `frac.py` we currently write a list of
intermediate `have(...)`s and stitch them with `by(SATZ_X)` calls; the
visual through-line is gone.

A reasonable port: `p.calc("x", "x = a + b").step("= a + (c + d)").by(...)
.step("= (a + c) + d").by(...).qed()`. The first call seeds the LHS;
each `.step(...)` parses an equation whose LHS must match (or be
auto-extracted from) the running RHS; `.qed()` registers the composed
equation as a single fact (and does the `thus`-style discharge if the
goal matches).

## 3. Numeric labels with auto-renumbering

miz3 labels are integers (`[1]`, `[2]`, ...), inserted by hand or
auto-generated (`renumber_labels`, `start_label`). The `miz3_of_hol`
module that converts a HOL tactic script back to declarative form
*generates* these label numbers (`miz3_of_hol.ml`,
`step_of_prooftree`).

Our labels are user-chosen strings and we lean hard on that — `IH`,
`hxy`, `nz_q` carry meaning that `[7]` doesn't. We should keep that.
But two miz3 features fall out of numeric labels for free that we
should consider mimicking:

- A `"-"` (last) reference. We have `p.fact(-1)` semantics vestigially
  via `coerce` but it isn't exposed in `by(...)` ref strings; treating
  the literal label `"-"` as "the previous step" in any ref would close
  the gap.
- A `"*"` reference meaning "all assumptions in the current frame".
  miz3 uses this to force the prover into the full context. We don't
  need this often, but it would simplify a few `_rewrite_facts` lists.

## 4. `now ... end` anonymous sub-blocks

```
now [3]
  assume !n. R n (SUC n);
  ...
  thus m <= n ==> R m n by LE_EXISTS;
end;
```
(`Samples/sample.ml`, `Samples/lagrange1.ml:101`). A `now` block is a
sub-proof whose conclusion is *inferred from the last `thus` inside
it* and registered against the parent label `[3]`. No goal-spec
needed.

Our `_Have.proof()` requires the goal up front (the `have(spec).proof()`
pattern). For local lemmas where the user is computing the conclusion
on the fly (especially common in Forster-style monotonicity arguments),
a `with p.now() as q:` that synthesizes the conclusion from the inner
`thus` would cut a redundant copy of the term. This is dual to point
2: `calc` builds an equation lemma, `now` builds an arbitrary lemma.

## 5. Embedded HOL tactics as a fallback (`exec`)

miz3 has `exec REWRITE_TAC[group; subgroup; SUBSET];` as a step
(`Samples/lagrange1.ml:25`) that runs an arbitrary HOL Light tactic
against the current proof state. `proof.py`'s analogue is
`by_rewrite_of`/`by_rewrite` plus the various `by_*` builders, which
are richer in some ways (simp-aware, lazy-let aware) but *closed*: if
no existing `by_*` does what you need, you have no escape hatch short
of writing a kernel function and calling `.by_thm(...)`.

Concrete example: the `exec REWRITE_TAC[...]` opener strips the goal of
its `group(...)`/`subgroup(...)` predicates before the declarative
script begins. We don't have a "preprocess the goal with this conv"
step. A `p.preprocess(conv_or_rules)` that mutates `_cur.goal` (and
records an equality theorem to compose at frame close) would let
algebraic-structure proofs open with the same one-liner.

## 6. "Sketch mode" / `proof_expected`

miz3 supports writing a proof skeleton with no justifications and
running it; the prover reports which steps it could fill in with the
default tactic and which need help (`Samples/lagrange1.ml:225` onward
shows `GROUP_LAGRANGE_COSETS_SKETCH` with embedded `:: 1: inference
error` annotations, and `:: #2` markers for step counts). That makes
top-down proof development incremental: write all the structure, then
fill the holes.

We can't do this. The closest equivalent would be:
- `by_admit("...")` — register the term as a fact without a proof,
  produce a real theorem with `[admitted]` as a hypothesis. The kernel
  has `ASSUME`; we'd need to make sure these hyps don't get silently
  discharged at frame close.
- A run mode that reports every `HolError` from a `by_*` justification
  but continues with `ASSUME`-as-fallback so the user sees the full
  list of failing steps in one run.

This is high-leverage for large proofs: the current "first failure
stops everything" model means a typo in step 5 hides whatever else is
wrong with steps 30-50.

## 7. Caching

miz3 has `by_item_cache` and `just_cache` (miz3.ml:288, 1151) — when
the same (tactic, fact set, goal) triple has succeeded before, replay
the theorem instead of running the prover. Re-running a proof script
during interactive development is dramatically faster as a result.

We rerun every `REWRITE_PROVE` call from scratch. For test-driven
porting work this is fine (each test is independent and short), but
for long single proofs (`landau.golden` is the obvious target) a
keyed-by-`(rule_concls, target)` cache on `REWRITE_PROVE` outputs
would shave noticeable time. Risk: cache invalidation when rules are
shadowed. Worth a measurement before building.

## 8. What we got right (and miz3 didn't)

It's worth being explicit about the points where we should *not*
import from miz3:

- **Plain-text DSL.** miz3 parses a quoted Mizar string out of an OCaml
  source file (`miz3/grammar/miz3.y`, `miz3.ml:39-83` `parse_script`),
  then lexes/parses it. Our embedding in Python — every step is a
  Python method call — gives us syntax errors at the right line, IDE
  navigation, type checking on rule names, and trivial parameterization
  (loops over a list of similar lemmas). Don't go back.
- **Implicit context window (horizon=1).** Mentioned above. Requiring
  explicit refs is a feature, not a bug. Any "recent fact" sugar should
  be a *named* shorthand, not the default.
- **Mutable global state.** miz3 has `horizon`, `timeout`,
  `default_prover`, `proof_indent`, ... all as global `ref`s
  (miz3.ml:4-20). Our equivalents (induction strategies, contra finders,
  etc.) live in registries but are added at import time and are
  effectively immutable; users don't toggle them mid-proof.
- **Surface-level pretty-printing as the source of truth.** miz3's
  `string_of_substep` / `pp_step` / `outdent` machinery (miz3.ml:810,
  1000, 1032) exists because the on-disk Mizar-style proof *is* the
  data structure miz3 mutates (e.g. the "grow" feature rewrites the
  source). Our proof scripts are normal Python — if you want to
  rearrange them, the editor is enough.

## 9. Rough priority

1. **`p.calc(...)` equational chains.** Highest concrete payoff for
   `frac.py` / `rat_int.py`. ~50 lines.
2. **`now` / `have(...).proof()` without goal.** Removes a class of
   duplicated terms in declarative blocks. Small.
3. **`"-"` last-fact ref in `by(...)`.** Trivial; immediate readability win
   on chained reasoning.
4. **`p.preprocess(...)` opener.** Replaces goal-shape boilerplate at
   the top of structured-object proofs (groups, posets, ...).
5. **Sketch mode / admit.** Larger surface area, but the right answer
   for any proof above ~50 steps. Defer until we hit one we can't
   debug.
6. **Caching.** Measure first.
