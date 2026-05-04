# Proof DSL specification

A reference for the declarative proof DSL implemented in `proof.py`. The
DSL is Isar-flavored: every step produces one kernel theorem, named
facts accumulate in a frame stack, and structured blocks (induction,
cases, suppose) are entered as Python `with`-statements that discharge
on exit.


---

## 1. Entry point

```python
from proof import proof

@proof
def THM(p):
    p.goal("...")
    ...
```

`@proof` instantiates a `Proof`, runs `fn(p)`, and returns the kernel
theorem at the root frame. It raises if frames are unbalanced at end
or if the root frame has no `result` (no closing `thus`/block).


---

## 2. The frame stack

Every `Proof` maintains a stack of `_Frame`s. The bottom is `ROOT`
(`FrameKind.ROOT`); structured blocks push and pop frames. Each frame
carries:

| Field            | Purpose                                                   |
|------------------|-----------------------------------------------------------|
| `goal`           | term to discharge — set by `p.goal(...)`, peeled by `fix`/`assume`/block openers |
| `vars_added`     | foralls introduced by `fix`; `GEN`'d on close             |
| `hyps_added`     | hypotheses introduced by `assume`; `DISCH`'d on close     |
| `facts_added`    | fact labels registered in this frame; dropped on exit     |
| `choose_env`     | witness names bound in this frame (`name → term`)         |
| `type_env`       | parser hints for higher-order or non-default-typed names  |
| `lazy_lets`      | local definitions (`define`/`let`); discharged on close   |
| `simp_rules`     | frame-local default rewrite rules                         |
| `data`           | kind-specific (`_InductionData`, `_CasesData`)            |
| `result`         | the discharging theorem; set by closing tactic            |

Frame kinds: `ROOT`, `INDUCTION`, `IND_BASE`, `IND_STEP`, `CASES`,
`CASE`, `HAVE_PROOF`, `SUPPOSE`. Each block opener pushes the
corresponding kind.

### Closing a frame

`_close_frame(fr, th)` runs in this order:

1. For each `h` in `reversed(fr.hyps_added)`, `DISCH(h.asm._concl, th)`,
   then rewrite the antecedent to its goal-form via the saved
   `term_eq_ant` shape equation (so the user's surface form survives
   simp/let bridging).
2. `_discharge_lazy_lets(fr, th)` — substitute every lazy-let carrier
   with its `\args. body` abstraction, BETA-normalize, `PROVE_HYP` the
   now-trivial local-equation hypothesis. Reverse registration order.
3. `_beta_norm_concl(th)`.
4. `GEN` over `reversed(fr.vars_added)` (must be free of remaining
   hyps).

Sub-frames also `p._drop_facts(fr.facts_added)` after their `on_close`
runs, so frame-local labels do not leak.

---

## 3. Goal, fix, assume

### `p.goal(spec, types=None)`

Set the current frame's goal. Errors if already set. `types` is an
optional `{name: hol_type}` mapping for higher-order parameters; the
parser consults it for bare identifiers and binders so `goal("!f. f
0 = 0", types={"f": ind_to_ind})` works.

`hol_type` values can be built with `parser.parse_type` instead of
the kernel constructors, e.g. `types={"f": parse_type("ind -> ind")}`
in place of `mk_fun_ty(ind_ty, ind_ty)`.

### `p.fix(names)`

Peel one or more outer foralls. `names` is a string of
whitespace-separated names or a list. Each name must match the next
binder's name *exactly* (no auto-rename). Each peeled binder is added
to `vars_added` and registered in scope; the frame's goal becomes the
binder body.

### `p.assume(*specs)`

Consume the goal's antecedent(s) as facts via pattern destructuring.
Each spec consumes one `==>`; the spec's *pattern* then destructures
the consumed antecedent into named facts.

Pattern grammar (parsed by `parser.parse_pattern_spec`):

```
pattern_start := pattern (":" term)?
pattern       := NAME                              # PatName
               | "(" pattern ("," pattern)+ ")"    # PatConj (>= 2 parts)
```

Patterns:

* **Atomic** — `label` / `label: term`: register the antecedent under
  `label`. `_` is anonymous (auto-generated `_h{n}`). When `term` is
  given, it is `simp_aconv`-checked against the goal's antecedent and
  preserves the user's surface form across frame close via
  `_derive_shape_eq`.
* **Conjunction split** — `(p1, p2, ..., pn)` / `(p1, p2, ..., pn):
  term`: the antecedent must be a right-associated conjunction with
  `n` conjuncts; each sub-pattern receives the corresponding conjunct
  via a `CONJUNCT1`/`CONJUNCT2` chain. Sub-patterns may themselves be
  tuples (nested destructure) or names. Simp-normalizes the
  assumption before splitting, so a folded carrier whose unfolded
  form is a conjunction still works.

Examples:

```python
p.assume("h: A")                              # atomic, one ==>
p.assume("h1: A", "h2: B")                    # chain, two ==>s
p.assume("(h1, h2): A /\\ B")                 # split: h1: A, h2: B
p.assume("(h1, _, h3): A /\\ B /\\ C")        # _ discards a conjunct
p.assume("(h, (a, b)): A /\\ (B /\\ C)")      # nested
```

New pattern kinds (existential witness, iff-split, disjunction
case-split, …) plug in by extending `_GRAMMAR`'s `pattern` rule with
a new alternative + visitor method in `parser.py`, then registering a
handler via `proof.register_pattern_handler(PatType, handler)`. The
handler receives `(p, pat, th)` where `th` is a kernel theorem of the
consumed antecedent's shape.

### `p.split(ref, spec)`

Run the same pattern grammar as `assume` on an arbitrary existing
fact (label, index, or theorem). The pattern destructures `ref`'s
conclusion and registers the resulting sub-theorems as facts;
simp-normalization happens inside the conjunction-pattern handler so
folded carriers whose unfolded form is a conjunction still expose the
top `/\\`. The optional `: term` annotation is
simp-equivalence-checked against `ref`'s conclusion.

```python
p.split("h", "(h1, h2)")            # split a conjunction fact
p.split("h", "(h1, _, h3)")         # discard middle conjunct
p.split(-1, "(h1, (h2, h3))")       # nested destructure
p.split("h", "(h1, h2): A /\\ B")   # with shape annotation
```

---

## 4. Have / thus

Every intermediate step is a `have` or `thus`:

```python
p.have("label: term")           # add `label: term` as a fact
p.thus("term")                  # discharge the current goal as `term`
```

`p.have(spec)` and `p.thus(spec)` both return a `_Have` object whose
`by_*` methods supply the justification. `thus` additionally sets
`fr.result` and lifts the supplied theorem to the goal's exact shape
via `_simp_require`.

`spec` is `"label: term"` or just `"term"` (label auto-generated as
`_h{n}`).

### Justification methods on `_Have`

| Method                                              | Meaning                                                                |
|-----------------------------------------------------|------------------------------------------------------------------------|
| `.by_thm(th)`                                       | direct: `th` already proves the term                                   |
| `.by(just, *args)`                                  | SPEC/MP chain (term arg → `SPEC`, fact arg → `MP`); or callable; simp-aware |
| `.by_match(just, *args)`                            | backward-chaining: foralls inferred by first-order matching against goal + facts |
| `.by_rewrite(rules, *, ac=None, ac_rules=())`       | `REWRITE_PROVE(rules + active simp set, term, ac=ac)`                  |
| `.by_rewrite_of(ref, rules, *, ac=None, beta=False, op=...)` | rewrite source `ref` to the have-term via shared normal form    |
| `.by_unfold(src, *defs)`                            | `by_rewrite_of` with `beta=True` — bridge unfolded ↔ defined-symbol forms |
| `.by_eq_mp(eq_th, ref)`                             | `EQ_MP(eq_th, fact)` modulo simp on the LHS                            |
| `.by_fold(ref)`                                     | inverse of an unfolder: fold `ref` back into a registered relation     |
| `.by_witness(witness, ref)`                         | `EXISTS` for an existential have-term                                  |
| `.by_disj(ref)`                                     | `DISJ1`/`DISJ2`-chain a fact into a disjunction goal                   |
| `.by_ac(op, assoc, comm)`                           | `AC_PROVE` shortcut                                                    |
| `.by_cases(ref, *args)`                             | open `cases_on` whose target is the have-term                          |
| `.proof()`                                          | open a sub-frame to prove the have-term inline                         |
| `.by_contradiction(label_spec)`                     | classical: open `F`-frame with `~target` as fact, close via `NOT_NOT_ELIM` |

`.by` and `.by_match` resolve string args polymorphically: a known
fact label resolves to a theorem, otherwise the string is parsed as a
term in scope. Negative `int` args index into the fact insertion
order.

### `_finish` semantics

After producing a theorem `th`, `_Have._finish(th)`:

* If `is_thus`: `simp_require(goal, th)`, set `fr.result = th`.
  The fact is registered at goal shape (no redundant simp lift) since
  `thus`-facts have frame-local lifetime.
* Otherwise: `simp_require(self.term, th)`, register at have-term
  shape.
* Register under `self.label` (or a fresh `_h{n}`).

---

## 5. Block constructs

All blocks are Python `with`-statements. The block's body uses the
same `p` object; the block opener pushes a sub-frame, the closer
discharges and writes the parent frame's result.

### `with p.induction(var_name): ...`

Open an induction block. If the goal is `!var_name. body`, the binder
is peeled automatically. Otherwise `var_name` must already be in scope
(via `fix`).

The induction strategy is looked up by `var.ty` in
`_INDUCTION_STRATEGIES`. Plugins register strategies via
`register_induction(InductionStrategy(ty, base_term, succ_fn,
induct_prove))`. `num.py` ships the natural-number strategy.

Inside the block:

```python
with p.base():
    p.thus("body[base/var]")...

with p.step("IH"):                # IH label is required, no default
    p.thus("body[succ var/var]")...    # `IH` is body[var/var]
```

`base()` errors outside `induction()`; same for `step()`.

### `with p.cases_on(ref, *args): ...`

Case-split on a disjunction. `ref` is a fact label, theorem, or
relation fact (`a R b` for a relation registered with
`register_disj_unfolder`, e.g. `<=`, `>=` — auto-unfolded to a
disjunction). Extra `*args` are `MP_LIST`-applied to the resolved
theorem before splitting.

Inside, each branch is opened with:

```python
with p.case("label: disjunct"):
    p.thus(target)...
```

If a leaf is `?v. body`, the case auto-introduces a `choose`-style
witness: `v` enters scope and `v_eq: body[v]` is registered (no need
for an explicit `p.choose` inside the case). The display name follows
the user's spec bvar; falls back to the leaf's bvar.

A `cases_on` block requires `>= 2` cases. Branches need not appear in
disjunct order; they're matched by `aconv` to the right-associated
leaves.

### `with p.suppose("label: p"): ...`

Open a hypothetical sub-block when the current goal is `~p`. The
inner goal is `F`, `label: p` is registered as a fact, and on close
the `F`-theorem is wrapped via `NOT_INTRO(DISCH(p, F_th))` to
discharge the parent's `~p`.

Spec may be a bare label (`"h"`) — the negated body is filled in —
or `"h: p"` (must `simp_aconv`-match the inner of `~p`).

### `with p.have(...).proof(): ...`

Sub-frame whose goal is the have-term. Body proves it via standard
tactics; on exit the result is registered as the have's fact (and, if
called from `thus`, as the parent's result).

### `with p.have(...).by_contradiction("h"): ...`

Classical contradiction: opens an `F`-frame with `h: ~target` as a
fact. Body derives `F`; on close, `NOT_NOT_ELIM` lifts `~~target`
back to `target`.

---

## 6. Witnesses

### `p.choose(name_spec, from_, eq_label=None)`

Eliminate an existential. `name_spec` is `"name"` or `"name:
equation"`. `from_` is a fact whose conclusion is `?v. body`, or a
relation registered with an existential unfolder (`>`, `<`).

Effects:
* `name` enters scope as the SELECT-derived witness term
  (`@v. body`).
* A fact `eq_label` (default `f"{name}_eq"`) is registered with
  conclusion `body[name/v]` and hypotheses inherited from the source.

If `eq_check` is supplied, it is parsed in scope (with `name` bound)
and `simp_match`-checked against the witness body.

### `p.disj(*rules, ac=None)`

Close a disjunction goal by discharging some leaf directly. Each
`rule` whose conclusion alpha-matches a leaf is used as-is; otherwise
each leaf is tried via `REWRITE_PROVE(rules + active simp set, leaf,
ac=ac)`. With no rules, collapses to `REFL` for tautological leaves.

### `p.disj_witness(witness, *rules, ac=None)`

Close a disjunction goal by witnessing an existential leaf. For each
leaf that is `?w. body[w]` (directly or via a registered unfolder),
attempt `REWRITE_PROVE(rules + active simp set, body[witness/w])`.
First success is `EXISTS`-wrapped, unfolder folded back, and
`DISJ1`/`DISJ2`-chained into the full disjunction.

---

## 7. Local definitions and simp

### `p.let("NAME(arg1, arg2, ...) := body", types=None)`

Isabelle-style local abbreviation. A fresh kernel `Var NAME : t1 ->
... -> tn -> body_ty` enters scope as a *carrier*; an internal
local-equation theorem `[!args. NAME args = body] |- !args. NAME args =
body` is associated with it.

Goals and facts mention `NAME` in folded form throughout the proof.
The hypothesis is discharged on frame close: carrier substituted with
`\args. body`, BETA-normalized, hypothesis `PROVE_HYP`'d. The
resulting theorem has no lazy-let baggage and never names `NAME`
externally.

`types` supplies types for fresh tyvars or function-typed bvars not
registered as parser aliases. Values may be built with
`parser.parse_type` (e.g. `"num -> A -> bool"`) just as for `goal`.

### `p.unfold_let(name, *args)` / `p.fold_let(name, *args)`

Produce the local equation specialized at args:
`|- name a1...an = body[bvars := ai]` (and its `SYM`).

### `p.materialize_let(th, name)`

Substitute the named carrier with `\args. body` in `th` and BETA-
normalize. Use when downstream code needs the original lambda shape.

### `p.unfold(def_th, *args)`

Thin wrapper over `tactics.UNFOLD`: applies a global definition
equation to argument terms; string args parsed in scope.

### `p.simp(*rules)`

Register one or more theorems as default rewrite rules in the current
frame. Each rule is a fact label or theorem. Rules
extend the active simp set, used silently by every subsequent
`by_rewrite`-family / `disj`-family call in this frame and any nested
frame. Frame-scoped: a sub-block can extend without affecting the
surrounding proof.

### Simp-aware bridges

`simp_aconv`, `simp_match`, `simp_normalize`, `simp_norm_fact`,
`simp_mp`, `simp_eq_mp` align folded and unfolded forms across
boundaries. The bottom-up walker (`_unfold_walk`) bypasses
`REWRITE_CONV`'s under-binder filter — sound because lazy-let
equations are `!args. carrier args = body` and `ABS` succeeds when
the bvar is not free in any hyp.

---

## 8. Absurd (deriving F)

`p.absurd()` returns an `_Absurd` helper that produces a theorem of
conclusion `F`, wrapped via `CONTR(goal, F_th)` and set as the
frame's result. Methods:

| Method                                    | Meaning                                                           |
|-------------------------------------------|-------------------------------------------------------------------|
| `.by_thm(th)`                             | `th` already proves `F`                                            |
| `.by(just, *args)`                        | SPEC/MP chain (non-simp); or callable                              |
| `.by_conj(ref_a, ref_b)`                  | match `P` against `~P` (either order); `MP(NOT_ELIM, P)`           |
| `.auto(ref_a, ref_b)`                     | look up a contradiction finder for `(rel(a), rel(b))` in `_CONTRA_FINDERS` |
| `.via(forward, case, *, source)`          | lift `case` through `forward` (an implication) into a fact contradicting `source` via `auto` |

---

## 9. Registries

Plugin-registered, consulted by core dispatch:

### Relation unfolders — `register_unfolder(op, fn)` / `register_disj_unfolder(op, fn)`

`fn(a, b)` returns `|- (op a b) = body`. Two kinds:

* `"exists"` — `body` is `?v. ...`. Consumed by `choose`,
  `by_witness`, `disj_witness`.
* `"disj"` — `body` is `left \/ right`. Consumed by `cases_on`.

`by_fold` accepts either kind. Use `register_relation(RelationDef(op,
kind, fn))` for full control.

### Contradiction finders — `register_contra_finder(rel_a, rel_b, finder)`

`finder(th_a, th_b) -> |- F` for facts `rel_a a b` / `rel_b a b`.
Both orientations are stored automatically.

The `@contra_finder` decorator stacks on top of `@proof` and
auto-registers a theorem of shape `!vs. R1 a b ==> R2 a b ==> F`.
Constraint: the first antecedent must uniquely determine the foralls
(its operands are the schematic vars). For symmetric-shape
antecedents like `a = b`, put the rigid relation first.

### Induction strategies — `register_induction(InductionStrategy(ty, base_term, succ_fn, induct_prove))`

`induct_prove(var, body, base_th, step_fn) -> |- !var. body` is the
kernel principle; `step_fn(IH) -> step_th`.

### Assume patterns — `register_pattern_handler(pat_type, handler)`

`handler(p, pat, th) -> None` registers the facts for a pattern node
type, given a kernel theorem `th` whose conclusion is the term the
pattern destructures. Built-in handlers cover `PatName` (atomic
binding) and `PatConj` (right-associated conjunction split). New
pattern kinds require:

1. A new alternative on the `pattern` rule in `parser.py`'s `_GRAMMAR`
   plus a visitor method on `_Builder` returning a fresh AST node
   class.
2. A handler registered here.

`assume` then dispatches automatically — no further core changes.

---

## 10. Names and namespaces

`_namespace_kind(name)` covers four namespaces that resolve to
*different kernel values* at lookup:

* fact labels (in `self._facts`)
* lazy-let carriers (`fr.lazy_lets`)
* choose witnesses (`fr.choose_env`)
* fixed variables (`fr.vars_added`)

Registering any of these errors if the name already lives in another
namespace (`_require_fresh_name`). `type_env` is intentionally
excluded — it is a parser hint, not a separate kernel value, so
`fix` realising the hint is consistent.

Auto-generated labels are `_h{n}` (anonymous have/assume) and
`{name}_eq` (choose default).

Fact references resolve via `coerce`:

* `thm` → returned unchanged
* `str` → fact label, or (with `accept_term=True`) parsed as a term in scope
* term → returned (with `accept_term=True`) or rejected

---

## 11. Parser scope

`_scope_env()` is rebuilt on each `_parse` from the frame stack
(outer → inner) and contains:

* constants `T`, `F`
* every `type_env` entry
* every `vars_added` (kernel `Var`)
* every `choose_env` witness term
* every `lazy_lets` carrier `Var`

Lookup is last-write-wins, so inner frames shadow outer.

---

## 12. Errors

Every parse / shape / matching failure raises `HolError` with an
op-prefixed message naming the call site (`assume:`, `by_match:`,
`induction:`, …). Kernel errors (e.g., `ABS` failing because a bvar
is free in a hyp) propagate unchanged when not specifically caught;
soft simp failures use `_simp_require` for uniform shape-mismatch
messages.

`@proof` itself raises if frames are unbalanced at end or the root
has no `result`.

---

## 13. Worked example

```python
@proof
def SATZ_5(p):
    p.goal("!x y z. (x + y) + z = x + (y + z)")
    p.fix("x y z")
    with p.induction("z"):
        with p.base():
            p.thus("(x + y) + 1 = x + (y + 1)") \
                .by_rewrite([ADD_1, ADD_SUC])
        with p.step("IH"):
            p.thus("(x + y) + SUC z = x + (y + SUC z)") \
                .by_rewrite([ADD_SUC, "IH"])
```

* `goal` records the full forall.
* `fix("x y z")` peels three binders into `vars_added`; goal is now
  the body.
* `induction("z")` consumes `z` from `vars_added` and pushes an
  `INDUCTION` frame; the strategy is the natural-number one.
* `base()` pushes `IND_BASE` with goal `(x + y) + 1 = x + (y + 1)`.
* `step("IH")` pushes `IND_STEP` with `IH: (x + y) + z = x + (y +
  z)` as a fact and the successor-substituted goal.
* On `induction` exit, `INDUCT_PROVE` composes base/step into `|- !z.
  body`; `_close_frame` then `GEN`s `x`, `y`.
