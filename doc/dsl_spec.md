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

Frame kinds: `ROOT`, `INDUCTION`, `IND_BASE`, `IND_STEP`, `CASES`,
`CASE`, `HAVE_PROOF`, `SUPPOSE`. Each block opener pushes the
corresponding kind.

### Closing a frame

`fix` and `assume` write `_Binding` records into a single
`fr.bindings` list in interleaved registration order (`kind="var"` for
fix, `kind="hyp"` for assume). `vars_added` / `hyps_added` are now
read-only views over that list.

`_close_frame(fr, th)` runs in this order:

1. `_discharge_lazy_lets(fr, th)` — substitute every lazy-let carrier
   with its `\args. body` abstraction, BETA-normalize, `PROVE_HYP` the
   now-trivial local-equation hypothesis. Reverse registration order;
   saved `ASSUME`s are INST'd in lockstep, so each binding's
   `asm._concl` still matches `th._asl` when DISCH runs later.
2. `_beta_norm_concl(th)`.
3. Replay `reversed(fr.bindings)`, alternating per kind:
   * `"var"` → `GEN(b.var, th)` (its `ABS` step requires `b.var` to
     be absent from remaining hyps; reverse iteration discharges any
     `v`-mentioning hyp before its GEN, since a hyp added before
     `fix("v")` cannot mention `v`).
   * `"hyp"` → `DISCH(b.asm._concl, th)`, then rewrite the antecedent
     to its goal-form via the saved `term_eq_ant` shape equation (so
     the user's surface form survives simp/let bridging).

Interleaved replay means goals shaped like `!a. h1 ==> !b. h2 ==>
body` close naturally with `fix("a"); assume("h1"); fix("b");
assume("h2"); thus(body)` — no need to peel all foralls up front.

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

Binder annotations accept full type expressions inline (arrows and
parens, registered constructors, single-uppercase tyvars), so a
higher-order goal can avoid the `types=` map entirely:
`goal("!f:ind->ind. f 0 = 0")`. Postfix type application (`num list`)
must be parenthesised in this position to keep the var_decl grammar
unambiguous against juxtaposed bvars.

### `p.fix(names)`

Peel one or more outer foralls. `names` is a string of
whitespace-separated names or a list. Each name must match the next
binder's name *exactly* (no auto-rename). Each peeled binder is added
to `bindings` (as a `"var"` entry) and registered in scope; the
frame's goal becomes the binder body. `fix` and `assume` may be
interleaved freely — `_close_frame` replays them in reverse, so a
goal like `!a. h ==> !b. body` accepts `fix("a"); assume("h");
fix("b")` without flattening the foralls first.

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

`spec` is `"label: term"`, just `"term"` (label auto-generated as
`_h{n}`), or `"label:"` (trailing colon, no body — *inferred-conclusion*
form). The trailing-colon variant skips the term-shape check in
`_finish` and registers the justifier's output at its native conclusion;
useful for intermediate facts whose shape is uniquely determined by the
justification (e.g. `by_inst(LEMMA, *terms)` SPECs the lemma — the
conclusion is fixed by the args, no need to repeat it in the spec).

### Justification methods on `_Have`

* `.by_thm(th)` — direct: `th` already proves the term.
* `.by(just, *args)` — SPEC/MP chain (term arg → `SPEC`, fact arg → `MP`); or callable; simp-aware.
* `.by_match(just, *args)` — backward-chaining: foralls inferred by first-order matching against goal + facts; `...` (Ellipsis) at an antecedent slot auto-derives a reflexive claim via `register_refl_prover`. Conjunctive antecedents (`A /\ B ==> C`, right-associated) auto-CONJ: pass one fact per atomic conjunct and `by_match` builds the `CONJ` chain at MP time. A single fact alpha-matching the whole conjunction is also accepted (back-compat).
* `.by_tree(*, unfold=())` — structural-intro for `P term` goals: walks `term` and dispatches each node via the `IntroSet` registered for `P` (atoms by `aconv`, binary App-style constructor by recursion + `CONJ` + `MP`). `unfold` is an optional list of definitional equations applied via `REWRITE_CONV` to fixpoint on `term` before the walk, then folded back via `EQ_MP(SYM(AP_TERM(P, eq)), ...)` at the end. Use to see past folded constants whose unfolded shape is a registered tree (e.g. `is_sk_term Y_t` with `unfold=[Y_T_DEF, I_T_DEF]`).
* `.by_rewrite(rules, *, ac=None, ac_rules=())` — `REWRITE_PROVE(rules + active simp set, term, ac=ac)`.
* `.by_rewrite_of(ref, rules, *, ac=None, beta=False, op=...)` — rewrite source `ref` to the have-term via shared normal form.
* `.by_unfold(src, *defs)` — `by_rewrite_of` with `beta=True` — bridge unfolded ↔ defined-symbol forms.
* `.by_eq_mp(eq_th, ref)` — `EQ_MP(eq_th, fact)` modulo simp on the LHS; sym-tolerant — flips `eq_th` if the fact aligns with the RHS.
* `.by_def(def_th, ref)` — unfold `def_th` at `ref`'s head args, then `EQ_MP` — sugar for `by_eq_mp(UNFOLD(def_th, ...), ref)`.
* `.by_inst(lemma, *terms)` — `SPECL(terms, lemma)` — pre-instantiate a lemma at term args; pairs with `have("label:")` so the result's conclusion need not be spelled out.
* `.by_spec(lemma, *terms)` — `SPECL` + `BETA_NORM` — like `by_inst` but absorbs the BETA_NORM step when one or more `terms` is a `\v. body`; pairs with `have("label:")`.
* `.by_trans(*eqs)` — `TRANS_CHAIN(eqs)` — compose `a=b`, `b=c`, ... into `a=c`; greedily orients each link, so equations in either direction work.
* `.by_cong(left, right)` — single-step congruence: term + fact → `AP_TERM`; fact + term → `AP_THM`; fact + fact → `MK_COMB`.
* `.by_cong(op, eq1, eq2)` — binop shorthand: from `a=c` and `b=d` derive `op a b = op c d` (i.e. `MK_COMB(AP_TERM(op, eq1), eq2)`).
* `.by_ext(ref)` — function extensionality: `ref` is `!x1...xn. f t1...tn = g t1...tn`; collapses every outer forall via SPEC + `FUN_EXT(GEN ...)` to yield `f = g`.
* `.by_iff(fwd, rev)` — iff-intro: combine `L ==> R` and `R ==> L` facts into the bool equality `L = R` (order-agnostic).
* `.by_fold(ref)` — inverse of an unfolder: fold `ref` back into a registered relation.
* `.by_witness(witness, ref)` — `EXISTS` for an existential have-term.
* `.by_exists(witnesses, *rules)` — introduce `?v1...vn. body` at concrete witnesses; each `/\` conjunct of the substituted body is auto-discharged by alpha-matching against a supplied rule (raw or via `simp_match`) and using it as-is, falling back to `REWRITE_PROVE(rules + active simp set)` for equation conjuncts (reflexive bodies need no rules at all).
* `.by_select_def(def_th, *args, from_)` — read the body of a SELECT-style definition `f = \x1...xk. @v. P v` at concrete `args` from an existence fact `from_: ?v. P v` (one `CHOOSE_WITNESS` + `SYM(UNFOLD)` rewrite).
* `.by_disj(ref)` — `DISJ1`/`DISJ2`-chain a fact into a disjunction goal.
* `.by_ac(op, assoc, comm)` — `AC_PROVE` shortcut.
* `.by_cases(ref, *args)` — open `cases_on` whose target is the have-term.
* `.proof()` — open a sub-frame to prove the have-term inline.
* `.by_contradiction(label_spec)` — classical: open `F`-frame with `~target` as fact, close via `NOT_NOT_ELIM`.

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

`_simp_require` is sym-tolerant: when both target and produced theorem
are equations, it retries against `SYM(th)` if direct/simp matching
fails. Every consumer that funnels through `_simp_require` (`by_thm`,
`by_witness`, `thus`/`have` finalization, `calc` steps, …) inherits
this — equation facts can be supplied in either direction without an
explicit `SYM`.

### `p.sorry()`

Cheat-close the current frame by posting `new_axiom(goal)`. Stub for
incremental development: closes the frame so surrounding structure can
be exercised while flagging the unproved subgoal. Each call adds a
fresh axiom to the kernel's axiom list; `@proof` warns at proof end
naming each sorried goal. Use it where any other frame-closing call
(`p.thus(...).by_*`, `p.absurd().by(...)`, …) would go.

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

### `with p.strong_induction(var_name, ih_label): ...`

Strong / well-founded induction on `var_name`. Auto-peels `!var_name.
body` from the goal (or uses the env-bound var if no leading binder).
Opens a single sub-frame whose goal is `body` and whose IH (registered
under the required `ih_label`) is `!k. lt k var ==> body[var:=k]`.
Unlike Peano induction there is no `base()` / `step()` split — one
sub-frame, one `thus`. The strategy is looked up by `var.ty` in
`_STRONG_INDUCTION_STRATEGIES`; plugins register one via
`register_strong_induction(StrongInductionStrategy(ty, lt, thm))` where
`thm` is `|- !P. (!n. (!k. lt k n ==> P k) ==> P n) ==> !n. P n`.
`nat0_order.py` ships the nat0 strategy.

```python
with p.strong_induction("n", "IH"):
    # goal: body[n]; IH: !k. k < n ==> body[k]
    p.thus(body)...
```

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

### `with p.calc(lhs_spec, *, thus=False) as c: ...`

Mizar-style equational chain (`... .= ...`). `lhs_spec` is `"lhs"` or
`"label: lhs"`; the chain seeds at `lhs` and each step extends it.

Inside the block, each `c.step("= rhs").by_*(...)` proves the segment
`cur_rhs = rhs` and TRANS-composes it onto the running chain;
`cur_rhs` advances to `rhs`. Steps don't push a frame and don't
register their own facts — only the composed equation `lhs =
final_rhs` is registered on context exit (under the user's label or a
fresh `_h{n}`).

`_CalcStep` is a `_Have` subclass, so every justification listed in
§4 is available on a step (`by`, `by_thm`, `by_rewrite`,
`by_rewrite_of`, `by_match`, `by_ac`, `proof()`, …).

With `thus=True`, the composed equation must alpha-match the current
goal and discharges it (mirrors `thus` vs. `have`).

```python
# have-mode: equation registered as a fact for downstream use
with p.calc("eq_A: (x1*z2)*(y2*u2)") as c:
    c.step("= (x1*y2)*(z2*u2)").by_ac(TIMES, SATZ_31, SATZ_29)
    c.step("= (y1*x2)*(z2*u2)").by_thm(e1_zu)
    c.step("= (y1*u2)*(x2*z2)").by_ac(TIMES, SATZ_31, SATZ_29)
sum_eq = MK_COMB(AP_TERM(PLUS, p.fact("eq_A")), p.fact("eq_B"))

# thus-mode: composed equation closes the goal
with p.calc("radd X Y", thus=True) as c:
    c.step("= Q (a*d + c*b) (b*d)").by_thm(radd_XY_eq_canon_LR)
    c.step("= Q (c*b + a*d) (d*b)").by_thm(p.fact("Qcomm"))
    c.step("= radd Y X").by_thm(SYM(radd_YX_eq_canon_RL))
```

Errors: empty chain, malformed step (no leading `=`), goal mismatch
in `thus=True` mode, and per-step shape mismatches all raise
`HolError`.

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
the substituted body `body[witness/w]` is discharged by trying each
`rule` first via `aconv` and `simp_match` against its conclusion (so
non-equation bodies that exactly match a supplied fact are accepted
as-is), then falling back to
`REWRITE_PROVE(rules + active simp set, body[witness/w])` for
equation bodies. First success is `EXISTS`-wrapped, unfolder folded
back, and `DISJ1`/`DISJ2`-chained into the full disjunction.

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
Inline binder annotations (`p.let("Q(i:num, k:A->bool) := ...")`) are
the lighter alternative when the type fits on one line.

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

### `define_with_at(name, ty, body, ...)`

Module-level. Wraps `parser.define`: returns `(DEF, AT)` where
`DEF: |- C = \x1 ... \xn. body` and
`AT: |- !x1 ... xn. C x1 ... xn = body[xi]`. Strips outer abstractions
and beta-reduces stepwise, then `GENL`s the args. For a nullary
definition (no leading `\`), `AT` coincides with `DEF`. Removes the
`AP_THM` + `BETA_CONV` + `TRANS` + `GENL` boilerplate that lift sites
otherwise repeat per definition.

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

* `.by_thm(th)` — `th` already proves `F`.
* `.by(just, *args)` — SPEC/MP chain (non-simp); or callable.
* `.by_conj(ref_a, ref_b)` — match `P` against `~P` (either order); `MP(NOT_ELIM, P)`.
* `.auto(ref)` / `.auto(ref_a, ref_b)` — one-fact: discharge `~(t = t)` via `MP(NOT_ELIM, REFL(t))`. Two-fact: look up a contradiction finder for `(rel(a), rel(b))` in `_CONTRA_FINDERS`.
* `.via(forward, case, *, source)` — lift `case` through `forward` (an implication) into a fact contradicting `source` via `auto`.

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

### Strong-induction strategies — `register_strong_induction(StrongInductionStrategy(ty, lt, thm))`

`thm` is `|- !P. (!n. (!k. lt k n ==> P k) ==> P n) ==> !n. P n`;
consumed by `p.strong_induction(var, ih_label)`. One strategy per
`hol_type`.

### Reflexivity provers — `register_refl_prover(op_name, prover)`

`prover(*shared_args) -> |- op_name shared shared`. Consulted by
`by_match`'s `...` (Ellipsis) auto-derivation and any other primitive
needing to discharge a syntactically reflexive claim. The recognised
target shape is `op a1 ... an a1 ... an` (binary `op t t` is the
`n=1` case); the prover is invoked on the shared front-half args.
`=` is native (`REFL`); derived relations like `>=` / `<=` and
multi-arg "self-equal" heads (e.g. Landau's 4-ary `feq`) register
their own builders.

### Structural-intro sets — `register_intro_set(pred, *, atoms, app)`

`pred` is the unary predicate constant (`is_sk_term`, `is_normal`,
…); `atoms` is a list of `(atom_term, |- pred atom_term)` pairs (true
atoms + leaf-like macros); `app` is `(app_const, |- !a b. pred a /\
pred b ==> pred (app_const a b))`. Consumed by `_Have.by_tree`,
which dispatches each node of the goal's argument term to an atom
rule (matched by `aconv`) or the App-rule (recursive + auto-CONJ).
One IntroSet per predicate; re-registering overrides.

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

The parser's atom resolution (`parser._Builder._lookup`) walks a
single precedence cascade:

1. an in-parse binder for the name (innermost wins)
2. an env-provided `Var` — so `p.fix("F")`, `choose`, and lazy-let
   carriers shadow same-named constants, mirroring how an in-parse
   binder shadows them above
3. a registered constant in `sig.const`
4. an env-provided `Const` / `Comb` / `Abs` term
5. an env-provided `hol_type`, treated as a free `Var` of that type
6. the registry's `default_var_ty`

Step 2 is the reason `fix("F")` works without further parser config:
the local `Var("F", ...)` in `_scope_env` outranks the `F = False`
constant for the lifetime of the frame.

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
