## Limitations

Capabilities the DSL deliberately or incidentally lacks. Unlike the
gotchas above, these are not surprises that bite during use — they
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
*elimination* is first-class (`assume`'s tuple pattern, `p.split`),
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

### `assume` patterns can't bind the whole and destructure

The `(p1, p2): A /\\ B` form binds the parts but discards the whole
conjunction fact. If a downstream step needs both `h1: A`, `h2: B`
*and* `h: A /\\ B` (e.g., to MP a lemma whose antecedent is
`A /\\ B`), the tuple pattern alone won't do it; you must fall back
to `assume("h: ...") + split("h", "(h1, h2)")`. There is no
"bind whole + destructure" pattern syntax (e.g. `@h(h1, h2): ...`)
to capture both at once.

### Pattern destructure ships only conjunction + name

The pattern registry currently has handlers only for `PatName` and
`PatConj`. New pattern kinds (existential witness, iff-split,
disjunction case-split, ...) need a `register_pattern_handler`
plugin. Until those land, destructuring an existential or iff fact
produced by `have` / `choose` / an MP chain still needs hand-written
`CHOOSE_WITNESS` / `EQ_IMP` / etc. -- but conjunctions are covered
end-to-end by `assume`'s tuple pattern and `p.split`.

### No rewriter for an explicit-binder bridge

`by_rewrite` / `by_rewrite_of` filter out rewrites whose equation
mentions a bound variable of the surrounding term, so an equation
like `k = n` cannot be lifted under a `!Q. ...` binder that captures
neither side. The escape hatch is to build the abstraction by hand
(`mk_abs(kk, body)`) and chain `SYM(BETA_CONV) ; AP_TERM(...) ;
BETA_CONV` — the `R_func_a` dance in `R_UNIQUE_STEP` (`num.py:691`).
A `p.rewrite_at(var, eq)` (or relaxed filter that takes an explicit
abstraction point) would absorb this. **Workaround**: hand-roll the
beta bridge as in `num.py:691-700`.

### `by_witness` doesn't beta-reduce the substituted body

When the witness term is a `\n. ...` whose application beta-reduces
to the user's target, `by_witness` (via `simp_require`) doesn't
chain the BETAs needed to align the existential body with the fact.
The escape hatch is a manual `BETA_CONV` triple +
`TRANS_CHAIN` — `NUM_RECURSION` does this at `num.py:791-805`
(`beta_1`, `beta_n`, `beta_sn`, then `fn_sn_eq = TRANS_CHAIN(...)`).
Beta-aware matching in `by_witness` would collapse the tail.

### `MK_DEST` / `DEST_MK` peel idiom not abstracted

Each proof that crosses the `num`/`ind` type-definition boundary
re-derives the same instantiation pattern: `INST([(t, r_var)],
DEST_MK)` for some `t`, then `EQ_MP` to peel the
`NUM_REP`-wrapped form. `AXIOM_3`, `AXIOM_4`, and `INDUCTION` all
do this (`num.py:360-362, 387-389, 449-457`). The proofs read
declaratively except for these peels. There's no DSL-level helper
because the pattern is specific to `new_basic_type_definition`'s
output shape; a `peel_NUM_REP(t)` rule (or, more generally, a
`peel_subtype(MK_DEST, DEST_MK, t)` factory) would let those proofs
go through `by_thm` without the inline `INST`/`EQ_MP` plumbing.

### Order/disjunction folders aren't first-class

`LT_TO_LE`, `EQ_TO_LE`, `GT_TO_GE`, `EQ_TO_GE` (`nat.py:490-506`)
are written as ~1-line raw-kernel helpers
(`EQ_MP(SYM(UNFOLD_LE(a,b)), DISJ_(...))`) because they have to
return a `thm` — `by_match` slots take theorems, not in-block proof
calls. The DSL's `by_fold` + `by_disj` cover the same ground but
only inside a proof block, so these helpers can't be expressed with
them. A "promote a `by_*` chain to a standalone rule" facility, or
just rewriting the four as `@proof` lemmas, would close the gap.

### No fact-flip helper (`SYM` / `NE_SYM`)

Flipping a named equation requires raw `SYM(p.fact("name"))` — there
is no `p.sym("name")` or `by_thm(..., flip="name")` surface, and no
`by_rewrite_of` mode that takes a fact name and applies it
right-to-left. This is the single most common residual kernel
pattern in the rat-level proofs: ~30 sites across `rat_int.py`
(SATZ_81, 84-90, 94, 95, 97A/B, 101, 106A/B, 110, 111, 114,
RMUL_ONE, ...) and many in `frac.py` (SATZ_55, 56, 60, 61, 67_EXIST,
...). The disequation form `NE_SYM` (`num.py:169`) has the same gap.
**Workaround**: a one-line `p.have("name_sym:").by_thm(SYM(p.fact(
"name")))` per use — verbose enough that authors usually inline the
raw call instead.

### `simp` / `by_match` take theorems, not `(lemma, args)` pairs

When the user wants a partially-instantiated lemma fed into the simp
set or as a `by_match` rule, the only surface is to materialize it
inline as `SPECL([Z_t, Y_t], SATZ_92)`. There is no
`p.simp_with(LEMMA, [Z_t, Y_t])` / `by_match_with(...)` form.
Instances: `rat_int.py:1148, 1172, 1619, 1643` (SATZ_98, SATZ_99A,
SATZ_107, SATZ_108A) all double up
`p.simp(SPECL([...], SATZ_92), SPECL([...], SATZ_92))` to register
two pre-specialized commutativities before a `by_rewrite_of` step.

### No congruence combinator under operators

When you have `a = b` and need `f a c = f b c` or `g (h a) = g (h
b)`, the proof reaches for raw `AP_TERM` / `AP_THM` / `MK_COMB`
chains — there is no `p.cong(f, "e1", "e2")` or `p.under(f, eq)`
surface. The fraction-arithmetic proofs are dense with this pattern:
`frac.py:132` (SATZ_39 `MK_COMB(AP_TERM(TIMES, e1), e2)`),
`frac.py:211` (SATZ_44), and especially `frac.py:600-715` (SATZ_57,
SATZ_58, SATZ_59 build long chains of `AP_THM(AP_TERM(...), ...)` to
lift equations under `+` / `*`). A congruence combinator would cut
these proofs significantly.

### `TRANS` / `TRANS_CHAIN` aren't usable as glue outside `calc`

`p.calc(...)` emits a final equation theorem, but only by closing
the frame as a `have` / `thus` registered fact. When the user needs
an *intermediate* equation theorem to pass into another kernel call
(e.g., `AP_TERM(...)` or the second arg of `EQ_MP`), they fall back
to `TRANS` / `TRANS_CHAIN` directly. Instances: `num.py:474, 765`
(R_UNIQUE_STEP, INDUCTION compose intermediate equations),
`rat_int.py:2028` (SATZ_115 `eq_WX_Y = TRANS(com, rdiv_prop)`),
`frac.py:669, 676, 698, 705` (SATZ_59 nests TRANS chains between
distributivity steps).

### `by_witness` body often needs hand-`CONJ` assembly

`by_witness(["a", "b", ...], body_thm)` accepts a single theorem; if
the existential body is a conjunction, the body theorem must be
assembled by hand. There is no spec-string surface like
`by_witness(["a", "b"], "REFL, REFL, hgt")` or a
`by_witness_conj(...)` arity. Instances: `rat_int.py:499, 510`
(RGT_INTRO, RLT_INTRO assemble `CONJ(REFL(Q_ab), CONJ(REFL(Q_cd),
hgt))` for the `?a b c d. Q a b = X /\ Q c d = Y /\ ...` shape) and
`num.py:256` (NUM_REP_IND_SUC_CLOSED). This is a special case of
the missing conjunction-introduction block, but the call site is
specifically `by_witness`, not a top-level conjunction goal.

### `CHOOSE_WITNESS` has no DSL surface

`p.choose("v", from_=h)` introduces `@v.body` (a SELECT term) into
scope, but there is no surface that returns the *witness theorem*
`P (@v.body)` directly for use as an MP argument outside the bound
scope. NUM_RECURSION (`num.py:820, 831, 837`) calls `CHOOSE_WITNESS`
three times to thread unique-recursion witnesses through the
construction. This is independent of the existing "Witnesses from
`choose` are SELECT terms only" entry — that one is about *which
term* `choose` selects, this is about getting the witnessing
*theorem* without binding a name into scope.

### No DSL surface for extensionality (`FUN_EXT` / `GEN`)

To prove `f = g` from `!x. f x = g x` (or, two-level, `!x y. f x y =
g x y`), the proof reaches for raw `GEN` / `FUN_EXT`. There is no
`p.fun_ext(...)` or `with p.ext("x"):` block. Instance:
`rat_int.py:321-325` (RAT_EQ derives `feq a b = feq c d` from a
pointwise equality by `FUN_EXT(GEN(...))` twice to peel both
arguments).

### `UNFOLD(DEF, t1, t2, ...)` mid-expression has no DSL form

`p.unfold(DEF, "x")` registers an unfold theorem as a fact in the
current frame, but when the user needs the unfold *theorem* as a
direct argument to another kernel call — typically wrapped in `SYM`
or fed into `EQ_MP` — they fall back to raw `UNFOLD(DEF, t1, t2,
...)`. Instances: `rat_int.py:266, 415, 1843, 1875, 1933, 1996`
(RAT_EQ, Q_SURJ, SATZ_111A_REV, SATZ_111C_REV, RMUL_ONE, SATZ_114
all do `EQ_MP(SYM(UNFOLD(DEF, ...)), ...)` to flip a definitional
equation in place).

### Bootstrap defs predate the DSL

The classical-logic kernel proofs (`classical.py:63, 118-150`:
F_NEQ_T, EXCLUDED_MIDDLE) and the early `num.py` definitions before
induction is registered (`_IND_SUC_PROPS_PAIR`, `_EXISTS_WITNESS`,
`IND_SUC_NEQ_IND_1`, `NUM_REP_IND_1`, `NUM_REP_IND_SUC_CLOSED`) are
written below the abstraction layer they would need to use. They
will always show up in the escape-hatch lint and don't represent a
missing DSL feature — just the irreducible bottom of the stack.
The lint flags them for completeness; they are not actionable.
