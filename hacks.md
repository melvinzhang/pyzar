# Hacks / Smells in `proof.py` and `tactics.py`

Catalogue of dubious patterns. Each entry: where it lives, why it's a smell, and a proposed fix.

**Status legend:** ✅ fixed · 📝 doc-only · ⏳ pending

| # | Status | Notes |
|---|--------|-------|
| H1 | ✅ | Renamed to `subst_term` in `fc6b43f`; redundant local import removed. |
| H2 | ✅ | `InductionStrategy` registry in `proof.py`; `num.py` registers ℕ-induction at import time. No `from num` in the proof core. |
| H3 | ⏳ | Not addressed. |
| H4 | ✅ | Alpha-aware Abs match in `fc6b43f`. |
| H5 | ✅ | `_term_match` mutates `subst` in place in `fc6b43f`. |
| H6 | ✅ | Frame kinds replaced with `FrameKind` enum; misspellings now fail at parse time. |
| H7 | ✅ | Spec syntax promoted into the Lark grammar via `label_start` / `let_start` rules; new `parse_label` / `parse_let_spec` entry points. |
| H8 | ✅ | `_split_label` commits once `NAME ":"` is recognised by the grammar; body `ParseError` propagates instead of being masked by a whole-spec retry. |
| H9 | ✅ | Cheaper variant: `_namespace_kind` collision check at every registration site (fact / lazy-let / choose-witness / fixed-var). |
| H10 | ✅ | `simp_normalize` no longer wraps `HolError` as `SimpFailure` (`56170d0`). |
| H11 | ✅ | `hyps_added` stores ASSUME theorems INSTed in lockstep with `th`; DISCH/lazy-let-discharge order is no longer load-bearing. |
| H12 | ✅ | `_substitute_carrier` / `_beta_norm_concl` extracted in `fc6b43f`. |
| H13 | ✅ | `assume` registers user surface ASSUME; `term_eq_ant` synthesised at assume-time, lifted into the implication antecedent at frame close. |
| H14 | ✅ | `CHOOSE_WITNESS` factored, `pending_choose` deleted (`3a8d734`). |
| H15 | ⏳ | Asymmetric strictness on fact registry. |
| H16 | ⏳ | `auto_choose` still a positional 6-tuple. |
| H17 | ✅ | Self-tests moved to `tactics_test.py` and `proof_test.py`; `sys.modules` workaround retired. |
| H18 | ✅ | `subst_term` capture-avoiding by construction (`fc6b43f`); kernel `INST` for the Var case. |
| H19 | ⏳ | `_open_cases`'s theorem-only-with-args still undocumented. |
| H20 | ⏳ | `_fresh_label` still uses a collision-prone prefix. |

Plus one issue surfaced during fixes:

**H21. `nat.CHOOSE_GT` / `CHOOSE_LT` rely on the rewriter's under-binder filter.** `eq_u : a = b + (@u. a = b + u)` is non-terminating as an oriented rewrite rule (LHS `a` appears inside RHS's SELECT term), but the OLD `eq_u` came as `ASSUME(body_at_w)` with non-empty `_asl`, so the under-binder filter (`tactics.py:678`, `active = [r for r in rules if not r[3]._asl]`) silently kept it inactive under `@u`. Replacing `ELIM_EX(..., λeq: body_fn(eq, …))` with `CHOOSE_WITNESS(pred, ex)` produced an `eq_u` with `_asl = h_gt._asl = []`, exposing the loop. Reverted at `fc6b43f`. The structural fix is termination-aware rewriting (see H3), not a CHOOSE_WITNESS rollback.

---

## H1. Private `_subst_term` exported across module boundaries  ✅

**Where:** `tactics.py:336` defines `_subst_term`; `proof.py:42` imports it at the top
level and `proof.py:1236` re-imports it locally inside `_Have.by_witness`.

**Smell:** Leading-underscore names are a Python "private API" convention, but
`_subst_term` is freely consumed by another module — twice. The naming is
lying about the contract.

**Fix:** Rename to `subst_term` and export it as a first-class helper from
`tactics.py`. Drop the redundant local import in `by_witness`.

---

## H2. Lazy local imports from `num` to dodge a circular dependency  ✅

**Where:** `proof.py:469` (`from tactics import UNFOLD` — duplicate of top-level),
`proof.py:778` (`from num import ONE`), `proof.py:793` (`from num import mk_suc`),
`proof.py:1236` (`from tactics import _subst_term` — see H1),
`proof.py:1467` (`from num import INDUCT_PROVE`).

**Smell:** Five intra-method imports, all because `num` imports from `proof`
(via `@proof`). The induction/base/step machinery is hard-wired to the
naturals (`ONE`, `mk_suc`, `INDUCT_PROVE`), so the DSL leaks a domain
dependency. The `from tactics import UNFOLD` and `from tactics import
_subst_term` cases are pure code-smell duplicates of the top-level imports.

**Fix:** Either (a) parameterise the induction context on a "successor / base
constant / induction principle" triple registered by `num.py`, breaking the
cycle structurally; or (b) move `INDUCT_PROVE` and the SUC/ONE constants to
a shared lower-level module that both `proof` and `num` can import. Then
collapse the duplicate `tactics` imports.

---

## H3. Iteration-bounded termination guards (`SIMP_ROOT_FIRE_LIMIT` / `SIMP_OUTER_PASS_LIMIT`)

**Where:** `tactics.py:565-566` defines the magic numbers `256` and `64`;
`tactics.py:690-700` and `tactics.py:705-720` use them.

**Smell:** Soft kill switches stand in for a real termination argument. The
comment ("any well-formed terminating rule set should finish well below
them") admits as much. Bumping them is documented as the wrong answer, but
nothing prevents it.

**Fix:** Track the multiset/size measure of the current term across rewrite
fires; bail when it stops strictly decreasing for a rule whose RHS is not
syntactically smaller. Or, at minimum, push the limits into a configurable
context object so test code can dial them down to catch regressions early.

---

## H4. `_term_match` Abs case is name-rigid, not alpha-aware  ✅

**Where:** `tactics.py:630-633`.

**Smell:** The matcher explicitly requires `pat.bvar.name == tgt.bvar.name`,
which is *stricter* than alpha-equivalence — `\x. body` vs `\y. body[y/x]`
fails to match even though they are alpha-equal. The module docstring claims
"Lambdas in patterns must alpha-match exactly", but the code under-delivers.

**Fix:** Either (a) honestly document that lambda matching is name-literal
(rename the file's claim); or (b) alpha-rename one side to the other's bvar
before recursing. The latter restores alpha-soundness.

---

## H5. `_term_match` copies the substitution dict on every var bind  ✅

**Where:** `tactics.py:619` (`s = dict(subst); s[pat] = tgt`).

**Smell:** First-order matching does an O(n) dict copy per match step, so
matching a pattern with `k` variables against a tree of size `m` costs
O(k·m·n) where n is the running substitution size. Fine for tiny rule sets,
quadratic-ish on large ones.

**Fix:** Mutate `subst` in place and undo on backtrack. Or use a persistent
trie / linked alist. Simpler still: since matching either succeeds or
fails monotonically (no real backtracking happens — the recursion is
deterministic per node), just mutate without copying.

---

## H6. Inconsistent frame-`kind` naming  ✅

**Where:** `proof.py` uses `"root"`, `"_induction"`, `"_cases"` (underscore-
prefixed), but also `"ind_base"`, `"ind_step"`, `"case"`, `"have_proof"`,
`"suppose"` (no underscore).

**Smell:** Mixed conventions for "internal-only" vs "user-facing" frame
kinds. Readers cannot tell at a glance which kinds are visible from the
public DSL.

**Fix:** Replaced the magic strings with a `FrameKind` enum
(`ROOT`, `INDUCTION`, `IND_BASE`, `IND_STEP`, `CASES`, `CASE`, `HAVE_PROOF`,
`SUPPOSE`). Misspellings now raise `AttributeError` at the use site instead
of silently never matching. The `__str__` override preserves the original
value strings for the `_SubFrameCtx.__exit__` error message.

---

## H7. Mini-DSL parsing via three regexes (`_LABEL_RE`, `_LET_SPEC_RE`, `_LET_ARG_RE`)  ✅

**Where:** `proof.py:502-510`.

**Smell:** The DSL grammar (`"label: term"`, `"NAME(arg1:ty, arg2) := body"`) is
defined by three ad-hoc regexes scattered through one class. Edge cases —
nested colons in a term, paren-balance inside the args list, type
annotations with arrows — quickly outgrow what regex can handle. Already
visible in `_split_label` (H8) where the regex misclassifies and falls
back.

**Fix:** Spec syntax is now first-class in `parser.py`'s Lark grammar.
Two new start rules — `label_start: NAME ":" term | term` and
`let_start: NAME "(" arglist ")" ":=" term` — share the existing `term`
production, so binders / nested colons / parens / type annotations are
handled by the kernel grammar instead of duplicated regex logic. New
public entry points `parse_label` / `parse_let_spec` wrap them; the
`_Builder` visitor returns `(label, term)` and `(name, [Var], body)`
respectively, with body parsed in scope of the args. Lark errors are
re-wrapped as `ParseError` so callers don't need to know about lark.

A single small regex remains (`Proof._peel_label`) for the deferred-
parse case in `choose()`, where the body must be parsed only after the
witness term is computed and bound under the label name; eager
`parse_label` doesn't fit that flow.

---

## H8. `_split_label` swallows the real parse error  ✅

**Where:** `proof.py:519-527`.

**Smell:** When the label-form regex matches but the body fails to parse,
the function silently retries the *whole* spec as a term. Genuine typos in
label-form specs (e.g. `"hxy: x ?? y"`) get reported against the wrong
syntactic interpretation, hiding the original `ParseError` and producing a
confusing error.

**Fix:** Folded into H7. With `label_start` as a Lark production, the
parser commits to label form as soon as it sees ``NAME ":"`` — there's
no fallback path, so a body-level `ParseError` reaches the caller
verbatim. ``"hxy: x ?? y"`` now reports the unexpected ``?`` against
the `x ?? y` body, exactly where the typo lives.

---

## H9. String overloading in `coerce` and `by_select`  ✅

**Where:** `proof.py:552-584` (`coerce` walks `accept` in order; same string
may be a fact label or a parseable term);
`proof.py:1128-1140` (`by_select` resolves a string as let-name → fact-label
→ parseable term).

**Smell:** Whether `"x"` means "fact named x", "lazy-let named x", or "the
variable term x" depends on which scopes happen to be populated. Add a fact
called `x` later and an existing `by_select(..., "x")` silently changes
meaning.

**Fix (cheaper variant).** Collisions now fail at the *write* side:
``Proof._namespace_kind`` walks fact labels, lazy-let carriers, choose
witnesses, and fixed vars; ``_require_fresh_name`` is called at every
registration point (`_register_fact`, `_register_lazy_let`, `fix`,
`choose`, `case` auto-witness). Two different kernel values can no
longer share a name, so later ``coerce`` lookups have an unambiguous
source regardless of resolution order.

``type_env`` is intentionally outside the collision set: it carries
*type hints* for variable names that ``fix`` later realises (e.g.
``goal(types={"p": pred_ty})`` then ``fix("p")``). The hint and the
realised Var are the same identifier, not two competing values.

---

## H10. `simp_normalize` wraps every `HolError` as `SimpFailure`  ✅

**Where:** `proof.py:217-222`.

**Smell:** Any kernel-level `HolError` raised inside `_unfold_walk` (a
genuine bug — type mismatch, malformed equation, …) is rewrapped as
`SimpFailure` and downstream `simp_match` treats it as "no match, move on"
(`proof.py:330-336`). Real bugs become silent unification failures.

**Fix:** Distinguish "rewriter ran clean but found nothing" (a non-error
return value) from "rewriter blew up" (propagate). Use a sentinel return
or a dedicated `SimpNoProgress` rather than catching the broad `HolError`.

---

## H11. `_close_frame`'s discharge order is an implicit invariant  ✅

**Where:** `proof.py:_close_frame`.

**Smell:** The docstring spells out the order — DISCH, then lazy-let
discharge, then GEN — and warns that swapping any two will break specific
scenarios. The DISCH-vs-lazy-let-discharge swap is the silent one (`DISCH`
always succeeds at the kernel level regardless of whether `term` is in
`_asl`); the GEN-too-early swap is caught by `ABS`'s "var free in hyp"
check, but the silent one is not.

**Why an obvious fix doesn't work.** The first attempt was to assert "term
must be in `th._asl` before DISCH'ing it." But DISCH is also valid when
the user's proof didn't use the assumption, so the assertion rejects
legitimate proofs. The `Status: 📝` row records that result.

**Proper fix (correct by construction).** The fundamental issue is that
`hyps_added` stores the user's surface-form term, which may mention lazy-let
carriers; lazy-let discharge then INSTs those carriers everywhere *except*
in the saved term, leaving DISCH stranded. To make the order
non-load-bearing, keep the saved term in lockstep with `th` through every
substitution.

Concrete design:

1. Change `hyps_added` to store the *registered ASSUME theorem*, not the
   raw term (i.e. `(label, ASSUME(term))` instead of `(label, term)`).
2. In `_substitute_carrier`, when INSTing the carrier in `th`, INST the
   same substitution into every saved ASSUME theorem too. This keeps each
   saved hyp's `_concl` synchronised with `th._asl`.
3. After the loop in `_discharge_lazy_lets`, every saved ASSUME's `_concl`
   matches its corresponding entry in `th._asl` exactly.
4. Now DISCH and lazy-let discharge commute: pulling each saved theorem's
   `_concl` and DISCHing it works regardless of whether INST has run yet.
5. The `_close_frame` body becomes a single ordering — but the order no
   longer carries soundness consequences, only ergonomic ones (you'd
   probably still discharge in registration order for legibility).

This eliminates the silent-failure mode entirely: there is no more
"term shape diverged from `_asl` shape" because the data structure
guarantees they evolve together. The mechanical cost is one extra
`INST` per saved ASSUME per lazy-let discharge — proportional to the
existing work, no asymptotic change.

---

## H12. `materialize_let` and `_discharge_lazy_lets` duplicate the same lambda-build / INST / PROVE_HYP / BETA_NORM choreography  ✅

**Where:** `proof.py:277-303` vs `proof.py:389-425`.

**Smell:** Both functions:
1. Build `\args. body` from the let.
2. `INST([(abs_body, lz.carrier)], th)`.
3. Construct the equation hypothesis via `BETA_NORM(mk_app(abs_body, *bvars))` then `GEN`.
4. `PROVE_HYP` it out.
5. Beta-normalise the conclusion.

Two implementations of the same five steps. Diverging copies are a
known maintenance hazard.

**Fix:** Extract `_substitute_carrier(lz, th)` returning a clean theorem
and call it from both sites. `_discharge_lazy_lets` becomes a fold over
the frame's lets in reverse registration order.

---

## H13. `assume` silently swaps the registered fact's shape  ✅

**Where:** `proof.py:Proof.assume`.

**Smell:** The user writes `p.assume("h: folded_form")`; `_simp_require`
validates that `folded_form` matches the implication's antecedent `ant`.
But the registered fact is `ASSUME(ant)`, not `ASSUME(term)` — so
`p.fact("h")` returns a theorem whose conclusion is the *unfolded* shape
the user did not write. That difference can confuse later tactics (or the
user reading their own proof).

**Why the obvious fix doesn't work.** Registering `ASSUME(term)` (the
user's surface form) keeps `p.fact("h")` consistent with the spec, but it
breaks frame close: `hyps_added` would store `term` and `_close_frame`
would DISCH that, producing `term ==> remaining_goal`. The original goal
was `ant ==> remaining_goal`, so the kernel-aconv check at the end of
`_SubFrameCtx.__exit__` rejects the result. Going from `term ==> ...`
to `ant ==> ...` requires a kernel rewrite step that the simple "register
the surface form" fix doesn't include.

**Proper fix (correct by construction).** Keep the user's surface form on
the fact registry *and* synthesise the simp equation between the two
shapes once, at `assume` time, then use that equation at `_close_frame`
to lift the resulting implication.

Concrete design:

1. At `assume("h: term")` time, compute `term_eq_ant : |- term = ant`
   (one direction of `simp_normalize` between the two shapes — both go
   to the same normal form, so this falls out of `simp_match`'s
   internals).
2. Register `ASSUME(term)` as the fact (preserves user surface form for
   `p.fact("h")`).
3. Store `(label, term, term_eq_ant)` in `hyps_added` (was
   `(label, term)`).
4. In `_close_frame`, after `DISCH(term, th)` (which produces
   `... |- term ==> concl`), build the corresponding implication
   equation: `imp_eq : |- (term ==> concl) = (ant ==> concl)` via
   `MK_COMB(AP_TERM(==>, term_eq_ant), REFL(concl))`. Then
   `EQ_MP(imp_eq, th)` rewrites the implication's antecedent to the
   kernel form. The resulting theorem matches the original goal.

The user always sees their surface form when they look up the fact;
the kernel-form `ant` only appears in the final closed theorem (where
it was always going to live anyway, since it came from the goal). No
shape-swapping, no surprise — the asymmetry is gone.

The mechanical cost is one extra `MK_COMB` + `EQ_MP` per assumed hyp at
frame close, only when `term ≠ ant` (kernel-aconv check skips the
equation build in the common case).

---

## H14. `pending_choose` discharge uses `lambda _: th`, relying on hyp-set merging  ✅

**Where:** `proof.py:182-189`.

**Smell:** `ELIM_EX(pred, hyp_ex, body_fn)` calls `body_fn(ASSUME(body_at_w))`
expecting the caller to use that fact. The pending-choose discharge ignores
the argument (`lambda _: th`) because `th`'s `_asl` already contains
`body_at_w` from the earlier `ASSUME` registered under `{name}_eq`. Soundness
hinges on that inclusion holding identically — a future `ELIM_EX` refactor
that switches to a fresh ASSUME would silently leave the original `body_at_w`
hypothesis floating in the result.

**Fix:** Have `_set_frame_result` actually thread `body_fn`'s argument
through `PROVE_HYP(arg, th)` so the dependency on shared hyp-set identity
becomes explicit.

---

## H15. `_register_fact` raises on duplicates; `_drop_facts` silently ignores missing labels

**Where:** `proof.py:538-550`.

**Smell:** Asymmetric strictness. `_register_fact` is fail-fast; `_drop_facts`
uses `pop(label, None)`. The asymmetry hides bugs — if a frame's
`facts_added` ever mentions a label that's already gone, we'll never know.

**Fix:** Make both fail-fast (`del self._facts[label]`), or both lenient,
and pick whichever the invariants actually need. The natural answer is
fail-fast: `facts_added` should always be a subset of `_facts` at frame
exit.

---

## H16. `auto_choose` is a 6-tuple stuffed into the generic `_SubFrameCtx`

**Where:** `proof.py:1003-1009` builds it; `proof.py:1407-1415` consumes it.

**Smell:** Every sub-frame carries an optional `auto_choose` slot, used by
exactly one caller (`case()` for an existential leaf). The 6-tuple is
positionally unpacked, with no dataclass or named-tuple to anchor the
shape.

**Fix:** Either (a) lift the auto-choose plumbing out of `_SubFrameCtx` —
have `case()` push the witness/equation onto the new frame after entering
it, the same way `extra_facts` does; or (b) at minimum, make the tuple a
`_AutoChoose` `dataclass` so the field names are visible at the use site.

---

## H17. Self-tests live inside the module bodies  ✅

**Where:** `tactics.py:886-905`, `proof.py:1615-1924`.

**Smell:** `proof.py`'s `_selftest` is over 300 lines and pulls in `nat`,
`num`, `parser`, `fusion` directly. Failure noise dumps into module import
output rather than into a test runner. The module is harder to read because
the second half is fixtures.

**Fix:** Move the bodies of `_selftest` into `tests/test_tactics.py` /
`tests/test_proof.py`. Keep the `if __name__ == "__main__":` shim if you
want `python proof.py` to keep working — have it call into the test module.

---

## H18. `_subst_term` is capture-unsafe but exposed as a utility  ✅

**Where:** `tactics.py:336-351`.

**Smell:** The function does literal term substitution under binders; if
`old` becomes captured by an inner `Abs` whose `bvar` clashes with a free
variable of `new`, the result is unsound. Current call sites avoid this by
construction (replacing fresh witnesses or fix-vars), but the function is
re-imported (H1) and treated as a public-ish helper, so it could grow
unsafe call sites.

**Fix:** Rename to `_subst_term_capture_unsafe`, or implement
capture-avoidance via `variant` on the fly. The kernel already has the
machinery to do this safely (cf. `INST`).

---

## H19. `_open_cases` accepts theorem-only when args are supplied — undocumented in the public API

**Where:** `proof.py:873-892`. `cases_on(ref, *args)` and `by_cases(ref, *args)`
both delegate.

**Smell:** Public methods say nothing about the constraint; you only learn
about it from a `HolError` at runtime: "spec args require a theorem
source". A user who passes a fact label and args gets a confusing message.

**Fix:** Either widen the implementation to accept fact labels (resolving
to a theorem before `MP_LIST`), or document the constraint in the public
docstrings of `cases_on` / `by_cases`. The first is essentially a one-
line change (`ref = self._resolve_fact(ref)`).

---

## H20. `_fresh_label` namespace can collide with user labels

**Where:** `proof.py:529-534`.

**Smell:** Anonymous facts are named `_h1`, `_h2`, …. Nothing reserves the
`_h<digits>` prefix; a user who writes `p.have("_h7: …")` either collides
silently (different anonymous index) or shadows. The check
`if name not in self._facts` only avoids active collisions, not future
ones if `_drop_facts` clears one out.

**Fix:** Use a prefix that's syntactically illegal as a user label — e.g.
`"#h7"` — and have the parser refuse `#`-prefixed labels. Or carry a
session-unique counter that's never recycled, and refuse user labels
matching the generated pattern.
