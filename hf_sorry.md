# Order of attack — HF Gödel-I `sorry()` plan

This document is primarily the plan for the nine `p.sorry()` calls in
`hf_repr_thms.py`. The full HF Gödel-I path also has nine additional
`p.sorry()` calls in `hf_godel1.py`; those are listed here as downstream
work, but the detailed inventory below is file-local to `hf_repr_thms.py`.

The plan is ordered to settle the greatest unknown first. At the moment
that unknown is not the substitute trace machinery; it is whether the
intended `Prov_HF_internal` / `Proof_HF_internal` encoding matches the
current external `Proof_HF` representation.

## Inventory

| # | Theorem                          | Line | Est. size  | Depends on (sorry)        | Depends on (other)                                          |
|---|----------------------------------|-----:|-----------:|---------------------------|-------------------------------------------------------------|
| A | `HF4_INST`                       | 1373 | ~600 lines | —                         | `_prov_of_hf_axiom`, `PROV_HF_UI`, substitute reductions    |
| B | `QUOTE_HF_NEQ_FROM_LOW_BIT`      | 1420 | ~150 lines | A                         | `HF2`/`HF3_INST`, canonical-form lemmas, `LOW_BIT_LT`        |
| C | `QUOTE_HF_NEQ_FROM_CLEAR_LOW`    | 1451 | ~150 lines | A                         | same as B                                                    |
| D | `IS_SUBSTITUTE_STEP_REPRESENTS`  | 2699 | ~150 lines | —                         | `IS_IN_REPRESENTS` (✓), `IS_PAIR_ORD_REPRESENTS` (✓), `QUOTE_HF_AT_PAIR_ORD` (✓), HF1–HF3 (✓); **body of `is_substitute_step_internal`** |
| E | `IS_SUBSTITUTE_TRACE_REPRESENTS` | 2740 |  ~80 lines | D                         | `HF_INDUCTION` (✓); **body of `is_substitute_trace_internal`** |
| F | `SUBSTITUTE_REPRESENTS`          | 2772 |  moderate  | E                         | `TRACE_EXISTS` (✓); **body of `substitute_internal`**       |
| G | `PROV_HF_REPRESENTS`             | 2850 | large      | F                         | Σ₁ completeness (forward) — Σ₁ soundness deferred to Stage 6; **body of `Prov_HF_internal`** |
| H | `IS_FORM_PROV_HF_INTERNAL`       | 2863 | small      | G's body def              | `is_form` closure under HF-formula constructors             |
| I | `FREE_IN_PROV_HF_INTERNAL`       | 2875 | small      | G's body def              | `free_in` recursion                                          |

✓ = already proven and exported (no sorry).

Two implementation clusters plus one design gate:

* **Design gate: internal proof predicate.** The notes below used to say
  `mem_l_internal` "collapses to `In_a`" because proof lists are HF sets.
  That is only true after a refactor. The current external proof objects
  are `cons_l` lists (`cons_l h t = Pair_ord (SUC0 0) (Pair_ord h t)`),
  and `mem_l` is a recursive list predicate, not HF set membership.

* **Canonical-form/quote_hf cluster (A → B, C).** Closes the residual gap
  inside `QUOTE_HF_PROV_NEQ` (the `s≠0 ∧ t≠0` branch).
* **Representability cluster (D → E → F → G; H, I attached to G).**
  Builds the Stage-3C/3D `…_REPRESENTS` chain consumed by the diagonal
  lemma in `hf_godel1.py`.

The two proof clusters are mostly separable, but the no-sorry dependency
graph is stricter than the previous version of this note claimed:
`IS_SUBSTITUTE_STEP_REPRESENTS` uses `IS_IN_REPRESENTS`, and
`IS_IN_REPRESENTS` calls `QUOTE_HF_PROV_NEQ`. Since `QUOTE_HF_PROV_NEQ`
still contains the A/B/C residual branch, A/B/C are latent prerequisites
for a fully closed substitute-representability chain.

## Recommended order

### Phase 0 — settle `Prov_HF_internal` / `Proof_HF_internal` design

Do this first, before investing in hundreds of lines of substitute-trace
proof code. The current plan for G says:

```text
mem_l_internal collapses to In_a
valid_step_internal mirrors valid_step
Proof_HF_internal is a bounded conjunction over members
```

That is a plausible plan only if proof objects are represented as HF
sets. The current external checker in `hf_repr_core.py` uses `cons_l`
lists and recursive `mem_l`. Pick one path:

1. **Refactor external `Proof_HF` to HF-set proof objects.**
   Then `mem_l_internal = In_a` is honest, and the bottom-up internal
   proof predicate can be as simple as the current comments suggest.
   This is a larger refactor but may shrink Stage 3D substantially.

2. **Keep current `cons_l` proof objects.**
   Then define real internal formulas for `mem_l`, `valid_step`,
   `Proof_HF`, and `Prov_HF` over the `cons_l` encoding. This avoids a
   refactor but means the "HF sets make lists free" shortcut is false.

Exit criterion for Phase 0: a tiny no-sorry prototype that demonstrates
the chosen encoding. Good prototypes:

* If refactoring to HF-set proof objects: prove the axiom-only proof
  witness is internally recognised.
* If keeping `cons_l`: define `mem_l_internal` and prove the internal
  cons case corresponding to `mem_l (cons_l h t) x = (x = h \/ mem_l t x)`.

Until this is done, G is the highest-risk item in the whole HF G1 plan.

### Phase 1 — canonical-form quote_hf inequality (close `QUOTE_HF_PROV_NEQ`)

Close this before claiming the substitute representability chain is
fully no-sorry. `IS_IN_REPRESENTS` already exists, but it depends on
`QUOTE_HF_PROV_NEQ`, whose nonzero/nonzero branch is still closed by the
A/B/C sorries.

1. **A — `HF4_INST`** (~600 lines).
   - Mechanical extension of `HF2_INST`/`HF3_INST` template: two
     `PROV_HF_UI` steps + substitute reductions through the body's
     `∀z` + encoded-iff. Tedious, not deep.
   - Tax/value ratio is poor, but it removes the hidden sorry under
     `IS_IN_REPRESENTS`.

2. **B — `QUOTE_HF_NEQ_FROM_LOW_BIT`** and
   **C — `QUOTE_HF_NEQ_FROM_CLEAR_LOW`** (~150 lines each).
   - Symmetric uses of A + canonical-form (`LOW_BIT_CLEAR_LOW_PRECOND`)
     to lift bit-component inequalities to whole-`quote_hf`
     inequalities. B and C can be done in parallel after A.

### Phase 2 — `substitute` representability

With Phase 0 settled and the `IS_IN_REPRESENTS` dependency really clean,
this cluster becomes mostly local proof engineering: define the three
HF-formula bodies and walk the resulting Σ₀/Σ₁ structure.

3. **D — `IS_SUBSTITUTE_STEP_REPRESENTS`**
   - First define the body of `is_substitute_step_internal` in
     `hf_repr_core.py` as a 9-disjunction `Or_f`-chain mirroring the
     HOL `is_substitute_step` cases, with `In_a (Pair_ord_q …) var_T`
     for trace-membership clauses.
   - Then case-split on `IS_SUBSTITUTE_STEP_DEF`'s 9 disjuncts; each
     case dispatches one HF-disjunct via `IS_PAIR_ORD_REPRESENTS` /
     `IS_IN_REPRESENTS` / `QUOTE_HF_AT_PAIR_ORD` and walks HF1–HF3.
   - **Risk:** the body shape is a design choice; pick it once and
     keep all downstream reductions consistent. Expect to revisit
     once if E/F surface a friction.

4. **E — `IS_SUBSTITUTE_TRACE_REPRESENTS`**
   - Define `is_substitute_trace_internal` body.
   - HF_INDUCTION on the Insert-tower of `T`; per-element step
     discharges via D.

5. **F — `SUBSTITUTE_REPRESENTS`**
   - Define `substitute_internal := ?T. is_substitute_trace T F t v r`.
   - Existence supplied by `TRACE_EXISTS`; uniqueness supplied at
     numerals by determinism of `is_substitute_trace`.

After Phase 2, the diagonal-lemma path is unblocked end-to-end at the
substitute layer.

### Phase 3 — provability representability

6. **G — `PROV_HF_REPRESENTS`** (the deepest semantic step).
   - Define `Prov_HF_internal(x) := ?_internal y. Proof_HF_internal(y, x)`.
     The shape of `Proof_HF_internal` must follow the Phase 0 decision:
     either HF-set proof objects with `In_a`, or current `cons_l` proof
     objects with an internal `mem_l`.
   - **Forward direction** (HOL ⇒ HF): Σ₁ completeness for HF.
     Extract a `Proof_HF` witness via `PROV_HF_AT`, encode as
     HF-numeral, verify each conjunct as a closed Σ₀ fact.
   - **Backward direction** (HF ⇒ HOL): Σ₁ soundness — explicitly
     deferred to Stage 6 (HF |= HF1–HF5 via the model construction).
     If needed, split the current iff into forward/backward named
     lemmas so the Stage-6 dependency is not hidden inside one giant
     theorem.

7. **H — `IS_FORM_PROV_HF_INTERNAL`** and
   **I — `FREE_IN_PROV_HF_INTERNAL`**.
   - Both routine once `Prov_HF_internal` has a body: walk the
     formula recursion using `IS_FORM_AT_*` and the `free_in`
     definition. Discharge in parallel with each other.

## Why this order

* **Phase 0 first** because it can invalidate the current comments for
  G. If the proof-object representation is wrong, substitute-trace work
  still helps, but it will not close the headline G1 path.
* **Phase 1 next** because it removes the hidden `IS_IN_REPRESENTS` /
  `QUOTE_HF_PROV_NEQ` dependency under D and E.
* **Phase 2 after that** because it is high-leverage and comparatively
  local once the `IS_IN_REPRESENTS` dependency is genuinely clean.
* **Phase 3 last** because G carries the deepest semantic content and
  depends on both F and the Phase 0 design decision; H/I are cheap
  follow-ups triggered by the chosen `Prov_HF_internal` body.

## Downstream `hf_godel1.py` sorries

After `hf_repr_thms.py` is no-sorry, the remaining G1 work is in
`hf_godel1.py`:

| Theorem | Role | Depends on |
|---|---|---|
| `DIAG_REPRESENTS` | diag relation existence | `SUBSTITUTE_REPRESENTS`, numeral/internal composition |
| `IS_FORM_DIAG_INTERNAL` | diagonal side condition | body of `diag_internal` |
| `FREE_IN_DIAG_INTERNAL` | diagonal side condition | body of `diag_internal` |
| `DIAG_FUNCTIONAL` | uniqueness/functionality | `SUBSTITUTE_REPRESENTS`, equality reasoning |
| `VAR_X_NEQ_SUC0_0` | concrete side condition | tag/numeral disjointness |
| `VAR_Y_NEQ_VAR_X` | concrete side condition | `VAR_T_INJ`, numeral inequality |
| `SUBSTITUTE_FREE_NO_OP` | substitution bookkeeping | structural induction on formulas |
| `FREE_IN_SUBSTITUTE_AT_DIFFERENT_VAR` | substitution bookkeeping | structural induction on formulas |
| `DIAGONAL_LEMMA` | headline fixed point | all of the above plus `PROV_HF_REPRESENTS` side conditions |

Do not start this block until the Phase 0 decision and at least F/H/I
are settled; otherwise the diagonal lemma will keep chasing moving
definitions.

## Execution log and implementation notes

* **Connectives lifted (done)** — `And_f` / `Or_f` / `Iff_f` /
  `Exists_f` and their `_AT` rewrite + `SUBSTITUTE_AT_*` distribution
  lemmas now live in `hf_connectives.py` (loaded between
  `hf_syntax` and `hf_repr_core`). `hf_godel1.py` re-imports them.
  This unblocks the outer logical scaffolding of the
  `is_*_internal` bodies.

* **Prerequisite for D — Python builders for godelnum shapes.**
  The body of `is_substitute_step_internal` needs to express
  godelnum-shape claims like ``a = Var_t v`` in HF formulas with
  `var_z` as a free leaf. Writing this as `Eq_f var_a (Var_t var_z)`
  does **not** work: `substitute` treats `Var_t k` as a leaf
  (HIT/MISS on the index `k = var_z` = `Var_t (SUC0² 0)`), so it
  never pushes the substitute into `var_z`. The fix is to write
  bodies that mention only `Insert_t` / `Empty_t` in subject-term
  position — `substitute` already pushes through those via
  `SUBSTITUTE_AT_INSERT` / `_EMPTY`, reaching the leaf placeholders.

  Implement as **Python builders** (no new HOL constants, no new
  lemmas): a small module of helper functions emitting the right
  Insert_t-tower term at body-construction time.

  ```python
  def _quote_nat(n):
      t = Empty_t
      for _ in range(n):
          t = mk_app(Insert_t, t, t)         # von Neumann successor
      return t

  def Q_pair_ord(a, b):
      sing_a  = mk_app(Insert_t, a, Empty_t)
      pair_ab = mk_app(Insert_t, a, mk_app(Insert_t, b, Empty_t))
      return mk_app(Insert_t, sing_a, mk_app(Insert_t, pair_ab, Empty_t))

  def Q_var_t(idx):       return Q_pair_ord(_quote_nat(2),  idx)
  def Q_eq_f(a, b):       return Q_pair_ord(_quote_nat(5),  Q_pair_ord(a, b))
  def Q_not_f(phi):       return Q_pair_ord(_quote_nat(6),  phi)
  def Q_imp_f(a, b):      return Q_pair_ord(_quote_nat(7),  Q_pair_ord(a, b))
  def Q_forall_f(n, phi): return Q_pair_ord(_quote_nat(8),  Q_pair_ord(n, phi))
  def Q_insert_t(a, b):   return Q_pair_ord(_quote_nat(9),  Q_pair_ord(a, b))
  def Q_in_a(a, b):       return Q_pair_ord(_quote_nat(10), Q_pair_ord(a, b))
  ```

  Bodies are then constructed in Python like
  ``Q_eq_f(var_a, Q_var_t(var_z))`` and substitute walks them
  end-to-end via `SUBSTITUTE_AT_INSERT` alone. ~30 lines of Python
  helpers; **zero kernel-side overhead**. The IS_PAIR_ORD_INTERNAL
  precedent already does this manually with literal Insert_t-towers
  — the helpers just package what's already in the codebase.

  Tradeoff: theorem statements print with the body fully expanded
  into Insert_t/Empty_t towers (verbose). Downstream consumers cite
  `is_substitute_step_internal` as a constant and never need to see
  the expansion, so the cost is one-time at definition.

## Notes per step (pitfalls to flag now)

* **D**: the choice of `Or_f`-chain order is consumed verbatim by
  E, F, and (indirectly) G. Pick it once, document the convention
  near the body definition. The Q-builder shape is fixed by the
  godelnum tag table (`Var_t`=2, `Eq_f`=5, …, `In_a`=10) so no
  design choice there.
* **F**: `?T. is_substitute_trace …` uses Hilbert ε at the HF level.
  Verify uniqueness of the trace at numerals (determinism of
  `is_substitute_trace`) before relying on the ε-elim.
* **G**: keep the forward/backward split explicit — only forward
  direction is in scope for this file; backward gets a parked
  Stage-6 citation, not a sorry-on-sorry.
* **A**: when extending the `HF2_INST`/`HF3_INST` template, the
  encoded-iff `Not_f (Imp_f (Imp_f …) (Not_f (Imp_f …)))` is the
  shape that lengthens the substitute-reduction tail; budget for
  one full `Imp_f`-tower walk per layer.
