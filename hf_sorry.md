# Order of attack — HF Gödel-I `sorry()` plan

This document is primarily the plan for the `p.sorry()` calls in
`hf_repr_thms.py`. The active quote path is the measured mutual
membership/inequality induction; the old HF-IND quote spike and global
low-bit quoted-inequality route have been removed from
`hf_repr_thms.py`. The full HF Gödel-I path also has
additional `p.sorry()` calls in `hf_godel1.py`; those are downstream
work, but the detailed inventory below is file-local to `hf_repr_thms.py`.

The plan is ordered to settle the greatest unknown first. The switch is
now decided: `Prov_HF_internal` must use HF-native proof objects, not
`cons_l` lists. The HF-set proof-object shape is pinned, and `Prov_HF`
has been redirected to the set-native checker.

## Inventory

| # | Theorem                          | Line | Est. size  | Depends on (sorry)        | Depends on (other)                                          |
|---|----------------------------------|-----:|-----------:|---------------------------|-------------------------------------------------------------|
| A | `HF4_INST`                       | 1400 | done       | —                         | `_prov_of_hf_axiom`, `PROV_HF_UI`, substitute reductions    |
| B | `QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES`  | active | small/med | — | bit top-difference layer |
| C | `QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES` | active | small/med | — | symmetric bit top-difference layer |
| D | `QUOTE_HF_MUTUAL_MEASURED`       | active | med/large  | B, C                      | three object-level HF1/HF2/HF3 branch bridges               |
| E | `QUOTE_HF_MEM_DECISION`          | done   | done       | D                         | final unbounded projection from measured theorem             |
| F | `IS_SUBSTITUTE_STEP_REPRESENTS`  | active | ~150 lines | E                         | `IS_PAIR_ORD_REPRESENTS` (✓), `QUOTE_HF_AT_PAIR_ORD` (✓), HF1–HF3 (✓); **body of `is_substitute_step_internal`** |
| G | `IS_SUBSTITUTE_TRACE_REPRESENTS` | active |  ~80 lines | F                         | `HF_INDUCTION` (✓); **body of `is_substitute_trace_internal`** |
| H | `SUBSTITUTE_REPRESENTS`          | active |  moderate  | G                         | `TRACE_EXISTS` (✓); **body of `substitute_internal`**       |
| I | `PROV_HF_REPRESENTS`             | active | large      | H                         | Σ₁ completeness (forward) — Σ₁ soundness deferred to Stage 6; **body of `Prov_HF_internal`** |
| J | `IS_FORM_PROV_HF_INTERNAL`       | active | small      | I's body def              | `is_form` closure under HF-formula constructors             |
| K | `FREE_IN_PROV_HF_INTERNAL`       | active | small      | I's body def              | `free_in` recursion                                          |

✓ = already proven and exported (no sorry).

Two implementation clusters plus one representation switch:

* **Representation switch: HF-native proof objects.** The internal
  proof predicate will not encode list theory in HF. The previous
  `hf_repr_core.py` list checker has been removed from the active core;
  `Prov_HF` and `Prov_HF_internal` now target ranked HF-set proof
  objects.

* **Quote layer pivot.** The preferred route no longer makes global
  quoted inequality the blocking induction theorem. The target
  interfaces are membership decision and global quoted inequality,
  both projected from the measured mutual theorem:

  ```text
  QUOTE_HF_MEM_DECISION
  |- !x y.
     (In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y)))
     /\
     (~In x y ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y))))

  QUOTE_HF_PROV_NEQ
  |- !s t. ~(s = t)
     ==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))
  ```

  The previous membership-IND spike was negative: the branch-specific
  object formulas are not membership-inductive enough to close the quote
  interface directly. That code has been removed from `hf_repr_thms.py`.

  The active quote proof is the meta-level measured
  mutual induction:

  ```text
  QUOTE_HF_MUTUAL_MEASURED
  ```

  This is the bigger unknown because it must show that every recursive
  membership/inequality call is below the current measure. The theorem
  now uses the strong IH non-circularly; remaining sorries are the local
  object-level branch bridges and the two extensional-witness decrease
  helpers, not the induction shape itself.
* **Removed legacy quote cluster.** The old proof path through
  `QUOTE_HF_NEQ_FROM_LOW_BIT` / `QUOTE_HF_NEQ_FROM_CLEAR_LOW` /
  direct global induction is gone from `hf_repr_thms.py`;
  `QUOTE_HF_PROV_NEQ` has been reintroduced only as a projection from
  the measured mutual theorem.
* **Representability cluster (D → E → F → G; H, I attached to G).**
  Builds the Stage-3C/3D `…_REPRESENTS` chain consumed by the diagonal
  lemma in `hf_godel1.py`.

The active no-sorry dependency graph factors through the measured mutual
theorem once its local branch bridges are discharged.

## Recommended order

### Phase 0 — switch to HF-native proof objects

Do this first, before investing in hundreds of lines of substitute-trace
proof code. The target for G is:

```text
Prov_HF_internal(x) := ?P. Proof_HF_set_internal(P, x)
```

where `P` is an HF-native proof object. Do **not** internalise
`cons_l`, `mem_l`, `append_l`, or list recursion.

The Phase 0 prototype has pinned the shape to ranked proof-step sets.
For reference, the viable HF-native designs were:

1. **Ranked proof-step set.**
   `P` is a finite HF set of records `(rank, formula)`. A step at rank
   `k` is valid if it is an axiom, or follows by MP/Gen from records
   in `P` whose ranks are strictly below `k`. This keeps membership as
   `In_a` while preserving the well-founded "earlier step" relation.

2. **Proof tree.**
   `P` is a finite HF tree whose root formula is `x`; children are the
   immediate subproofs for MP/Gen. This avoids global step membership,
   but duplicates shared subproofs and makes proof combination more
   tree-shaped.

Do **not** use a naive unordered "closed set of formulas" predicate.
That admits circular justifications: a formula could be justified from
itself if the whole set is available at every step. The proof object
must carry a well-founded dependency relation, either explicit ranks or
tree structure.

Chosen design: **ranked proof-step set**. It is closest to the
current Hilbert proof-sequence semantics while keeping the internal HF
formula set-native.

Exit criterion for Phase 0:

* Define the external HOL predicate, e.g. `Proof_HF_set P n`. **Done:**
  `hf_repr_core.py` now has `valid_step_hf_set` and `Proof_HF_set`
  as the ranked-set target predicates.
* Prove the axiom-only witness: **Done:**
  `AXIOM_HAS_PROOF_HF_SET` proves
  `is_axiom n ==> ?P. Proof_HF_set P n`.
* Prove at least one closure prototype, preferably MP: **Done:**
  `MP_HAS_PROOF_HF_SET` proves
  `(?P. Proof_HF_set P f) /\ (?Q. Proof_HF_set Q (Imp_f f g))
   ==> ?R. Proof_HF_set R g`.
* Prove the Gen closure prototype: **Done:**
  `GEN_HAS_PROOF_HF_SET` proves
  `(?P. Proof_HF_set P f) ==> ?R. Proof_HF_set R (Forall_f x f)`.
* Redirect `Prov_HF` to the set-native checker: **Done:**
  `PROV_HF_AT` is now `Prov_HF n = (?P. Proof_HF_set P n)`.

Phase 0 has now settled the largest representation risk. G remains the
deepest theorem, but the proof-object shape is no longer the main
unknown.

### Phase 1 — measured quote theorem and projected interfaces

Do **not** prove the global theorem by direct induction. It is now a
small projection from `QUOTE_HF_MUTUAL_MEASURED`; downstream code can
use `QUOTE_HF_PROV_NEQ` directly.

1. **A — `HF4_INST`**. **Done.**
   - Mechanical extension of `HF2_INST`/`HF3_INST` template: two
     `PROV_HF_UI` steps + substitute reductions through the body's
     `∀z` + encoded-iff. Tedious, not deep.
   - This is now closed with no `p.sorry()`. It removed the largest
     mechanical unknown in Phase 1.

2. **Measured mutual quote theorem.**
   - Current active proof target:

     ```text
     QUOTE_HF_MUTUAL_MEASURED
     ```

   - Status: the strong-induction scaffold is now wired through the IH at
     the current measure. The membership miss branch obtains both needed
     recursive facts from the IH:

     ```text
     h_tail_dec  : membership decision for (x, clear_low y)
     h_head_neq  : quoted inequality for (x, low_bit y)
     ```

     using the closed decreases
     `QUOTE_HF_MEM_MEASURE_CLEAR_LOW_DECREASE` and
     `QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE`.
   - The inequality branch is also routed through the IH. `HF_EXT_DIFF`
     supplies a witness `w`; the branch then uses
     `QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES` or
     `QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES` to obtain the two smaller
     membership decisions and closes with
     `PROV_HF_NEQ_FROM_MEM_DIFF` / `_RIGHT`.
   - Remaining Phase 1 proof obligations:

     ```text
     QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES
     QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES
     ```

     These are the two bit/order decrease packages needed by the
     inequality branch after `HF_EXT_DIFF` finds a witness.
   - Remaining visible sorries inside `QUOTE_HF_MUTUAL_MEASURED`:
     exactly three membership branch bridges:

     ```text
     y = 0
     y != 0 /\ x = low_bit y
     y != 0 /\ x != low_bit y
     ```

     These are object-level HF1/HF2/HF3 transfer proofs, not measure or
     induction unknowns. The tail branch
     `y != 0 /\ x != low_bit y` is the largest remaining bridge because
     it must use the smaller tail membership decision plus the smaller
     quoted inequality through `HF3_INST`.

3. **Projected interfaces — done.**
   - This is the membership-only theorem downstream code should cite:

     ```text
     |- !x y.
        (In x y ==> Prov_HF (In_a (quote_hf x) (quote_hf y)))
        /\
        (~In x y ==> Prov_HF (Not_f (In_a (quote_hf x) (quote_hf y))))
     ```

   - This is now closed as the unbounded projection of
     `QUOTE_HF_MUTUAL_MEASURED`, instantiating the measured theorem at
     `SUC0 (quote_hf_mem_measure x y)` and using `NAT0_LT_SUC0`.
   - The global quoted inequality theorem is also closed as the
     analogous unbounded projection:

     ```text
     QUOTE_HF_PROV_NEQ
     |- !s t. ~(s = t)
        ==> Prov_HF (Not_f (Eq_f (quote_hf s) (quote_hf t)))
     ```

     It instantiates `QUOTE_HF_MUTUAL_MEASURED` at
     `SUC0 (quote_hf_neq_measure s t)` and uses `NAT0_LT_SUC0`.

### Phase 2 — `substitute` representability

With Phase 0 settled and the quote dependency concentrated in
`QUOTE_HF_MEM_DECISION`,
this cluster becomes mostly local proof engineering: define the three
HF-formula bodies and walk the resulting Σ₀/Σ₁ structure.

3. **D — `IS_SUBSTITUTE_STEP_REPRESENTS`**
   - First define the body of `is_substitute_step_internal` in
     `hf_repr_core.py` as a 9-disjunction `Or_f`-chain mirroring the
     HOL `is_substitute_step` cases, with `In_a (Pair_ord_q …) var_T`
     for trace-membership clauses.
   - Then case-split on `IS_SUBSTITUTE_STEP_DEF`'s 9 disjuncts; each
     case dispatches one HF-disjunct via `IS_PAIR_ORD_REPRESENTS` /
     `QUOTE_HF_MEM_DECISION` / `QUOTE_HF_AT_PAIR_ORD` and walks HF1–HF3.
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
     The shape of `Proof_HF_internal` follows Phase 0's HF-native
     proof objects. There is no `cons_l` / `mem_l` internal path.
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

* **Phase 0 first** because it removes the largest architectural risk:
  list theory must not be smuggled into HF just to internalise proofs.
  Substitute-trace work still helps, but it will not close the headline
  G1 path until the HF-native proof-object representation is viable.
* **Phase 1 next** because it concentrates the quote dependency into
  `QUOTE_HF_MUTUAL_MEASURED`, with `QUOTE_HF_MEM_DECISION` and
  `QUOTE_HF_PROV_NEQ` as small projected interfaces for downstream
  code.
* **Phase 2 after that** because it is high-leverage and comparatively
  local once `QUOTE_HF_MEM_DECISION` is closed.
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

* **HF-set proof predicate prototype (done)** — `valid_step_hf_set` and
  `Proof_HF_set` now live in `hf_repr_core.py`. They use ranked proof
  records `Pair_ord k h` and only allow MP/Gen citations from lower
  ranks, avoiding the cyclicity problem of unordered closed formula
  sets. The Phase 0 prototype also proves
  `VALID_STEP_HF_SET_PRESERVES`, `AXIOM_HAS_PROOF_HF_SET`, and
  the two closure prototypes `MP_HAS_PROOF_HF_SET` and
  `GEN_HAS_PROOF_HF_SET`. `Prov_HF` has been redirected to
  `?P. Proof_HF_set P n`; next work is internalizing
  `Proof_HF_set_internal`.

* **HF4 instantiation (done)** — `HF4_INST` is now a closed proof,
  not a `p.sorry()`. It follows the `HF3_INST` pattern: obtain
  `Prov_HF HF4_axiom`, prove the nested `is_form` obligations, run
  two `PROV_HF_UI` steps, then normalize the capture-blind
  substitutions through the `Forall_f` and encoded-iff body.
  The old Phase 1 blocker was a canonical nonmembership/order bridge for
  a direct global low-bit quoted inequality theorem. That path has been
  removed; the active proof uses extensional witnesses plus smaller
  membership decisions, with the global theorem now recovered as
  `QUOTE_HF_PROV_NEQ`.

* **Small diagonal side condition (done)** — `hf_godel1.py` no longer
  axiomatizes `VAR_Y_NEQ_VAR_X`; it is proved from `VAR_T_INJ`,
  `VAR_X_DEF`, `VAR_Y_DEF`, and `AXIOM_3_0`.

* **Membership-difference discriminator (done)** —
  `PROV_HF_NEQ_FROM_MEM_DIFF` is closed. This is the reusable final
  step for the mutual-induction strategy: once the induction supplies
  object-level positive membership on one quoted set and object-level
  negative membership on the other, it yields object-level inequality
  of the quoted sets by equality substitution and contraposition.

* **Projected interface contract (active target)** —
  `QUOTE_HF_MEM_DECISION` and `QUOTE_HF_PROV_NEQ` are now the clean
  downstream interfaces.

* **Reverse discriminator (done)** —
  `PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT` is closed. The mutual proof can now
  use either witness orientation:
  positive-left/negative-right via `PROV_HF_NEQ_FROM_MEM_DIFF`, or
  negative-left/positive-right via `PROV_HF_NEQ_FROM_MEM_DIFF_RIGHT`.

* **nat0 order orientation (done)** —
  `NAT0_LT_TRICHOTOMY` and `NAT0_LT_TOTAL_NEQ` are closed in
  `nat0_order.py` by transporting `nat.py` trichotomy through
  `rep_nat0`. This removes a foundational unknown for any strategy that
  orients `quote_hf i` versus `quote_hf x` before using an ordered
  inequality projection.

* **Measure correction for the mutual induction** —
  `Pair_ord x y` is not a valid decreasing measure; numerically,
  `Pair_ord 1 0 > Pair_ord 1 1`. The membership recursion should use
  the set-native measure `Insert x y` instead. In the `x != low_bit y`
  branch, the recursive call from `(x, y)` to `(x, clear_low y)`
  should decrease because removing `low_bit y` removes a bit different
  from `x`. The first bit lemma for this route is now closed:
  `SET_BIT_COMMUTE_DIFF` in `bits.py`.
  The canonical-clearing fact `BIT_CLEAR_LOW_LOW_BIT` is also closed:
  after clearing a nonzero set's low bit, that bit is absent. This is
  needed to prove the formal decrease of
  `quote_hf_mem_measure x (clear_low y)` below
  `quote_hf_mem_measure x y`.

  The HOL extensional discriminator needed by the inequality branch is
  now closed as `HF_EXT_DIFF`, with a small closed Boolean splitter
  `BOOL_NEQ_XOR`.

  The membership miss branch now has the exact named recursive-call
  bound:

  ```text
  QUOTE_HF_MEM_NEEDS_HEAD_NEQ_DECREASE
  |- y != 0 /\ x != low_bit y
     ==> quote_hf_neq_measure x (low_bit y)
         < quote_hf_mem_measure x y
  ```

  Its public proof no longer uses `p.sorry()`. It is derived by splitting
  the `quote_hf_neq_measure` max/`COND_nat0` branch after citing the raw
  Ackermann bit-order obligation:

  ```text
  QUOTE_HF_MEM_HEAD_NEQ_RAW_DECREASE
  |- y != 0 /\ x != low_bit y
     ==> quote_hf_mem_measure x (low_bit y)
         < quote_hf_mem_measure x y
      /\ quote_hf_mem_measure (low_bit y) x
         < quote_hf_mem_measure x y
  ```

  That raw fact is now closed. It applies the top-difference bridge to
  the two strict `Insert` inequalities under the low-bit side condition.

  The required bit-order layer is now closed in `bits.py`. It includes
  the false-bit helpers:

  ```text
  BIT_SELF_FALSE
  |- !n. bit n n = F

  BIT_ABOVE_FALSE
  |- !n i. n < i ==> bit i n = F

  BIT_AT_SET_BIT_OTHER_SELF_FALSE
  |- !i j. i != j ==> bit j (set_bit i j) = F
  ```

  plus the double/half order helpers:

  ```text
  DOUBLE_LT_SUC0_DOUBLE_SELF
  DOUBLE_LT_SUC0_DOUBLE
  SUC0_DOUBLE_LT_DOUBLE
  HALF_LT_IMP_LT
  BIT_SUBSET_LE
  ```

  and the main top-difference comparison lemma:

  ```text
  BITWISE_LT_BY_TOP_DIFF
  |- !k a b.
     (!i. nat0_lt k i ==> bit i a ==> bit i b)
     /\ ~(bit k a) /\ bit k b
     ==> nat0_lt a b
  ```

  The raw-decrease proof applies this bridge to the two specialized
  `set_bit` bounds:

  ```text
  |- y != 0 /\ x != low_bit y
     ==> nat0_lt (set_bit x (low_bit y)) (set_bit x y)

  |- y != 0 /\ x != low_bit y
     ==> nat0_lt (set_bit (low_bit y) x) (set_bit x y)
  ```

  The first uses discriminator bit `low_bit y`; the second uses
  discriminator bit `x`. Both need `BIT_LOW_BIT`, `BIT_AT_SET_BIT_DIFF`,
  `BIT_AT_SET_BIT_SAME`, and the newly closed false-bit helpers for the
  high-bit-containment side condition.

  The remaining inequality-branch decreases are now named explicitly:

  ```text
  QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES
  |- In w s /\ ~In w t
     ==> M(w,s) < Q(s,t) /\ M(w,t) < Q(s,t)

  QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES
  |- ~In w s /\ In w t
     ==> M(w,s) < Q(s,t) /\ M(w,t) < Q(s,t)
  ```

  These are currently visible `p.sorry()` helpers. They should be
  discharged with `BITWISE_LT_BY_TOP_DIFF`, `SET_BIT_PRESENT_ID`, and
  branch splits over whether the outer set is already a bit of the
  opposite side.

* **Induction-target experiments** —
  `hf_induction_targets.py` brute-checks candidate measures
  against the mutual proof's decrease obligations:
  membership tail recursion, the membership proof's call to quoted
  head inequality, quote decomposition recursion, and the extensional
  symmetric-difference witness route. Up to `--limit 128`, the only
  tested target passing all obligations is:

  ```text
  quote_hf_mem_measure x y = Insert x y
  quote_hf_neq_measure s t =
    max(Insert s t, Insert t s)
  ```

  These are now defined in `hf_repr_thms.py`. The formal
  `quote_hf_neq_measure` avoids a general `max` operator by using
  `COND_nat0 (nat0_lt (Insert s t) (Insert t s))`.

* **Measured mutual target (active, induction shape validated)** —
  `QUOTE_HF_MUTUAL_MEASURED` states the strong-induction target over a
  bound `n`: all membership decisions with
  `quote_hf_mem_measure x y < n`, and all quote inequalities with
  `quote_hf_neq_measure s t < n`. Its body now has the correct outer
  strong-induction frame on `n` and no longer uses any old projection
  wrapper.

  The membership half calls the IH at the current membership measure
  `M(x,y)` and, in the miss branch, uses the closed measure decreases to
  obtain the tail membership decision and head inequality recursively.
  The remaining three `p.sorry()` leaves are the object-level branch
  bridges:

  ```text
  y = 0:
    HF1/NOT_IN_EMPTY bridge for the empty quoted set

  y != 0 /\ x = low_bit y:
    HF2 bridge for head membership in the Insert_t quote

  y != 0 /\ x != low_bit y:
    HF3 bridge transferring the tail decision across Insert_t, using
    the recursive quoted inequality between x and low_bit y
  ```

  The inequality half is structurally closed through the IH: it obtains
  a discriminating member from `HF_EXT_DIFF`, gets both smaller
  membership decisions using the left/right ext-diff decrease helpers,
  and closes via the object-level membership-difference lemmas. Its
  only remaining dependency is that the two ext-diff decrease helpers
  are still visible `p.sorry()` lemmas.

  `Pair_ord` is kept behind `--include-pair-ord` because exact values
  explode; small runs still reject it as the membership measure.

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
* **A**: done. The main DSL friction was exact parser shape
  management for the encoded iff under `Forall_f`; private string
  builders now keep those terms aligned with the substitute rewriter's
  unfolded `Var_t 0` / `Var_t (SUC0 0)` / `Var_t (SUC0 (SUC0 0))`
  normal forms.
* **B/C**: current blockers are the two ext-diff decrease helpers, not
  the removed low-bit global inequality lemmas. Keep the next work on
  `QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES` and
  `QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES`, then discharge the three
  membership branch bridges in `QUOTE_HF_MUTUAL_MEASURED`.
