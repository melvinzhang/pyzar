# Order of attack — HF Gödel-I `sorry()` plan

This document is primarily the plan for the `p.sorry()` calls in
`hf_repr_thms.py`. The active quote path is the measured mutual
membership/inequality induction; the old HF-IND quote spike and global
low-bit quoted-inequality route have been removed from
`hf_repr_thms.py`. The full HF Gödel-I path also has
additional `p.sorry()` calls in `hf_godel1.py`; those are downstream
work, but the detailed inventory below is file-local to `hf_repr_thms.py`.

The plan is ordered to settle the greatest unknown first. Two switches
are now decided:

* `Prov_HF_internal` must use HF-native proof objects, not `cons_l`
  lists. The HF-set proof-object shape is pinned, and `Prov_HF` has
  been redirected to the set-native checker.
* The G1 development is readability-first. Phase 2 should use a scoped
  HF syntax recursion/induction definitional package for substitution,
  not the old finite-computation encoding.
* Quoted syntax templates should use a separate data/template-filling
  layer. Object-language `substitute` keeps its standard semantics
  (replace variables, do not rewrite variable names); quoted data
  templates are filled by walking `Empty_t`/`Insert_t` data.

## Inventory

| # | Theorem                          | Line | Est. size  | Depends on (sorry)        | Depends on (other)                                          |
|---|----------------------------------|-----:|-----------:|---------------------------|-------------------------------------------------------------|
| A | `HF4_INST`                       | 1400 | done       | —                         | `_prov_of_hf_axiom`, `PROV_HF_UI`, substitute reductions    |
| B | `QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES`  | active | small/med | — | bit top-difference layer |
| C | `QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES` | active | small/med | — | symmetric bit top-difference layer |
| D | `QUOTE_HF_MUTUAL_MEASURED`       | active | med/large  | B, C                      | three object-level HF1/HF2/HF3 branch bridges               |
| E | `QUOTE_HF_MEM_DECISION`          | done   | done       | D                         | final unbounded projection from measured theorem             |
| F | `HF_SYNTAX_REC_PACKAGE`          | active | moderate   | —                         | scoped syntax recursion/induction definitional extension     |
| G | `SUBSTITUTE_REPRESENTS`          | active | small/med  | F                         | direct recursive equations for `substitute_internal`         |
| I | `PROV_HF_REPRESENTS`             | active | large      | G                         | Σ₁ completeness (forward) — Σ₁ soundness deferred to Stage 6; internal body landed |
| J | `IS_FORM_PROV_HF_INTERNAL`       | done   | done       | —                         | structural syntax walk over `Prov_HF_internal`              |
| K | `FREE_IN_PROV_HF_INTERNAL`       | done   | done       | —                         | package free contract for `Prov_HF_internal`                 |

✓ = already proven and exported (no sorry).

Two implementation clusters plus one representation switch:

* **Representation switch: HF-native proof objects.** The internal
  proof predicate will not encode list theory in HF. The previous
  `hf_repr_core.py` list checker has been removed from the active core;
  `Prov_HF` and `Prov_HF_internal` now target dependency-set HF proof
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

Do this first, before investing in downstream representability plumbing.
The target for G is:

```text
Prov_HF_internal(x) := ?P. Proof_HF_set_internal(P, x)
```

where `P` is an HF-native proof object. Do **not** internalise
`cons_l`, `mem_l`, `append_l`, or list recursion.

The Phase 0 prototype pinned the shape to proof-step sets; the Phase 3
spikes refined the rank field to be a dependency set rather than a
numeric height. `hf_repr_core.py` now implements that dependency-set
shape in the active external checker.
For reference, the viable HF-native designs were:

1. **Dependency-set proof-step set.**
   `P` is a finite HF set of records `(rank, formula)`. A step at rank
   `k` is valid if it is an axiom, or follows by MP/Gen from records in
   `P` whose ranks are members of `k`. Thus `k` is the finite set of
   citeable predecessor ranks. This keeps the checker HF-native:
   dependency checks are `In_a i k`, not an internal arithmetic
   `<` predicate.

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

Chosen design: **dependency-set proof-step set**. It is closest to the
current Hilbert proof-sequence semantics while keeping the internal HF
formula set-native and avoiding `lt_internal`.

Exit criterion for Phase 0:

* Define the external HOL predicate, e.g. `Proof_HF_set P n`. **Done:**
  `hf_repr_core.py` now has `valid_step_hf_set` and `Proof_HF_set`
  as dependency-set target predicates. `valid_step_hf_set` uses
  `In i k` / `In j k` membership checks for citations.
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

Phase 0 settled the largest representation risk, and the Phase 3 spikes
settled the final proof-object variant. G remains the deepest theorem,
but the proof-object shape is no longer a design unknown.

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
   - The Phase 1 bit/order obligations are now closed:

     ```text
     QUOTE_HF_EXT_DIFF_LEFT_MEM_DECREASES
     QUOTE_HF_EXT_DIFF_RIGHT_MEM_DECREASES
     ```

     These are the two decrease packages used by the inequality branch
     after `HF_EXT_DIFF` finds a witness.
   - The three object-level membership branch bridges inside
     `QUOTE_HF_MUTUAL_MEASURED` are also closed:

     ```text
     y = 0
     y != 0 /\ x = low_bit y
     y != 0 /\ x != low_bit y
     ```

     They are object-level HF1/HF2/HF3 transfer proofs, not measure or
     induction unknowns. The tail branch uses the smaller tail
     membership decision plus the smaller quoted inequality through
     `HF3_INST`.
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
this cluster should now be simplified for readability. Do **not** make
the old finite-computation checker the main G1 path. Instead, add a scoped
syntax-recursion/induction definitional package for the encoded HF
term/form grammar and define substitution directly by its usual
recursion equations.

3. **F — `HF_SYNTAX_REC_PACKAGE`**
   - Add a narrowly scoped definitional extension principle for
     structurally recursive functions over the existing encoded HF
     syntax grammar:

     ```text
     Empty_t
     Var_t
     Insert_t
     Eq_f
     In_a
     Not_f
     Imp_f
     Forall_f
     ```

   - The package should justify adding a named function/formula by
     recursive equations when all recursive calls are on immediate
     syntax subcomponents. It should also expose the corresponding
     induction principle for proving universal properties of that
     definition.
   - Keep `HF_INDUCTION` / membership induction. The recursion package
     introduces functions cleanly; induction still proves global
     properties about all encoded terms/forms.
   - Scope this to syntax recursion, not arbitrary definability. The
     goal is readable Gödel I, not a broad new replacement/separation
     theory.
   - Implemented in `hf_repr_core.py`: `substitute_internal` is now the
     fixed internal formula governed by the scoped `HF_SYNTAX_REC_PACKAGE`.
     The package exposes generated constructor rules for the substitution
     graph and derives the headline theorem by applying the package to
     those rules.
   - The package theorem is explicitly syntax-scoped:

     ```text
     |- !F t v. (is_term F \/ is_form F) ==>
          Prov_HF (substitute_internal (quote_hf F)
                                       (quote_hf t)
                                       (quote_hf v)
                                       (quote_hf (substitute F t v)))
     ```

     This is now HF-native: syntax codes are passed to the internal
     formula by `quote_hf`, preserving their HF-set constructor shape.
     Using `numeral` here would turn the code into an ordinal numeral
     and make qparse/constructor bodies miss the intended structure.
     The theorem is still syntax-scoped, so downstream proof scripts
     should cite `SUBSTITUTE_REPRESENTS_FORM` or
     `SUBSTITUTE_REPRESENTS_TERM` and discharge only `is_form phi` or
     `is_term phi`.
   - Consumer check: `hf_godel1.py`'s diagonal route already carries
     formula side conditions (`is_form phi`, `IS_FORM_DIAG_INTERNAL`).
     The main use should cite the form wrapper; no non-syntax default
     branch is needed for readability-first G1.

4. **G — `SUBSTITUTE_REPRESENTS`**
   - Define `substitute_internal` directly from the syntax-recursion
     equations for substitution:

     ```text
     substitute Empty_t t v = Empty_t
     substitute (Var_t x) t v =
       if x = v then t else Var_t x
     substitute (Insert_t a b) t v =
       Insert_t (substitute a t v) (substitute b t v)
     substitute (Eq_f a b) t v =
       Eq_f (substitute a t v) (substitute b t v)
     ...
     ```

   - Done via `HF_SYNTAX_REC_PACKAGE`, `SUBSTITUTE_REPRESENTS_SYNTACTIC`,
     `SUBSTITUTE_REPRESENTS_FORM`, and `SUBSTITUTE_REPRESENTS_TERM`.
     The public relation now uses `quote_hf` slots instead of `numeral`
     slots.
   - Direction update: do not make direct `qparse`-vs-`quote_hf`
     constructor bridges the main Phase 2 burden. They are object-level
     equality facts for finite `Insert_t` towers, and proving them
     directly would grow a separate finite-set algebra package.
   - Instead, keep object-language substitution semantic and use a
     separate template-filling layer for body construction. `qparse`
     remains the notation for readable quoted templates; template filling
     replaces explicit hole variables and has its own `Forall_f` behavior:
     preserve the binder slot and always fill the body. Any later bridge is
     localized to template interpretation, not entangled with object
     substitution.
   - Current bridge surface: only `QUOTE_HF_QPARSE_EMPTY` remains in
     `hf_repr_thms.py`, and it is a real closed proof. The non-empty
     `QUOTE_HF_QPARSE_*` bridge axioms have been removed from the main
     theorem layer.
   - Implemented package: `hf_repr_core.py` now exports
     `template_fill`, `template_fill_internal`, the template rules
     `TEMPLATE_FILL_EMPTY`, `TEMPLATE_FILL_HOLE_HIT`,
     `TEMPLATE_FILL_HOLE_MISS`, `TEMPLATE_FILL_EQ`,
     `TEMPLATE_FILL_NOT`, `TEMPLATE_FILL_IMP`,
     `TEMPLATE_FILL_FORALL`, `TEMPLATE_FILL_INSERT`,
     `TEMPLATE_FILL_IN`, and `TEMPLATE_FILL_QPARSE_VAR_T`, plus
     `TEMPLATE_FILL_REPRESENTS_TERM`.

5. **Old operational checker — removed**
   - Done for the main path: the step-by-step substitution checker is no
     longer exported from `hf_repr_thms.py`, and `SUBSTITUTE_REPRESENTS`
     is now the formula wrapper around the syntax-recursion package.
   - The old HOL existence helpers have been removed from `hf_repr_core.py`;
     they do not drive the `SUBSTITUTE_REPRESENTS` proof or the high-layer
     import path.

After Phase 2, the diagonal-lemma path is unblocked end-to-end at the
substitute layer.

### Phase 3 — provability representability

6. **G — `PROV_HF_REPRESENTS`** (the deepest semantic step).
   - **Confirmed design.** Use the dependency-set proof checker:
     proof records remain `Pair_ord k h`, but `k` is a finite HF set of
     citeable predecessor ranks. The external and internal checkers both
     use membership (`In i k` / `In_a i k`) for citations. Do not build
     `lt_internal`, trace/list proof objects, or a separate arithmetic
     rank theory for G1.
   - Define `Prov_HF_internal(x) := ?_internal P.
     Proof_HF_set_internal(P, x)`. The production body follows Phase 0's
     dependency-set HF proof records:
     `Proof_HF_set_internal(P,n)` says there is a rank `k` with
     `Pair_ord k n` in `P`, and every record `Pair_ord j h` in `P`
     satisfies `valid_step_hf_set_internal(P,j,h)`.
   - `spike_prov_hf_body.py` validates the constructor-level design:
     qparse emits the `Pair_ord` record templates, the body is built
     only from HF formula constructors, the free variables are exactly
     `{P,k,h}`, `{P,n}`, and `{x}` for the three layers, and no
     trace/list proof-object vocabulary appears in the compiled body.
   - The rank-as-dependency-set spike (`spike_prov_hf_dep_body.py`)
     keeps records as `Pair_ord k h` but interprets `k` as the finite
     set of predecessor ranks that may be cited. Citation checks become
     ordinary HF atoms `In_a i k`, so this route removes `lt_internal`
     from the primitive boundary. It also validates direct bodies for
     `is_mp_internal` (`g = Imp_f f h`) and `is_gen_internal`
     (`?x. h = Forall_f x f`).
   - The primitive internal bodies for this route now live in
     `hf_repr_core.py`: support recognizers, split axiom packages,
     direct MP/Gen recognizers, `valid_step_hf_set_internal`,
     `Proof_HF_set_internal`, and `Prov_HF_internal`. This replaces
     trace/list recursion and does not reintroduce proof-object bridge
     machinery.
   - `spike_axiom_internal_body.py` validates the split schema-package
     plan:
     `is_axiom_internal = is_hf_axiom_internal \/ is_hf_ind_axiom_internal
     \/ is_logical_axiom_internal`, with the logical package split into
     K/S/N/UI/Vac/Refl/Subst/FaImp. Each package has exactly `{h}` free.
     The remaining lower-layer support bodies are `is_form_internal`,
     `is_term_internal`, `free_in_internal`, and `substitute_internal`.
   - `spike_internal_support_bodies.py` validates finite HF bodies for
     those support predicates. `is_term_internal` and `is_form_internal`
     use closure-set certificates, `free_in_internal` uses a downward
     witness-path set, and `substitute_internal` uses an evaluation graph
     of `Pair_ord input output` records. The bodies have the expected
     free variables and no rank/order or trace/list vocabulary.
     Production proofs still need equivalence/functionality for these
     certificate bodies.
   - `spike_forward_dep_shape.py` validates the forward proof-object
     construction for the dependency-set route. Axiom witnesses use
     `Pair_ord Empty h`; MP adds a new root rank containing the two
     cited root ranks; Gen adds a new root rank containing the cited
     root rank. The intended forward targets are
     `Proof_HF_dep_set P n ==> Prov_HF Proof_HF_dep_set_internal[P,n]`
     and `Prov_HF n ==> Prov_HF Prov_HF_internal[n]`.
   - `spike_external_dep_predicate.py` validates the external predicate
     refactor shape before editing `hf_repr_core.py`: replace
     `nat0_lt i k` premises in `valid_step_hf_set` with `In i k`.
     Closure witnesses become `Pair_ord Empty h` for axioms, a new
     dependency rank `Pair kf kg` for MP, and `Singleton kf` for Gen.
     The preserve/axiom/MP/Gen closure shapes all pass in the executable
     model and contain no rank/order or trace/list vocabulary.
   - `spike_prov_hf_side_conditions.py` validates the final
     `IS_FORM_PROV_HF_INTERNAL` / `FREE_IN_PROV_HF_INTERNAL` proof
     shape. The composed bodies have free variables `{P,k,h}`,
     `{P,n}`, and `{x}` at the valid-step/proof/provability layers;
     no binder captures `x`, and no binder name is reused in the final
     body. The non-local side lemmas are now exported by
     `HF_PACKAGE_SIDE_CONDITION_PACKAGE`: `IS_FORM_IS_AXIOM_INTERNAL`,
     `FREE_IN_IS_AXIOM_INTERNAL`, and reusable qparse-template term/free
     clauses.
   - **Forward direction** (HOL ⇒ HF): Σ₁ completeness for HF.
     Extract a dependency-set `Proof_HF_set` witness via `PROV_HF_AT`,
     encode it with `quote_hf`, and verify each checker conjunct using
     the package bodies above.
   - **Backward direction** (HF ⇒ HOL): Σ₁ soundness — explicitly
     deferred to Stage 6 (HF |= HF1–HF5 via the model construction).
     If needed, split the current iff into forward/backward named
     lemmas so the Stage-6 dependency is not hidden inside one giant
     theorem.

7. **J — `IS_FORM_PROV_HF_INTERNAL`** and
   **K — `FREE_IN_PROV_HF_INTERNAL`**.
   - `IS_FORM_PROV_HF_INTERNAL` is discharged by a structural syntax
     walk over the dependency-set body, using `IS_FORM_AT_*`,
     `TEMPLATE_FILL_PRESERVES_IS_FORM`, and the package side lemma for
     `is_axiom_internal`.
   - `FREE_IN_PROV_HF_INTERNAL` is discharged from the final package
     free-contract theorem `HF_PROV_FREE_CONDITION_PACKAGE`.

## Why this order

* **Phase 0 first** because it removes the largest architectural risk:
  list theory must not be smuggled into HF just to internalise proofs.
  The HF-native proof-object representation must be stable before
  provability representability is worth attacking.
* **Phase 1 next** because it concentrates the quote dependency into
  `QUOTE_HF_MUTUAL_MEASURED`, with `QUOTE_HF_MEM_DECISION` and
  `QUOTE_HF_PROV_NEQ` as small projected interfaces for downstream
  code.
* **Phase 2 after that** because it is high-leverage and comparatively
  local once `QUOTE_HF_MEM_DECISION` is closed. For readability-first
  G1, this should be a syntax-recursion/induction definitional package,
  not the old finite-computation encoding.
* **Phase 3 last** because G carries the deepest semantic content and
  depends on both Phase 2 and the Phase 0 design decision; H/I are cheap
  follow-ups triggered by the chosen `Prov_HF_internal` body.

## Downstream `hf_godel1.py` sorries

After `hf_repr_thms.py` is no-sorry, the remaining G1 work is in
`hf_godel1.py`:

| Theorem | Role | Depends on |
|---|---|---|
| `DIAG_REPRESENTS` | diag relation existence | `SUBSTITUTE_REPRESENTS`, quote/internal composition |
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

* **HF-set proof predicate prototype (done; refactored to Phase 3
  dependency sets)** — `valid_step_hf_set` and `Proof_HF_set` now live
  in `hf_repr_core.py`. They use proof records `Pair_ord k h`, where
  `k` is the finite set of citeable predecessor ranks; MP/Gen citations
  are checked by `In i k` / `In j k`. This avoids the cyclicity problem
  of unordered closed formula sets without importing a numeric
  `lt_internal` predicate. The prototype also proves
  `VALID_STEP_HF_SET_PRESERVES`, `AXIOM_HAS_PROOF_HF_SET`, and
  the two closure prototypes `MP_HAS_PROOF_HF_SET` and
  `GEN_HAS_PROOF_HF_SET`. `Prov_HF` has been redirected to
  `?P. Proof_HF_set P n`. Axiom witnesses use `Pair_ord Empty h`, MP
  adds a root dependency set `Pair kf kg`, and Gen adds
  `Singleton kf`.

* **Original ranked-body spike (done)** — `spike_prov_hf_body.py`
  validates the `nat0_lt`-ranked internal body shape. The formula design
  is viable with qparse `Pair_ord` record terms and ordinary `In_a`
  atoms, but it leaves `lt_internal` as an extra primitive boundary.

* **Rank-as-dependency-set spike (done; moved to production bodies)** —
  `spike_prov_hf_dep_body.py` validates the cleaner HF-native variant:
  proof records remain `Pair_ord k h`, but `k` is the finite set of
  citeable predecessor ranks. The MP/Gen citation checks use `In_a i k`
  instead of `nat0_lt i k`, eliminating `lt_internal`; the production
  definitions in `hf_repr_core.py` now include direct formula bodies for
  `is_mp_internal`, `is_gen_internal`, `valid_step_hf_set_internal`,
  `Proof_HF_set_internal`, and `Prov_HF_internal`.

* **Split axiom-schema spike (done; moved to production bodies)** —
  `spike_axiom_internal_body.py` validates the `is_axiom_internal`
  package split. Closed HF axioms are a 5-way equality package; logical
  axioms are K/S/N/UI/Vac/Refl/Subst/FaImp packages; induction is its
  own package. UI/Subst/Ind factor through `substitute_internal`, while
  Vac/FaImp/Ind factor through `free_in_internal`. The spike confirms
  every package leaves exactly `{h}` free and introduces no rank/order
  or trace/list vocabulary. The package definitions now live in
  `hf_repr_core.py`.

* **Support internal-body spike (done; moved to production bodies)** —
  `spike_internal_support_bodies.py` validates finite object-formula
  bodies for `is_term_internal`, `is_form_internal`, `free_in_internal`,
  and `substitute_internal`. Term/form use finite closure sets; free-in
  uses a witness-path set; substitute uses a local evaluation graph. The
  production definitions now live in `hf_repr_core.py`. The public
  support package `HF_SUPPORT_PREDICATE_PACKAGE` exports positive and
  negative representability clauses for `is_term_internal`,
  `is_form_internal`, and `free_in_internal`; `substitute_internal`
  remains governed by `HF_SYNTAX_REC_PACKAGE`. The companion
  `HF_SUPPORT_EQUIV_PACKAGE` exports the iff-style support equivalences,
  and `SUBSTITUTE_INTERNAL_FUNCTIONAL` derives graph functionality from
  `SUBSTITUTE_INTERNAL_EQUIV`.

* **Forward dependency-set shape spike (done)** —
  `spike_forward_dep_shape.py` validates the proof-object witness shape
  needed for the forward half of `PROV_HF_REPRESENTS`. Closure under
  axioms, MP, and Gen works with dependency sets: new MP ranks contain
  exactly the two cited root ranks, and new Gen ranks contain exactly
  the one cited root rank. This shape is now reflected by the external
  closure proofs in `hf_repr_core.py`.

* **External dependency predicate spike (done)** —
  `spike_external_dep_predicate.py` spells the candidate external
  definitions and validates their closure behavior. The refactor has
  been landed in `hf_repr_core.py`: `valid_step_hf_set` uses
  `In i k` / `In j k`; MP chooses dependency set `Pair kf kg`; Gen
  chooses `Singleton kf`. The executable closure proofs pass for
  subset-preservation, axiom, MP, and Gen.

* **Prov_HF side-condition spike (done)** —
  `spike_prov_hf_side_conditions.py` validates the final
  `IS_FORM_PROV_HF_INTERNAL` and `FREE_IN_PROV_HF_INTERNAL` proof shape.
  The final body has exactly `{x}` free.  The needed package side lemmas
  are landed in `hf_repr_core.py` as `HF_PACKAGE_SIDE_CONDITION_PACKAGE`,
  exporting `IS_FORM_IS_AXIOM_INTERNAL`, `FREE_IN_IS_AXIOM_INTERNAL`, and
  qparse-template term/free clauses for `Pair_ord`, `Imp_f`, and
  `Forall_f`; the final `Prov_HF_internal` free-variable contract is
  exported as `HF_PROV_FREE_CONDITION_PACKAGE`.

* **Phase 3 design decision (confirmed and internal bodies landed)** —
  the main path uses the dependency-set proof checker, and the fixed
  internal bodies/packages now live in `hf_repr_core.py`.
  Remaining work is proof engineering: equivalence/functionality for
  support certificates, package side lemmas, and the forward
  `PROV_HF_REPRESENTS` theorem.

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

  These are now closed. The proof uses `BITWISE_LT_BY_TOP_DIFF`,
  `SET_BIT_PRESENT_ID`, and branch splits over the
  `quote_hf_neq_measure` selector. The right-oriented package is derived
  by applying the left-oriented package with `s`/`t` swapped and rewriting
  through `QUOTE_HF_NEQ_MEASURE_SYM`.

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
  Its object-level branch bridges are closed:

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
  and closes via the object-level membership-difference lemmas.

  `Pair_ord` is kept behind `--include-pair-ord` because exact values
  explode; small runs still reject it as the membership measure.

* **Quoted syntax parser (retained utility).**
  If an internal formula needs to express godelnum-shape claims like
  ``a = Var_t v`` with `var_z` as a free leaf, do not write
  `Eq_f var_a (Var_t var_z)`. `substitute` treats `Var_t k` as a leaf
  (HIT/MISS on the index `k = var_z` = `Var_t (SUC0² 0)`), so it
  never pushes the substitute into `var_z`. The fix is not to change
  object-language substitution; it is to distinguish quoted-data
  template filling from object substitution.

  Implement the notation as **a separate quoted-syntax parser**:
  `hf_qsyntax.qparse` has its own small Lark grammar and emits the
  right `Insert_t`-tower term at body-construction time. The low-level
  builders remain private implementation machinery behind the parser.
  The semantic layer above it is a separate data/template-filling
  relation that walks `Empty_t`/`Insert_t` data and replaces explicit
  hole variables.

  ```python
  qparse("Var_t(var_z)", var_z=var_z)
  qparse("Eq_f(var_a1, var_a2)", var_a1=var_a1, var_a2=var_a2)
  qparse("Forall_f(var_wq, var_f1)", var_wq=var_wq, var_f1=var_f1)
  ```

  Template bodies are then constructed in Python like
  ``Q_eq(var_a, qparse("Var_t(var_z)", var_z=var_z))`` and template
  filling walks the quoted data end-to-end via the `Insert_t`/`Empty_t`
  structure.
  This keeps the notation readable without overloading the ordinary HOL
  parser. The IS_PAIR_ORD_INTERNAL precedent already does this manually
  with literal Insert_t-towers — `qparse` just packages what's already
  in the codebase.

  Tradeoff: theorem statements print with quoted data fully expanded
  into Insert_t/Empty_t towers (verbose). Downstream consumers cite
  named constants and should not need to see the expansion, so the cost
  is one-time at definition.

  **Spike conclusion:** the quoted parser validates the body-shape
  choice. Under the existing `SUBSTITUTE_AT_*` rewrites,
  primitive `Var_t` with a slot in its index stays stuck, and primitive
  `Forall_f` with the target variable as binder correctly stops under
  the binder. The quoted builder shapes normalize as needed for
  `Var_t`, `Eq_f`, `Not_f`, `Imp_f`, `Forall_f`, `Insert_t`, `In_a`,
  and the shared `Pair_ord` expansion. The same run now validates the
  `qparse` forms for `Var_t`, `Eq_f`, and `Forall_f`, so the public
  body-construction API can be the grammar rather than direct builder
  calls. The script run currently reports
  `15/15 candidate expectations satisfied` with:

  ```text
  .venv/bin/python spike_substitute_step_body.py
  ```

  One nuance: primitive `Eq_f` and `In_a` bodies also validate because
  their substitution equations recurse through both arguments. The
  Phase 2 body should still prefer `qparse`/quoted data uniformly,
  because `Var_t` and binder-index positions are exactly where the
  primitive syntax becomes misleading.

  **Current direction:** the parser remains useful, but the direct
  constructor bridge facts are no longer the main plan. For clean G1,
  use scoped syntax recursion for `substitute_internal` and use a
  separate quoted-data/template-filling layer for future internal
  formula bodies. This prevents the proof from trading the old trace
  machinery for a large qparse bridge algebra.

  The first version of that layer is now in `hf_repr_core.py`:
  `template_fill` is a separate HOL recursion, and
  `template_fill_internal` is the internal formula alias. The exported
  rules cover the quoted-template structure (`Empty_t`, `Var_t` hole
  hit/miss, `Insert_t`) and the formula constructors (`Eq_f`, `Not_f`,
  `Imp_f`, `Forall_f`, `In_a`) plus `TEMPLATE_FILL_REPRESENTS_TERM`.
  The `Forall_f` rule is deliberately not object substitution: it keeps
  the binder slot and fills the body. The existing `is_Pair_ord_internal`
  quoted-data body is now built through `qparse`, and
  `TEMPLATE_FILL_QPARSE_VAR_T` proves the representative qparse fill
  case in-repo.

## Notes per step (pitfalls to flag now)

* **Phase 2 recursion package**: keep the schema scoped to the encoded
  HF syntax grammar. A broad "all definable recursive functions" axiom
  would make the model/soundness story harder to audit.
* **G**: keep the forward/backward split explicit — only forward
  direction is in scope for this file; backward gets a parked
  Stage-6 citation, not a sorry-on-sorry.
* **A**: done. The main DSL friction was exact parser shape
  management for the encoded iff under `Forall_f`; private string
  builders now keep those terms aligned with the substitute rewriter's
  unfolded `Var_t 0` / `Var_t (SUC0 0)` / `Var_t (SUC0 (SUC0 0))`
  normal forms.
* **B/C**: done. The ext-diff decrease helpers are closed; the main DSL
  friction was avoiding global symmetric rewrite loops by specializing
  `QUOTE_HF_NEQ_MEASURE_SYM` at use sites.
