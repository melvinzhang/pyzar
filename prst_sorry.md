# PRST Remaining `p.sorry()` Ledger

This file intentionally lists only open `p.sorry()` obligations in
`prst_*.py`. Completed layer notes are removed.

The sole explicit PRST axiom outside this ledger is `MU_CORRECTNESS`.

## Order of Attack

This ledger is ordered by dependency and expected discharge path, not by file.
Pure forwarding theorems are deleted instead of tracked.

### Architectural note: no structural HOL↔PR bridge

`Mem_PRST`, `ValidProof_PRST`, and `Proof_PRST` remain as HOL relations
for stating top-level theorems (Gödel statements mention `Prov_PRST`,
which is defined via `Proof_PRST`). The internal checker functions
(`mem_t_pr`, `exists_mp_witness_pr`, `valid_step_pr`, `valid_proof_list_pr`,
`is_tup_pr`, `is_pterm_pr`, `is_pr_axiom_pr`, `substitute_pr` recursion)
are reasoned about *directly* via `App_pt ... = T_pt`. There is no
structural correctness theorem bridging the two sides — that bridge layer
was deleted as scaffolding-only churn. Downstream stubs that need to
connect HOL `Proof_PRST` to PR `Proof_PRST_pr` go through the standard
PRST evaluator package (`PRST_INTERNALIZES_TRUE_PR_EVAL` /
`PRST_INTERNALIZES_FALSE_PR_EVAL`) rather than a body-correctness theorem.

### 1. `Proof_PRST_pr` Checker API Boundary

These are the immediate checker targets. All stated purely in PR terms
(`App_pt Proof_PRST_pr ... = T_pt` / `= F_pt`) plus, on the `~ Proof_PRST`
side, the HOL provability relation as antecedent only.

- `PRST_INTERNALIZES_TRUE_PR_EVAL`
- `PRST_INTERNALIZES_FALSE_PR_EVAL`
- `PROOF_PRST_PR_BOOLEAN_VALUE`
- `PROOF_PRST_PR_SEMANTIC_NEG`
- `PROOF_PRST_PR_QUOTED_TRUE_EVAL`
- `PROOF_PRST_PR_QUOTED_FALSE_EVAL`

The quoted-input obligations intentionally do not assert raw-to-`quote_hf`
checker-value preservation. `quote_hf` is the object-language numeral
interface; the proof route should use `numeral_pr`/`quote_hf` evaluation plus
internalisation of the resulting PR computation.

The `~ Proof_PRST pf n` antecedent in the semantic-neg / quoted-false stubs
is lifted to the PR side by case-splitting on `PROOF_PRST_PR_BOOLEAN_VALUE`
plus PRST soundness — *not* via a structural body-correctness theorem.

### 2. Proof-List Combination API

These discharge the remaining list plumbing used by PRST modus ponens and the
G2 proof-combinator path.

- `PROOF_PRST_VALID_MEM_SELF`
- `PROOF_PRST_LIST_MERGE`
- `MP_COMBINE_PR_CORRECT`

### 3. Internal PRST Evaluator Clauses

These are the constructor and composition clauses behind the public evaluator
theorems for `substitute_pr`, `numeral_pr`, and `diag_pr`.

- `PROV_PRST_SUBSTITUTE_EMPTY_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_VAR_HIT_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_VAR_MISS_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_TUP_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_APP_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_EQ_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_IN_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_NOT_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_IMP_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_OPAQUE_EVAL_CLAUSE`
- `PROV_PRST_SUBSTITUTE_EVAL_BY_STRUCTURAL_CLAUSES`
- `PROV_PRST_NUMERAL_ZERO_EVAL_CLAUSE`
- `PROV_PRST_NUMERAL_SUC_EVAL_CLAUSE`
- `PROV_PRST_DIAG_DEFINING_EVAL`
- `PROV_PRST_DIAG_EVAL_BY_COMPONENTS`

### 4. Representation Bridges

These are downstream of the evaluator and checker API. Keep this layer to the
concrete bridge obligations used downstream.

- `SUBSTITUTE_REPRESENTS_PRST`
- `DIAG_REPRESENTS_PRST`
- `PROV_PRST_REPRESENTS`

### 5. G1 Stack

These are the first-incompleteness targets after the checker, evaluator, and
representation bridges are in place.

- `DIAGONAL_LEMMA_PRST`
- `G_PRST_DIAGONAL_EQ`
- `PRST_CONSISTENT`
- `PRST_SIGMA1_SOUND`
- `GODEL_FIRST_PRST`
- `PRST_ESSENTIALLY_UNDECIDABLE`

### 6. G2 Stack

These remain after G1. `MP_COMBINE_PR_CORRECT` is listed earlier because its
proof depends on the checker/list-combine API, not on Loeb.

- `IS_PFORM_CON_PRST`
- `DERIV_D1`
- `DERIV_D2`
- `DERIV_D3`
- `LOEB_PRST`
- `GODEL_SECOND_PRST`
- `PRST_CANNOT_PROVE_OWN_CONSISTENCY`

## Counts

- Remaining `p.sorry()` sites: 40
  - prst_proof.py: 20
  - prst_repr.py:  6
  - prst_godel1.py: 6
  - prst_godel2.py: 8

  *(Down from 65: two scaffolding cuts. (1) Section 0 + 0b structural bridge
  (`IS_TUP_PR_CORRECT`, `MEM_T_PR_CORRECT`, `EXISTS_MP_WITNESS_PR_CORRECT`,
  `VALID_STEP_PR_CORRECT`, `VALID_PROOF_LIST_PR_CORRECT`, the five course_rec
  sub-stubs, and `PROOF_PRST_PR_BODY_CORRECT`). (2) Section 0a App_pt
  evaluator stack (`APP_PT_PROJ_AT_*`, `APP_PT_COMP_EVAL_*`,
  `APP_PT_CONST_EVAL`, `APP_PT_IF_IN_*_EVAL`, `APP_PT_PAIR_*_EVAL`,
  `APP_PT_PAIR_ORD_EVAL`, `APP_PT_REC_*_EVAL`, `APP_PT_COURSE_REC_*_EVAL`)
  plus the boolean/eq_nat helper proofs that consumed them
  (`AND/OR_BOOL_PR_CORRECT`/`REDUCE`/`TRUE_VIEW`, `EQ_NAT_PR_SAME`/`CORRECT_*`/
  `TRUE_VIEW`, `F_PT_NEQ_T_PT`, `TUP_HEAD_PR_CORRECT`,
  `PROOF_PRST_PR_BOOL_VIEW`). The boolean stack was orphaned by cut (1); no
  remaining stub consumes any of it. See the "no structural HOL↔PR bridge"
  note above.)*

## PR Symbol Evaluator Spikes

These are short validation tasks for the main unknowns on the PRST
evaluator path. They are not additional `p.sorry()` sites; they are meant to
decide whether the remaining proof debt stays local or expands into larger
representability work.

### Design 1 — Boolean Helper Correctness

Purpose: prove the small PR boolean helper facts once, then reuse them
everywhere.

Design facts:

- `eq_nat_pr` returns `T_pt` exactly on equal nat0 inputs.
- `or_bool_pr` and `and_bool_pr` agree with the `T_pt`/`F_pt` convention.
- `T_PT_NEQ_F_PT` is available before evaluator correctness proofs consume it.

Settled shape:

- `T_pt` and `F_pt` are distinct.
- `eq_nat_pr x y` returns `T_pt` exactly when `x = y`, and `F_pt` otherwise.
- `or_bool_pr` and `and_bool_pr` are ordinary boolean connectives under the
  boolean-input invariant `x,y in {T_pt,F_pt}`.
- Outside that invariant, the helpers intentionally branch on exactly
  `x = T_pt`: `or_bool_pr x y` returns `y` when `x != T_pt`, and
  `and_bool_pr x y` returns `F_pt` when `x != T_pt`.
- Under boolean inputs, the reusable algebra includes identity, annihilator,
  associativity, and distributivity facts needed by `is_pr_refl_pr`,
  `mem_t_pr`, and proof-list checker correctness.

The executable reference design is `prst_bool_spike.py`.

Production proof obligations: prove these helper evaluation lemmas once from
the `if_in_sym` defining equations and `T_PT_NEQ_F_PT`, then require downstream
checker proofs to establish the boolean-input invariant before using boolean
algebra rewrites.

### Design 2 — `is_pterm_pr` Correctness Slice

Purpose: pin the PR-level term recognizer used by reflexivity and proof-checker
examples.

Design facts:

- `is_pterm_pr Empty_pt = T_pt`.
- `is_pterm_pr (Tup_pt a b) = T_pt` from recursive `a`/`b` truth.
- `is_pterm_pr (App_pt f args) = T_pt` from `is_partial_pr_sym f` and args.
- `is_pr_refl_pr (Eq_pf t t) = T_pt` when the Eq shape is reflexive and
  `is_pterm_pr t = T_pt`.

Settled shape:

- `is_pterm_pr` is modeled as a Pair_ord course recursion returning
  `Pair_ord(is_term_bool, child_bool_pair)`, not as a direct syntax recursion.
- `Empty_pt`, `Var_pt`, `Tup_pt`, and `App_pt` have the expected boolean
  behavior. The `Tup_pt` branch consumes the two child booleans carried by the
  intermediate payload pair.
- The `App_pt` branch checks the function id with the syntactic
  `is_partial_pr_sym_pr` predicate and checks only the argument tuple through
  the payload's right child boolean.
- Representative reflexivity formulas such as `Eq_pf t t` with nontrivial
  `App_pt`/`Tup_pt` terms are accepted by `is_pr_refl_pr`; malformed non-term
  payloads and invalid App heads are rejected.

The executable reference design is `prst_pterm_spike.py`.

Production proof obligations: prove the corresponding PR evaluation lemmas for
the auxiliary course recursion, then use them to derive
`is_pr_refl_pr (Eq_pf t t) = T_pt` from the HOL-side `is_pterm t` theorem for
the representative constructor cases.

### Design 3 — `is_pr_axiom_pr` Leaf Alignment

Purpose: keep the PR checker leaf aligned with the HOL recognizer
branch-by-branch.

Branch contract:

- Direct and substituted PR-def axioms are accepted through
  `is_pr_def_instance_pr`.
- PRST reflexivity formulas such as
  `Eq_pf (App_pt adj_sym args) (App_pt adj_sym args)` are accepted through
  `is_pr_refl_pr`, guarded by `is_pterm_pr`.
- Propositional Hilbert schemas are accepted through `is_logical_axiom_pr`.

The PR-side recognizer has real bodies for the three leaves:

- `is_pr_def_instance_pr` is a disjunction of PR-level schema matchers.
  Each matcher reads schema parameters from the candidate formula, reconstructs
  the relevant PR-def template, and checks that the candidate is either the
  direct template or a one-variable `substitute_p` instance of that template.
- `is_pterm_pr` uses a Pair_ord course recursion for `Empty_pt`, `Var_pt`,
  `Tup_pt`, and `App_pt`, with App heads checked by a syntactic
  `is_partial_pr_sym_pr` shape recognizer.
- `is_logical_axiom_pr` recognizes the propositional K/S/N Hilbert schemas by
  PR-level destructuring of `Imp_pf`/`Not_pf` shapes.

`is_pr_def_instance_pr` must not search arbitrary `F,t,v < n`. Substitution can
shrink fixed `Var_pt` leaves, so a numeric bound on the pre-substitution axiom
is not a stable invariant. The settled design is schema-specific matching:

- For closed templates with no free `Var_pt` slots, accept the direct template.
- For fixed-arity schemas, destructure the candidate formula and verify each
  repeated formal slot against the extracted replacement term.
- For variable-arity schemas such as `proj_def_axiom_at i n`, read the schema
  parameters from the candidate symbol payload, check the HOL-side guard
  (`i < n`), walk the argument tuple, and verify one consistent substituted
  formal slot.
- For parametric schemas such as `rec`, `const`, `course_rec`, and `pair_*`,
  read the parameters from the candidate shape and use the same one-variable
  substitution-instance check, including nested parameter occurrences such as
  the RHS of `const_def_axiom_at c`.

The executable reference design is `prst_def_instance_spike.py`. It covers every
current `is_pr_def` axiom family: `zero`, `proj`, `if_in_true`,
`if_in_false`, `rec_base`, `rec_step`, `const`, `course_rec_base`,
`course_rec_step`, `pair_left`, `pair_right`, and `pair_ord`, including
malformed near-misses.

Production requirements: mechanise the reference design at PR level with tuple
walkers, PR-level guards such as `nat0_lt`/`is_pr_sym`, and reusable
substitution-instance checker components for schema parameters.

### Design 4 — `substitute_pr` External Correctness Slice

Purpose: pin the external correctness proof shape for `substitute_pr`.

Design facts:

- `substitute_pr Empty_pt t v` evaluates to `Empty_pt`.
- `substitute_pr (Eq_pf a b) t v` evaluates to
  `Eq_pf (substitute_p a t v) (substitute_p b t v)`.
- `App_pt`/`Tup_pt` nested examples evaluate by the same constructor-recursive
  equation as HOL-side `substitute_p`.

Settled shape:

- The Pair_ord course-recursive `substitute_pr` model agrees with direct
  `substitute_p` syntax recursion on `Empty_pt`, `Var_pt`, `Tup_pt`, `Eq_pf`,
  `In_pa`, `Not_pf`, `Imp_pf`, and nested examples.
- The `App_pt` branch is non-uniform in the intended way: it preserves the
  function id exactly and recurses only into the argument tuple.
- The raw default Pair_ord branch is enough to make constructor payload pairs
  carry the recursively substituted child values, which is what the `Eq_pf`,
  `Tup_pt`, and `App_pt` cases consume.
- If the target variable is absent from a well-formed example, the result is
  unchanged.

The executable reference design is `prst_substitute_spike.py`.

Production proof obligations: prove the external correctness theorem by a
single course-recursion induction over the encoded formula/term, with
constructor-specific rewrite lemmas for the Var hit/miss case, the default
payload-pair case, and the App non-uniform function-id case.

### Design 5 — `Proof_PRST_pr` List Checker Slice

Purpose: pin the proof-list checker recursion before proving full correctness.

Design facts:

- Singleton axiom list: `Proof_PRST_pr (Tup_pt a Empty_pt, a) = T_pt` when
  `is_pr_axiom_pr a = T_pt`.
- Two-line MP list: from lines `f` and `Imp_pf f g`, appending `g` validates.
- Negative empty-list case: `Proof_PRST_pr (Empty_pt, n) = F_pt`.

Settled shape:

- Proof lists use the same final-line-first `Tup_pt` orientation as
  `Proof_PRST`.
- singleton axiom proof lists validate from the `is_pr_axiom_pr` leaf;
- `Empty_pt` never validates as a proof list;
- a new head `g` validates by MP when the tail already contains both `f` and
  `Imp_pf f g`.
- negative cases cover non-`Tup_pt` proof inputs, malformed list tails, invalid
  axiom singletons, wrong targets, MP missing the antecedent, MP missing the
  implication, and nearby nonmatching implications;
- ordering and duplicate-line cases validate because MP uses membership in the
  full earlier-list tail.

The executable reference design is `prst_checker_spike.py`.

The current `Proof_PRST_pr` body in `prst_pr.py` matches this decomposition:
top-level `is_tup_pr`, head equality via `tup_head_pr`, full-list validation
via `valid_proof_list_pr`, membership via `mem_t_pr`, and MP search via
`exists_mp_witness_pr`.

Production proof obligations (PR-native; no HOL twin chain): callers needing
a structured view of `App_pt Proof_PRST_pr ... = T_pt` reduce through the
existing `PROOF_PRST_PR_BOOL_VIEW` (which expresses the body as an
`and_bool_pr` chain of `is_tup_pr`, head-eq, and `valid_proof_list_pr`
checks) and reason about the underlying PR predicates directly.

One separate G2-only blocker remains for the D2/proof-combinator path:
`mp_combine_pr` in `prst_godel2.py` is still the constant-0 stub, so the
two-line checker shape is validated only for an explicit proof list, not yet
for `App_pt mp_combine_pr ...`.

### Design 6 — Internal Evaluation Chain

Purpose: ensure that external PR-symbol correctness can be lifted into PRST
provability without recreating HF-style representability packages.

Reference coverage:

- `PROV_PRST_NUMERAL_EVAL` by induction on arbitrary `n`.
- `PROV_PRST_SUBSTITUTE_EVAL` by constructor recursion over all PRST syntax
  families.
- `PROV_PRST_DIAG_EVAL` by composition of `diag_pr`, numeral evaluation, and
  substitute evaluation.

Design criterion: each evaluation theorem follows from PR-def instances plus
`PROV_PRST_AX`, `PROV_PRST_SUBST`, `PROV_PRST_MP`, and equality reasoning,
not from a new global representability axiom.

Settled shape:

- `PROV_PRST_NUMERAL_EVAL` is modeled by induction on `n`: base uses the
  recursor base equation plus `zero_def_axiom`; successor uses the recursor
  step equation, the predecessor evaluation, and the `adj`/`Adj_pt` equation.
- `PROV_PRST_SUBSTITUTE_EVAL` is modeled by constructor recursion over every
  PRST syntax family: `Empty_pt`, `Var_pt` hit/miss, `Tup_pt`, `App_pt`,
  `Eq_pf`, `In_pa`, `Not_pf`, `Imp_pf`, and opaque atom/default cases.
- The `App_pt` substitution case records the non-uniform obligation that the
  function id is preserved exactly while only the argument tuple recurses.
- `PROV_PRST_DIAG_EVAL` is modeled as composition of the `diag_pr` definition,
  numeral evaluation, substitute evaluation, and equality reasoning.
- The proof-plan checker rejects any use of a global representability axiom;
  all leaves are PR-def instances, `PROV_PRST_AX`, `PROV_PRST_SUBST`,
  `PROV_PRST_MP`, or PRST equality reasoning.

The executable reference design is `prst_internal_eval_spike.py`.

Production proof obligations: expose the local PRST equality API needed for
reflexivity, symmetry, transitivity, and congruence; mechanise the generic
`PRST_INTERNALIZES_TRUE_PR_EVAL` boundary for true PR computations; then
mechanise the numeral induction, substitute constructor recursion, and diag
composition recorded by the reference. No global representability axiom is
part of the G1 internal-evaluation bridge.

### Spike 7 — `mu` Strength Check

Goal: verify that the current sole explicit axiom, `MU_CORRECTNESS`, is enough
for the planned proof-search witness.

Target fact:

- If `Proof_PRST_pr p n = T_pt`, then the `find_proof_pr`/`mu_sym` witness
  application also checks as a proof of `n`.

Success criterion: no leastness or totality property of `mu` is needed for G1;
only the current correctness direction is consumed.

Status: passed. `FIND_PROOF_PR_MU_CORRECT` proves the target specialization
from `MU_CORRECTNESS` alone:

```text
|- !pf n.
     App_pt Proof_PRST_pr (Tup_pt pf (Tup_pt n Empty_pt)) = T_pt
     ==> App_pt Proof_PRST_pr
           (Tup_pt (App_pt find_proof_pr (Tup_pt n Empty_pt))
                   (Tup_pt n Empty_pt)) = T_pt
```

The proof only uses `is_pr_sym Proof_PRST_pr`, the generic lift to
`is_partial_pr_sym`, `MU_CORRECTNESS`, and the definition
`find_proof_pr = mu_sym Proof_PRST_pr`.
