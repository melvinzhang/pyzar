# PRST Remaining `p.sorry()` Ledger

This file intentionally lists only open `p.sorry()` obligations in
`prst_*.py`. Completed layer notes are removed.

The sole explicit PRST axiom outside this ledger is `MU_CORRECTNESS`.

## `p.sorry()` Sites

### `prst_pr.py` — 5

- `PR_ARITY_ZERO`
- `PR_ARITY_ADJ`
- `PR_ARITY_PROJ`
- `PR_ARITY_IF_IN`
- `PR_ARITY_REC`

### `prst_proof.py` — 14

- `MEM_PRST_MONO`
- `VALID_PROOF_PRST_MONO`
- `PROOF_PRST_VALID_MONO`
- `PROOF_PRST_NIL`
- `PROOF_PRST_CONS`
- `PROOF_PRST_SINGLETON_AX`
- `PROOF_PRST_PR_CORRECT`
- `PROOF_PRST_PR_INTERNAL_EVAL`
- `PROOF_PRST_LIST_COMBINE`
- `PROOF_PRST_CONS_MP_STEP`
- `PROV_PRST_SUBSTITUTE_EVAL`
- `PROV_PRST_NUMERAL_EVAL`
- `PROV_PRST_DIAG_EVAL`
- `PROV_PRST_REPRESENTS`

### `prst_repr.py` — 7

- `T_PT_NEQ_F_PT`
- `REPRESENTABILITY_POSITIVE`
- `REPRESENTABILITY_NEGATIVE`
- `SUBSTITUTE_REPRESENTS_PRST`
- `DIAG_REPRESENTS_PRST`
- `PROOF_PRST_REPRESENTS_POS`
- `PROOF_PRST_REPRESENTS_NEG`

### `prst_godel1.py` — 6

- `DIAGONAL_LEMMA_PRST`
- `G_PRST_DIAGONAL_EQ`
- `PRST_CONSISTENT`
- `PRST_SIGMA1_SOUND`
- `GODEL_FIRST_PRST`
- `PRST_ESSENTIALLY_UNDECIDABLE`

### `prst_godel2.py` — 8

- `IS_PFORM_CON_PRST`
- `DERIV_D1`
- `MP_COMBINE_PR_CORRECT`
- `DERIV_D2`
- `DERIV_D3`
- `LOEB_PRST`
- `GODEL_SECOND_PRST`
- `PRST_CANNOT_PROVE_OWN_CONSISTENCY`

## Counts

- Remaining `p.sorry()` sites: 40

## PR Symbol Evaluator Spikes

These are short validation tasks for the main unknowns on the PRST
evaluator path. They are not additional `p.sorry()` sites; they are meant to
decide whether the remaining proof debt stays local or expands into larger
representability work.

### Spike 1 — Boolean Helper Correctness

Goal: prove the small PR boolean helper facts once, then reuse them everywhere.

Target facts:

- `eq_nat_pr` returns `T_pt` exactly on equal nat0 inputs.
- `or_bool_pr` and `and_bool_pr` agree with the `T_pt`/`F_pt` convention.
- `T_PT_NEQ_F_PT` is available before evaluator correctness proofs consume it.

Success criterion: `is_pr_refl_pr` and `mem_t_pr` proofs can treat boolean
combinators as ordinary boolean algebra instead of expanding `if_in_sym` every
time.

### Spike 2 — `is_pterm_pr` Correctness Slice

Goal: implement/prove a narrow recognizer slice for the constructors used by
reflexivity and proof-checker examples.

Target facts:

- `is_pterm_pr Empty_pt = T_pt`.
- `is_pterm_pr (Tup_pt a b) = T_pt` from recursive `a`/`b` truth.
- `is_pterm_pr (App_pt f args) = T_pt` from `is_partial_pr_sym f` and args.

Success criterion: prove `is_pr_refl_pr (Eq_pf t t) = T_pt` from
`is_pterm t` for a representative nontrivial term such as an `App_pt` over a
`Tup_pt` tuple.

### Spike 3 — `is_pr_axiom_pr` Leaf Alignment

Goal: test the PR checker leaf against the HOL recognizer branch-by-branch.

Target examples:

- A direct PR-def axiom, such as `zero_def_axiom`.
- A substituted PR-def instance, such as `substitute_p zero_def_axiom t v`.
- A PRST reflexivity formula, such as `Eq_pf (App_pt adj_sym args) (App_pt adj_sym args)`.

Success criterion: each example satisfies both the HOL recognizer
`is_pr_axiom` and the PR symbol recognizer `is_pr_axiom_pr`, with the same
branch responsible for success.

Status: partially unblocked. The HOL-side branch alignment is already in
place:

- `zero_def_axiom` reaches `is_pr_axiom` through
  `is_pr_def_instance`/`is_pr_def`;
- `substitute_p zero_def_axiom t v` reaches `is_pr_axiom` through
  `is_pr_def_instance`/substitution;
- `Eq_pf t t` reaches `is_pr_axiom` through `is_pr_refl` when `is_pterm t`.

The PR-side recognizer now has real bodies for the three leaves:

- `is_pr_def_instance_pr` recognizes the closed direct PR-def axioms
  `zero_def_axiom`, `if_in_true_def_axiom`, and `if_in_false_def_axiom`;
- `is_pterm_pr` uses a Pair_ord course recursion for `Empty_pt`, `Var_pt`,
  `Tup_pt`, and `App_pt`, with App heads checked by a syntactic
  `is_partial_pr_sym_pr` shape recognizer;
- `is_logical_axiom_pr` recognizes the propositional K/S/N Hilbert schemas
  by PR-level destructuring of `Imp_pf`/`Not_pf` shapes.

Remaining gap: the full `is_pr_def_instance_pr` leaf still needs bounded
witness search for parametric PR-def axioms and nontrivial substituted
instances. The `substitute_p zero_def_axiom t v` example is covered only when
it reduces back to the closed `zero_def_axiom`; it is not yet evidence for the
general substitution branch.

### Spike 4 — `substitute_pr` External Correctness Slice

Goal: prove correctness for the easy constructor cases before attempting the
full course-recursive theorem.

Target facts:

- `substitute_pr Empty_pt t v` evaluates to `Empty_pt`.
- `substitute_pr (Eq_pf a b) t v` evaluates to
  `Eq_pf (substitute_p a t v) (substitute_p b t v)`.
- One `App_pt`/`Tup_pt` example with nested arguments.

Success criterion: the full `PROV_PRST_SUBSTITUTE_EVAL` proof can be reduced
to a uniform course-recursion induction plus constructor cases, with no new
object-theory axiom.

### Spike 5 — `Proof_PRST_pr` List Checker Slice

Goal: validate the checker on the smallest proof lists before proving full
correctness.

Target facts:

- Singleton axiom list: `Proof_PRST_pr (Tup_pt a Empty_pt, a) = T_pt` when
  `is_pr_axiom_pr a = T_pt`.
- Two-line MP list: from lines `f` and `Imp_pf f g`, appending `g` validates.
- Negative empty-list case: `Proof_PRST_pr (Empty_pt, n) = F_pt`.

Success criterion: the remaining `PROOF_PRST_PR_CORRECT` proof decomposes into
`Mem_PRST`/`mem_t_pr`, `ValidProof_PRST`/`valid_proof_pr`, and the
`is_pr_axiom_pr` leaf, rather than needing a different proof representation.

Status: structurally passed. `prst_checker_spike.py` now validates the three
small cases against an executable reference model with the same final-line
first `Tup_pt` orientation as `Proof_PRST_pr`:

- singleton axiom proof lists validate from the `is_pr_axiom_pr` leaf;
- `Empty_pt` never validates as a proof list;
- a new head `g` validates by MP when the tail already contains both `f` and
  `Imp_pf f g`.

The current `Proof_PRST_pr` body in `prst_pr.py` matches this decomposition:
top-level `is_tup_pr`, head equality via `tup_head_pr`, full-list validation
via `valid_proof_list_pr`, membership via `mem_t_pr`, and MP search via
`exists_mp_witness_pr`. The remaining proof work is local evaluator API:
boolean helper correctness, Tup destructors, `mem_t_pr` correctness,
`valid_proof_list_pr` correctness, and branch correctness for
`is_pr_axiom_pr`.

One separate blocker remains for the D2/proof-combinator path:
`mp_combine_pr` in `prst_godel2.py` is still the constant-0 stub, so the
two-line checker shape is validated only for an explicit proof list, not yet
for `App_pt mp_combine_pr ...`.

### Spike 6 — Internal Evaluation Chain

Goal: check that external PR-symbol correctness can be lifted into PRST
provability without recreating HF-style representability packages.

Target examples:

- `PROV_PRST_NUMERAL_EVAL` for `0` and `SUC0 0`.
- `PROV_PRST_DIAG_EVAL` for a simple formula code.
- `PROV_PRST_SUBSTITUTE_EVAL` for a closed formula where substitution is a no-op.

Success criterion: each example follows from PR-def instances plus
`PROV_PRST_AX`, `PROV_PRST_SUBST`, `PROV_PRST_MP`, and equality reasoning,
not from a new global representability axiom.

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
