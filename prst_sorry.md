# PRST Remaining `p.sorry()` / `new_axiom` Ledger

This file intentionally lists only open `p.sorry()` obligations and explicit
`new_axiom` commitments in `prst_*.py`. Completed layer notes are removed.

## `p.sorry()` Sites

### `prst_pr.py` — 5

- `PR_ARITY_ZERO`
- `PR_ARITY_ADJ`
- `PR_ARITY_PROJ`
- `PR_ARITY_IF_IN`
- `PR_ARITY_REC`

### `prst_proof.py` — 5

- `MU_CORRECTNESS`
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

## Explicit `new_axiom` Commitments

### `prst_proof.py` — 5

- `PROV_PRST_SUBST_AXIOM`
  - `!F t v. is_pr_def F ==> Prov_PRST (substitute_p F t v)`
- `PRST_REFL_AXIOM`
  - `!t. is_pterm t ==> Prov_PRST (Eq_pf t t)`
- `PROOF_PRST_PR_CORRECT`
  - `!p n. Proof_PRST p n = (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt)`
- `PROOF_PRST_PR_INTERNAL_EVAL`
  - `!p n. App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt)) = T_pt ==> Prov_PRST (Eq_pf (App_pt Proof_PRST_pr (Tup_pt p (Tup_pt n Empty_pt))) T_pt)`
- `PROV_PRST_MP`
  - `!f g. Prov_PRST f /\ Prov_PRST (Imp_pf f g) ==> Prov_PRST g`

## Counts

- Remaining `p.sorry()` sites: 31
- Explicit `new_axiom` declarations: 5
- Total listed commitments: 36
