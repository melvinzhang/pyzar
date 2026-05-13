# Migration: `halts` over `sk_iter` → `halts_b` over `bullet_iter`

## Motivation

The current `halts t := ?n. is_normal (sk_iter n t)` framing puts
`STANDARDIZATION_NORMAL` on the critical path of the undecidability
proof: `DIAG_TERM` produces a parallel-reduction witness, but every
consumer needs to bridge back to `sk_iter` via standardization.

The natural fix is to switch to a Takahashi-style halting notion.
There are two ways to do this:

1. Via the parallel-reduction *relation* `sk_par_step`:
   `halts_par t := ?N. sk_par_steps t N /\ is_normal N`.
2. Via the parallel-reduction *function* `sk_bullet` (Takahashi's
   complete development):
   `halts_b t := ?n. is_normal (bullet_iter n t)`.

(1) and (2) are classically equivalent, but (1) requires proving the
equivalence via the triangle property + impredicative inversions on
`sk_par_step`.  (2) sidesteps that entire bridge: `sk_bullet` is
deterministic, so `bullet_iter` is just plain nat0 iteration, with no
non-determinism to absorb.

This document is for the **(2)-style** migration.  Switching to
`halts_b`:

- collapses `OMEGA_NON_HALTING` to a 3-cycle enumeration on
  `bullet_iter` (~120 lines, no triangle / par-step inversion),
- deletes the entire `sk_par_step` / `sk_par_steps` ecosystem,
- deletes the `sk_iter` machinery + Ω-trajectory machinery,
- deletes Tromp's Y-combinator subsystem,
- migrates the standardization obligation to a bounded
  "App-other-stable" lemma family used by `HALTS_*_APP_LEFT` consumers
  and `DIAG_TERM`.

Net change: ~3000 lines deleted, ~400 lines added.

## Spike result (2026-05-13): Layer 5 viable with diagonal swap

`outside/sk_par.py` EXP 5 walks three diagonal candidates under
`sk_bullet` with `H` as an opaque atom.

| Candidate | Witness | Target | Reached under bullet? |
|-----------|---------|--------|------------------------|
| (1) Original `DIAG_TERM` | `e = S (S (K H) SII) (K Omega)`, `d = e e` | `(H d) Omega` | **No** — Omega gets eaten at iter 2 |
| (2) **Classical Curry** | `e = S (K H) SII`, `d = e e` | `H d` | **Yes — exactly 4 bullet steps** |
| (3) I-doubled | `e = S (S (K H) I) I`, `d = e e` | `H d` | No — lands on `(H e) e`, then bullet-fixed |

The classical Curry diagonal (candidate 2) lands cleanly on `H d` at
iter 4:

```
iter 0:  d         = e e                                      size=39
iter 1:  (K H e)(SII e)                                       size=57  [outer S-redex]
iter 2:  H ((I e)(I e))                                       size=53  [K + inner S]
iter 3:  H ((K e)(K e) ((K e)(K e)))                          size=89  [two I-as-SKK S-redexes]
iter 4:  H (e e) = H d                                        size=41  [four K-redexes; e preserved]
```

The trick that **fails** for candidate (1) — bullet on `(K Omega) Z`
reduces Omega to `sk_bullet Omega = T1` — is **avoided** by
candidate (2), which has no `K Omega` term.  Bullet still propagates
through every redex, but the residual `e e` re-emerges because the
inner SII-applied-to-e structure fully develops to `e e` in two
parallel rounds of contraction.

**Verdict**: the bullet-only plan **is viable** if we change the
diagonal witness in `DIAG_TERM` from the Omega-protected form to the
classical Curry form.  The existing iter-form proof needed Omega
because LMO can't duplicate-then-collapse; under bullet (and under
par_step too), the classical form works.

Why iter needs Omega but bullet doesn't: under LMO `sk_iter`, each
step contracts exactly one redex.  When `d = e e` reduces to
`(K H e)(SII e)`, LMO contracts the K-redex to give `H`, then
contracts redexes inside `SII e` one at a time.  The intermediate
`(I e)(I e)` is two separate expressions; LMO contracts the left's
S-redex first, then the right's, and never collapses both `(K e)(K e)`
pairs into `e e` simultaneously because LMO is one-at-a-time.
Bullet's eagerness, which kills candidate (1) by eating Omega, is
exactly what makes candidate (2) work — all four K-redexes at iter 3
fire in parallel to give `e e` at iter 4.

**Layer 5 implication (initial)**: rewrite `DIAG_TERM`'s witness as
`e = S (K H) SII`, `d = e e`, target `H d`.  The body becomes
`bullet_iter 4 d = App H d` with explicit intermediate equations
from `SK_BULLET_S_REDEX`, `SK_BULLET_K_REDEX`, and
`SK_BULLET_APP_OTHER`.  Estimated ~150 lines.

**Layer 5 implication (post-audit, 2026-05-13)**: candidate (2)
satisfies DIAG_TERM but **does not** satisfy `DIAGONAL_TERM_EXISTS`'s
two-directional K_t/KI_t contract.  Resolution adopted: swap
`halts_decider` to a halting-status output convention (see "Output
convention change" section).  Under the new convention, candidate (2)
discharges the diagonal in ~10 lines and HALTING_UNDECIDABLE closes
in ~20 lines.

## Status
|------|--------|
| `sk_bullet` + 5 SK_BULLET_* unfolds (S_T, K_T, K_REDEX, S_REDEX, APP_OTHER) | **shipped** |
| `bullet_iter` | not yet defined |
| `HALTS_B_DEF`, `HALTS_B_AT` | not yet shipped |
| `OMEGA_NON_HALTING_BULLET` | not yet shipped |
| `HALTS_B_APP_DECOMP` + `BULLET_APP_DISTRIB_ATOMHEAD` | not yet shipped |
| `HALTS_PAR_DEF`, `HALTS_PAR_AT` (partial par-relation work) | **shipped but discardable** |
| `OMEGA_NON_HALTING_PAR` + bullet-orbit helpers | **shipped but discardable** |
| `PAR_STEP_K_APP_INV`, `PAR_STEP_S_T_APP_INV`, `PAR_STEP_S_APP_APP_INV` | **shipped but discardable** |
| Bucket A deletions | not yet executed |
| Bucket B deletions | not yet executed |
| Bucket C bullet restatements | not yet executed |
| Bucket D deletions | not yet executed |
| Bucket E deletions | not yet executed |

The par-relation `halts_par` path was partially built in commits
before this doc was rewritten.  Under this plan it becomes Bucket D
(deletable infrastructure) rather than the critical path; everything
in halting.py from the `sk_par_step` definition through
`OMEGA_NON_HALTING_PAR` is on the deletion list.

## Bucket A — `sk_iter` machinery (delete outright)

Internal recursion + glue lemmas whose only purpose is making
`sk_iter` work as a primitive.  Deleted with the `sk_iter` constant
itself.

| Proof | Role under iter | Fate |
|-------|-----------------|------|
| `SK_ITER_BASE`, `SK_ITER_STEP` | recursion equations | delete with `sk_iter` |
| `SK_ITER_ZERO` | `sk_iter 0 t = t` | delete |
| `SK_ITER_SUC` | unfold one iteration | delete |
| `SK_ITER_PUSH` | `iter (S n) t = iter n (step t)` | delete |
| `SK_ITER_ADD` | additivity in the count | delete |
| `SK_ITER_TRANS` | iter composition | delete |
| `SK_ITER_PAST_NORMAL` | `is_normal → iter stays put` | delete |
| `IS_NORMAL_SK_ITER_FIXED` | iter stuck at normal | delete |
| `SK_ITER_TO_PAR_STEPS` | iter→par bridge | delete |
| `I_T_REDUCES` | `iter 2 (I x) = x` | delete; bullet equivalent if needed |
| `HALTS_AT`, `HALTS_DEF` (iter-form) | unfold | delete; replaced by `HALTS_B_AT` / `HALTS_B_DEF` |
| `HALTS_SK_ITER` | iter-form halts witness | delete |
| `HALTS_SK_STEP_FWD`, `HALTS_SK_STEP_BWD` | iter-form halts preservation | delete |
| `HALTING_REDUCTION_PRESERVED` | iter→halts equivalence | delete |
| `STANDARDIZATION_NORMAL` | the bridge no longer needed | **delete** |
| `HALTS_PAR_STEPS_INVARIANT` | the iter-based proof | delete (replaced by `HALTS_B_APP_DECOMP`) |
| `HALTS_SK_STEP_APP_LEFT` | iter-form "reduce X inside App" | **delete** — bullet has no "reduce X, leave Y" notion; replaced by `HALTS_B_APP_DECOMP` for App-other shapes |
| `SK_ITER_APP_LEFT_HALTS` | iter premise lifts to halts | delete (same reason) |

## Bucket B — Ω trajectory under sk_iter (R3 family)

These eleven proofs exist solely to drive the size-growth argument in
the existing `OMEGA_NON_HALTING`.  The bullet-form proof
(`OMEGA_NON_HALTING_BULLET`) closes the same theorem via a 3-cycle
enumeration on `sk_bullet`'s deterministic orbit and uses **none** of
them.

| Proof | Role |
|-------|------|
| `SK_NEQ_DEEP_LEFT_WRAP` | non-equality lemma for deep left positions |
| `OMEGA_PEEL_HEAD2` | peel two head sk_steps off Ω |
| `OMEGA_PEEL` | peel one head sk_step |
| `OMEGA_TO_X_IX` | Ω-shape factoring |
| `OMEGA_TRAJ_I_DEPTH_STEP` | I-depth grows along Ω's trajectory |
| `OMEGA_DEPTH_SEQ` | depth-indexed Ω-shape extraction |
| `OMEGA_T_REACHES_LARGE_SIZE` | unbounded-size iter witness |
| `OMEGA_NON_HALTING` | iter-form non-halting (200 lines) |
| `OMEGA_T_NOT_FIXED` | corollary: no iter of Ω is sk_step-fixed |
| `SK_ITER_K_OMEGA_SHAPE` | iter trajectory of `App K Ω` |
| `I_POW_SUC` | I-power recurrence (Tromp-Y feeder) |

Total: ~1500 lines deleted.  Replaced by ~120 lines inside
`OMEGA_NON_HALTING_BULLET`.

## Bucket C — bullet-form restatements

These proofs survive the migration but their statement changes from
`?n. sk_iter n …` to `bullet_iter n …`.  Replace in place.

| Proof | Current statement | Bullet-form statement | Body |
|-------|-------------------|-----------------------|------|
| ~~`CHURCH_TRUE_REDUCES`~~ | K-Boolean encoding | (deleted — convention no longer uses K_t/KI_t outputs) |
| ~~`CHURCH_FALSE_REDUCES`~~ | KI-Boolean encoding | (deleted — same) |
| ~~`HALTS_KI_OMEGA_TRUE`~~ | KI Omega discriminator | (deleted — discriminator role gone with convention swap) |
| ~~`HALTS_K_OMEGA_FALSE`~~ | K Omega discriminator | (deleted — same) |
| ~~`HALTS_SK_STEP_APP_LEFT`~~ | (deleted — see Bucket A) | n/a |
| ~~`SK_ITER_APP_LEFT_HALTS`~~ | (deleted — see Bucket A) | n/a |
| `HALTS_DECIDER_DEF` | iter K/KI in spec | replace at the new definition (`halts_b t = ~halts_b (App H t)`) |
| `HALTS_DECIDER_DEF_THM` | unfold | one-line AT-form of new def |
| `DIAGONAL_TERM_EXISTS` | par_steps premise | `?d. is_sk_term d /\ halts_b d = halts_b (App H d)` — ~10 lines from DIAG_TERM + BULLET_ITER_INVARIANT |
| `HALTING_UNDECIDABLE` | iter K/KI conclusions | 5-step contradiction (see "Output convention change" section) |
| `HALTS_NOT_SK_REPRESENTABLE` | iter restatement | mechanical mirror of new HALTING_UNDECIDABLE |

The ~~struck-through~~ entries move from Bucket C (restate) to
Bucket D (delete) under the chosen convention swap.

Total cosmetic work: ~80 lines of mechanical restatement (down from
~150 in earlier estimates).  DIAG_TERM is the heavy outlier — see
Layer 5.

## Bucket D — `sk_par_step` / `sk_par_steps` ecosystem (delete)

Everything related to the parallel-reduction *relation* goes away.
The relation is no longer needed; the *function* `sk_bullet` is the
only Takahashi artefact retained.

| Proof / definition | Role |
|--------------------|------|
| `sk_par_step`, `SK_PAR_STEP_DEF`, `_PAR_STEP_CLOSURE` | the relation |
| `PAR_REFL`, `PAR_K`, `PAR_S`, `PAR_APP` | intro rules |
| `sk_par_steps`, `SK_PAR_STEPS_DEF` | RTC |
| `PAR_STEPS_REFL`, `PAR_STEPS_STEP`, `PAR_STEP_TO_STEPS` | RTC operations |
| `PAR_STEPS_TRANS`, `PAR_STEPS_APP_LEFT` | RTC composition |
| `par_chain` (context manager) | DSL helper |
| `_par_step_to_P`, `_par_steps_to_P` | impredicative helpers |
| `PAR_STEP_S_T_INV`, `PAR_STEP_K_T_INV` | atom inversions |
| `_par_step_atom_inv` (helper) | atom-inversion template |
| `_par_step_app_atom_inv` (helper) | App-atom-inversion template |
| `PAR_STEP_K_APP_INV`, `PAR_STEP_S_T_APP_INV`, `PAR_STEP_S_APP_APP_INV` | App-shape inversions |
| `BULLET_REFL` | `par_step W (sk_bullet W)` bridge |
| `_TRIANGLE_APP_CLOSURE` | triangle's App-rule case |
| `SK_BULLET_TRIANGLE`, `TRIANGLE_EXISTS` | the triangle |
| `PAR_STEP_DIAMOND` | Takahashi diamond |
| `PAR_STEPS_STRIP`, `PAR_STEPS_CONFLUENT` | confluence |
| `NORMAL_STABILITY_PAR_STEP`, `NORMAL_STABILITY_PAR_STEPS` | normal under par |
| `SK_PAR_STEP_TO_SK_STEP`, `SK_STEP_TO_PAR_STEPS` | iter/step ↔ par bridges |
| `HALTS_PAR_DEF`, `HALTS_PAR_AT` | par-form halts |
| `OMEGA_NON_HALTING_PAR` + supporting helpers | par-form non-halting (replaced by bullet version) |
| `T1_T_DEF`, `T2_T_DEF`, `SK_BULLET_OMEGA_T`, `SK_BULLET_T1_T`, `SK_BULLET_T2_T`, `T1_T_NOT_NORMAL`, `T2_T_NOT_NORMAL`, `OMEGA_ORBIT_REACH` | par-form orbit helpers (replaced; see `OMEGA_NON_HALTING_BULLET` below) |

Total: ~1500 lines deleted (par-relation infrastructure + the
in-progress `halts_par` path).

## Bucket E — dead code (delete with sk_iter)

Tromp's Y-combinator subsystem, used only by the pre-`DIAG_TERM`
diagonal route.

| Proof / definition | Role |
|--------------------|------|
| `Y_T_DEF`, `Y_t`, `IS_SK_TERM_Y` | Tromp's 25-symbol Y combinator |
| `Y_FIXED_POINT` | `?n. iter n (Y f) = f X_TROMP_f` (7-step trace) |
| `_TROMP_X_STR`, `X_TROMP_f` | the specific 7-step reduct |
| `SK_STEP_K_UNDER_LEFT`, `SK_STEP_S_UNDER_LEFT` | Y-FP step helpers |
| `SK_STEP_K_UNDER_LEFT_LEFT` | Y-FP step helper |
| `SK_STEP_APP_FIXED` | Y-FP step helper |

Verify each helper has no surviving callers outside the Y subsystem
before deleting; some `SK_STEP_LEFT`/`SK_STEP_RIGHT` siblings *are*
still used by `SK_STEP_I_APP` and structural reasoning, so be precise.

## The new helpers

### `bullet_iter`

Nat0 iteration of `sk_bullet`:

```
BULLET_ITER_ZERO : |- !t. bullet_iter 0 t = t.
BULLET_ITER_SUC  : |- !n t. bullet_iter (SUC0 n) t = sk_bullet (bullet_iter n t).
```

Plus an `_ADD` lemma if needed by the App-other-stable family.
Standard `define_unary_0` recursion; ~30 lines.

### `HALTS_B_DEF`, `HALTS_B_AT`

```
halts_b t := ?n. is_normal (bullet_iter n t).
HALTS_B_AT : |- !t. halts_b t = (?n. is_normal (bullet_iter n t)).
```

Mirrors `HALTS_PAR_DEF` / `HALTS_PAR_AT` in shape; ~20 lines for the
unfold.

### `OMEGA_NON_HALTING_BULLET`

```
|- ~ halts_b Omega_t.
```

Proof structure:

1. **Three orbit equations** (~25 lines each).  T1, T2 are concrete
   terms; see `outside/sk_par.py` EXP 1:
   - `sk_bullet Omega_t = T1` via `OMEGA_T_DEF` + `SK_BULLET_S_REDEX`
     at X=I_t, Y=I_t, Z=SII_t.
   - `sk_bullet T1 = T2` via `SK_BULLET_APP_OTHER` + recursion into
     the I-shape sub-bullet (which unfolds `I_T_DEF` and fires
     `SK_BULLET_S_REDEX` at X=K_t, Y=K_t, Z=SII_t).
   - `sk_bullet T2 = Omega_t` via `SK_BULLET_APP_OTHER` +
     `SK_BULLET_K_REDEX` at the inner K-redex.

2. **Orbit membership invariant** (~30 lines).  By nat0 induction:

   ```
   !n. bullet_iter n Omega_t = Omega_t \/
       bullet_iter n Omega_t = T1     \/
       bullet_iter n Omega_t = T2.
   ```

   Base: `bullet_iter 0 Omega_t = Omega_t` (orbit element 1).
   Step: case-split on the IH's three branches; apply the matching
   orbit equation; conclude membership of the next iterate.

3. **Three non-normality facts** (~15 lines each):
   `~is_normal Omega_t` (already shipped as `OMEGA_T_NOT_NORMAL`),
   `~is_normal T1`, `~is_normal T2`.  Each via a head-redex
   `sk_step T_i ≠ T_i` calculation.

4. **Close** (~10 lines).  Suppose `halts_b Omega_t`, unfold to
   `?n. is_normal (bullet_iter n Omega_t)`, choose `n`, case-split via
   (2), contradict via (3).

Total: ~120 lines.  No `sk_par_step`, no triangle, no inversion.

### `HALTS_B_APP_DECOMP` and `BULLET_APP_DISTRIB_ATOMHEAD`

Replaces the originally-planned `BULLET_APP_OTHER_STABLE` family.
The cleaner factoring (uncovered while auditing
`HALTS_SK_STEP_APP_LEFT`'s role under bullet — it has none, since
bullet has no "reduce X while leaving Y" notion):

```
BULLET_APP_DISTRIB_ATOMHEAD :
  |- !n X Y. is_atom_or_atom_headed X ==>
              bullet_iter n (App_t X Y) = App_t (bullet_iter n X) (bullet_iter n Y).

HALTS_B_APP_DECOMP :
  |- !X Y. (App_t X Y stays App-other under all bullet iterates) ==>
              halts_b (App_t X Y) = (halts_b X /\ halts_b Y).
```

Proof sketches:

`BULLET_APP_DISTRIB_ATOMHEAD`: nat0 induction on n.  Base trivial.
Step: when the left is atom-headed (e.g. `K_t Y`, `H ...`, etc.),
the top App stays App-other (head can never grow into App K _ or
App (App S _) _ shape), so `SK_BULLET_APP_OTHER` fires; combine with
IH.  ~30 lines.

`HALTS_B_APP_DECOMP`: from the distributivity above, plus
`is_normal (App_t A B) = is_normal A /\ is_normal B` for App-other
(`IS_NORMAL_APP_DECOMP`), plus normal-stability under bullet (once
`bullet^n X` is normal, `bullet^(n+k) X = bullet^n X`).  Two
directions: forward by choosing n maximizing both components,
backward by intersecting the indices.  ~40 lines.

Closing `HALTS_K_OMEGA_FALSE`:

1. `App_t K_t Omega_t` stays App-other (K_t is a leaf; top App
   needs `App_t (App_t K_t _) _` to be a K-redex — never reachable).
2. `HALTS_B_APP_DECOMP` gives `halts_b (App_t K_t Omega_t) =
   halts_b K_t /\ halts_b Omega_t`.
3. `halts_b K_t = T` (K_t is normal, `bullet_iter 0 K_t = K_t`).
4. `halts_b Omega_t = F` (`OMEGA_NON_HALTING_BULLET`).
5. Therefore `halts_b (App_t K_t Omega_t) = F`.

~15 lines.

## Execution order

Each layer compiles on its own; ship them as separate commits.

### Layer 1 — Add `bullet_iter` and `halts_b`

- `bullet_iter` definition + `BULLET_ITER_ZERO` + `BULLET_ITER_SUC`
- (optional) `BULLET_ITER_ADD` if needed downstream
- `halts_b` definition + `HALTS_B_AT`

### Layer 2 — Prove `OMEGA_NON_HALTING_BULLET`

- Three orbit-equation lemmas (`SK_BULLET_OMEGA_T`, `SK_BULLET_T1_T`,
  `SK_BULLET_T2_T`).  Existing stubs already exist as Bucket D items;
  rebuild fresh here without depending on `sk_par_step` machinery.
- Three non-normality lemmas
- nat0-induction orbit-closure
- Compose into `~halts_b Omega_t`

### Layer 3 — Bullet distributivity and `halts_b` App-decomposition

- `BULLET_APP_DISTRIB_ATOMHEAD` (~30 lines) — distributivity for
  atom-headed Apps under all bullet iterates.
- `HALTS_B_APP_DECOMP` (~40 lines) — `halts_b (App X Y) = halts_b X
  /\ halts_b Y` for App-other-forever shapes.

### Layer 4 — Restate Bucket C consumers in bullet form

- `CHURCH_TRUE_REDUCES`, `CHURCH_FALSE_REDUCES`,
  `HALTS_KI_OMEGA_TRUE`, `HALTS_K_OMEGA_FALSE`
- `HALTS_DECIDER_DEF`, `HALTS_DECIDER_DEF_THM`
- `HALTING_UNDECIDABLE`, `HALTS_NOT_SK_REPRESENTABLE`

These are mechanical mirrors once Layers 2 + 3 are in place.

### Layer 5 — `DIAGONAL_TERM_EXISTS` in bullet form

Re-trace `DIAG_TERM`'s reduction trajectory using `sk_bullet` steps.
The hardest single proof in this migration.

`DIAG_TERM`'s par-form proof exhibits a `sk_par_steps` chain producing
either `K_t` or `KI_t` based on a sub-term's halting status.  The
bullet-form proof needs to exhibit a concrete `bullet_iter` index
plus the resulting term equation.

Each `PAR_K` / `PAR_S` step in the original corresponds to one
`SK_BULLET_K_REDEX` / `SK_BULLET_S_REDEX` step *at the head of the
current term*.  When the original par-step contracts an inner redex,
the bullet equivalent needs `SK_BULLET_APP_OTHER` to descend first,
then fire the inner redex on the next iteration.

Cost: ~250-350 lines, comparable to the par-form proof but with
explicit `bullet_iter` indexing.

### Layer 6 — Delete Buckets A, B, D, E

After consumers are migrated, every par-relation / sk_iter /
Ω-trajectory / Tromp-Y item is dead.  Delete with confidence; verify
no surviving call sites with a grep pass per name.

### Layer 7 — Rename and tidy

- `halts_b` → `halts`, `HALTS_B_DEF` → `HALTS_DEF`,
  `HALTS_B_AT` → `HALTS_AT`
- `OMEGA_NON_HALTING_BULLET` → `OMEGA_NON_HALTING`
- Drop the `_BULLET` suffix from Bucket C statements

The public API matches the pre-migration shape; only the semantics
of `halts` has changed (Takahashi-strategy halting instead of LMO
halting).  Classically equivalent.

## Open sorries after migration

After Layer 5: **zero** sorries in the halting pipeline.

Compared to the pre-migration state (with `STANDARDIZATION_NORMAL` +
~6 Ω-trajectory sorries open simultaneously) and the abandoned
par-relation plan (with `_TRIANGLE_APP_CLOSURE` + `BULLET_REFL` + 6
bullet/orbit helpers open simultaneously): a small bounded set of
shape-stable lemmas replaces both the standardization stack and the
triangle stack.

## Comparison with the abandoned par-relation plan

| Property | Par-relation (abandoned) | Bullet-only (this plan) |
|----------|--------------------------|--------------------------|
| New definition cost | ~50 lines (`halts_par`) | ~50 lines (`halts_b` + `bullet_iter`) |
| Non-halting proof | ~250 lines (orbit-reach + 5 stub helpers) | ~120 lines (3-cycle enum) |
| Par/triangle stack | ~600+ lines required (`_TRIANGLE_APP_CLOSURE`, `BULLET_REFL`, inversions, DIAMOND, STRIP, …) | not needed |
| Internal-step preservation | trivial via `PAR_STEPS_TRANS` | **not needed** — replaced by `HALTS_B_APP_DECOMP` (~70 lines total with helpers) |
| `DIAG_TERM` rewrite | par-form lifts (~250 lines) | bullet-form lifts (~300 lines) |
| Total infrastructure added | ~1000 lines | ~400 lines |
| Total deleted | ~1500 lines | ~3000 lines (par stack + iter + Y) |
| Open sorries after migration | 0 (if `_TRIANGLE_APP_CLOSURE` closes) | 0 |

The bullet-only plan is **strictly smaller** for the iter-elimination
goal.  The par-relation plan would be preferable if Church-Rosser
were independently needed; it's not.

## Risks

Updated after the EXP 5 spike, the `HALTS_SK_STEP_APP_LEFT` audit,
and the `DIAGONAL_TERM_EXISTS` / `HALTING_UNDECIDABLE` consumer
audit:

- **(1) is resolved via output-convention change** — candidate (2)
  satisfies `DIAG_TERM` but not `DIAGONAL_TERM_EXISTS`'s
  two-directional K/KI contract.  Resolution: swap `halts_decider` to
  the halting-status convention; see Risk 1 and the "Output
  convention change" section.
- (2) is dissolved into the cleaner `HALTS_B_APP_DECOMP` framing.
- (3) is dissolved — `HALTS_SK_STEP_APP_LEFT` has no purpose under
  bullet; consumers re-wire to `HALTS_B_APP_DECOMP`.
- (4) and (5) remain as friction items, not blockers.

**Net status**: the bullet-only plan is **viable** under the
chosen output-convention change.  Total halting pipeline ~250 lines.
Grep confirmed `halts_decider`'s K/KI shape is local to halting.py
(leaf module, no external imports); the convention swap is safe and
adopted.

### 1. `DIAG_TERM` rewrite (Layer 5) — **RE-ELEVATED to blocking by consumer audit**

Two strands of evidence:

(a) The spike found a working bullet diagonal: candidate (2),
classical Curry `e = S (K H) SII`, `d = e e`, gives
`bullet_iter 4 d = App H d` in 4 explicit steps.  That part is fine.

(b) The consumer audit (DIAGONAL_TERM_EXISTS, halting.py:11672) shows
candidate (2)'s `d` **does not** satisfy DIAG_TERM's required contract.
The contract is two-directional:

  * K_t branch: `(H d → K_t) ==> ~halts d`.
  * KI_t branch: `(H d → KI_t) ==> halts d`.

Under candidate (2), since `bullet_iter 4 d = App H d` is the *only*
recursion, the bullet trajectory continues `d → App H d → (whatever
H d is)`.  Both K_t and KI_t are normal (halting).  So:

  * KI_t branch: provable — `bullet_iter (4+n) d = KI_t` (normal), so
    `halts d`. ✓
  * K_t branch: NOT provable — `bullet_iter (4+n) d = K_t` (normal),
    so `halts d`, *not* `~halts d`.  The contract demands `~halts d`
    in this branch. ✗

The iter-form derived `~halts d` in the K_t branch via the K/KI Omega
flip: `d → (H d) Omega → K_t Omega`, which doesn't halt because Omega
is inside a one-arg K.  Under bullet, Omega cannot be embedded in the
diagonal recursion — that's the original Risk #1 cause, and it's not
fixed by candidate (2): it just relocates from the recursion
(`(H d) Omega` as d's evaluation) to the consumer-level discriminator,
which then has nowhere to attach.

HALTING_UNDECIDABLE (halting.py:11867-11885) case-splits on `halts d`
via excluded middle and needs *both* directions to contradict.  The
`halts d` case has no contradiction route under candidate (2).

**Status**: Layer 5 cannot be discharged as currently planned.  No
known bullet-only diagonal satisfies DIAG_TERM's two-directional
contract.

**Chosen resolution**: option (2), the halting-status output
convention.  Verified by audit that nothing outside `halting.py`
depends on `halts_decider`'s K_t/KI_t shape (it's a leaf module).
See the "Output convention change" section below for the precise
definition swap, pipeline, and Bucket C impact.

Discarded alternatives:

1. **New diagonal under bullet** that produces `App (H d) Y` for some
   non-halting `Y` reachable in d's bullet trajectory.  Multiple
   candidates ruled out by EXP 5 (Omega-protected, I-doubled);
   Tromp-style Y-combinator applied to `\\x. (H x) Omega = S H (K Omega)`
   has the same K-Omega-eaten problem inside g.  Open question
   whether *any* SK term can encode the K/KI Omega flip under
   bullet's eager-everywhere semantics — not pursued.

3. **Hybrid plan**: keep bullet for OMEGA_NON_HALTING and most of the
   pipeline, but keep `sk_par_step` (and triangle / App-inversions)
   for `DIAG_TERM`'s diagonal proof.  Brings back ~600 lines of par-
   relation infrastructure for no semantic gain over (2).  Rejected.

## Output convention change (Risk 1 recovery option 2 — chosen path)

Audit (2026-05-13):

```
$ grep -rln "from halting|import halting|halts_decider|
            HALTING_UNDECIDABLE|HALTS_NOT_SK_REPRESENTABLE" --include='*.py' .
./halting.py
```

No external dependency.  `halting.py` is currently a leaf module; the
K_t/KI_t output convention in `halts_decider` is internal.
`halts_decider`'s only consumers are `HALTING_UNDECIDABLE` and
`HALTS_NOT_SK_REPRESENTABLE` (both inside halting.py), which we are
restating anyway.  Safe to change the definition outright.

### The change

**Old definition** (`halting.py:6474`):

```
halts_decider H := is_sk_term H /\
                   !t. is_sk_term t ==>
                       (halts t  ==> ?n. sk_iter n (App_t H t) = K_t) /\
                       (~halts t ==> ?n. sk_iter n (App_t H t) = KI_t)
```

**New definition**:

```
halts_decider H := is_sk_term H /\
                   !t. is_sk_term t ==>
                       halts_b t = ~halts_b (App_t H t)
```

The decider's output's *halting status* encodes the answer, with the
flipped convention "decider output doesn't halt iff input halts."
The K_t / KI_t syntactic encoding is gone.

Why flipped (not the natural `halts_b t = halts_b (App_t H t)`):
candidate (2)'s diagonal gives `halts_b d = halts_b (App H d)`
unconditionally, so an unflipped spec is vacuously satisfied and gives
no contradiction.  The flipped spec turns `halts_b d = halts_b (App H d)`
into `halts_b d = ~halts_b d`, which is the contradiction.

### Pipeline

1. `bullet_iter` + `halts_b` (Layer 1, unchanged).
2. `OMEGA_NON_HALTING_BULLET` (Layer 2, unchanged).
3. `BULLET_APP_DISTRIB_ATOMHEAD` + `HALTS_B_APP_DECOMP` (Layer 3,
   unchanged).
4. **New** Layer 3.5 — `BULLET_ITER_INVARIANT`:
   ```
   |- !n X. halts_b X = halts_b (bullet_iter n X).
   ```
   Trivial offset on the existential index inside `halts_b`'s
   definition.  ~15 lines.
5. **DIAG_TERM** (Layer 5, simplified): `!H. is_sk_term H ==>
   ?d. is_sk_term d /\ bullet_iter (SUC0 (SUC0 (SUC0 (SUC0 0)))) d =
   App_t H d.`  ~150 lines (the spike-validated trajectory).
6. **DIAGONAL_TERM_EXISTS** (Bucket C, simplified): `!H. is_sk_term H
   ==> ?d. is_sk_term d /\ halts_b d = halts_b (App_t H d).`  Derived
   from DIAG_TERM + BULLET_ITER_INVARIANT.  ~10 lines.
7. **HALTING_UNDECIDABLE** (simplified):
   ```
   |- ~ ?H. halts_decider H.
   ```
   Proof, ~20 lines:
   - Suppose `?H. halts_decider H`; choose H.
   - Unfold via `HALTS_DECIDER_DEF_THM`: get `!t. is_sk_term t ==>
     halts_b t = ~halts_b (App_t H t)`.
   - Apply `DIAGONAL_TERM_EXISTS` at H: choose d with `is_sk_term d`
     and `halts_b d = halts_b (App_t H d)`.
   - Specialise decider spec at t := d: `halts_b d = ~halts_b (App_t H d)`.
   - Combining: `halts_b (App_t H d) = ~halts_b (App_t H d)`.  Absurd.

Total halting pipeline: ~250 lines.  No K/KI Omega trick, no Omega
in the diagonal, no triangle.

### Bucket C impact

Several entries become trivial or redundant under the new convention:

| Lemma | Old role | Bullet-form fate |
|-------|----------|-------------------|
| `CHURCH_TRUE_REDUCES` | `iter (K X Y) = X` for Boolean True | **delete** if no consumer remains; was used only via the K_t output encoding |
| `CHURCH_FALSE_REDUCES` | analogous for KI | **delete** if no consumer remains |
| `HALTS_KI_OMEGA_TRUE` | `halts (KI Omega)` for the KI_t branch flip | **delete** — the diagonal no longer uses KI Omega |
| `HALTS_K_OMEGA_FALSE` | `~halts (K Omega)` for the K_t branch flip | **delete** — same reason |
| `HALTS_DECIDER_DEF` / `_THM` | unfold the K/KI spec | restate at the new definition |
| `DIAGONAL_TERM_EXISTS` | K/KI-branch contracts | restate as `halts_b d = halts_b (App H d)` |
| `HALTING_UNDECIDABLE` | use K/KI flip in the case-split | restate per pipeline step 7 above |
| `HALTS_NOT_SK_REPRESENTABLE` | corollary | mechanical mirror of new HALTING_UNDECIDABLE |

The `CHURCH_*_REDUCES` and `HALTS_*_OMEGA_*` lemmas were previously
mandatory Bucket C restatements; under 2a they become Bucket D
deletions.  Net saving: ~80 more lines deleted.

### 2. `_STABLE` catalog size — **resolved into App-decomposition**

Initial concern: every distinct App-shape the diagonal walks through
needs its own `_STABLE` lemma; 6-10 shapes would balloon the family.

EXP 5 candidate (2) shows the actual shape exposure is much smaller
— the 4-step trajectory uses per-iter explicit rewrites, not a
universally-quantified family.  Further auditing (see Risk 3 below)
showed that the only `_STABLE` lemma the consumers actually need is
a generic distributivity + a halts-decomposition lemma:

- `BULLET_APP_DISTRIB_ATOMHEAD` (~30 lines) — `App` with atom-headed
  left stays App-other under all bullet iterates.
- `HALTS_B_APP_DECOMP` (~40 lines) — `halts_b (App X Y) = halts_b X
  /\ halts_b Y` for App-other-forever shapes.

Closing `HALTS_K_OMEGA_FALSE` via these is a ~15-line consequence
(`halts_b K_t /\ halts_b Omega_t = T /\ F = F`), with no
specialized `APP_K_OMEGA_BULLET_STABLE` lemma needed — the generic
distributivity covers it.

Total ~70 lines.  Below the original ~100 budget; below the
intermediate ~50-80 estimate from the first spike-driven revision.

Shape-stability gotcha (still real but unencountered on this path):
`App_t X (App_t Y Z)` where X bullets to `App_t K_t _` would *create*
a new K-redex at the next bullet step, breaking distributivity.
Candidate (2)'s trajectory does not hit this case because the head
remains atom-shaped throughout, so `BULLET_APP_DISTRIB_ATOMHEAD`'s
guard is satisfied.

### 3. ~~`HALTS_SK_STEP_APP_LEFT` semantic mismatch~~ — **dissolved**

Initial concern: the iter-form `HALTS_SK_STEP_APP_LEFT` consumer
needs "reduce X internally, leave Y fixed", which has no bullet
analog.

Resolution: the lemma has *no purpose* under bullet halting.  Bullet
fundamentally reduces both children of an App in lockstep; there is
no "internal reduction with sibling fixed."  But the bullet world
gives a structurally different lemma — `HALTS_B_APP_DECOMP` — that
covers every iter-form consumer that was using
`HALTS_SK_STEP_APP_LEFT`.

- iter-form consumer: "X reduces to X' inside App ==> halts (App X
  Y) = halts (App X' Y)".  Used to evaluate one child to expose
  structure.
- bullet replacement: `halts_b (App X Y) = halts_b X /\ halts_b Y`
  (under App-other-forever).  Same effect achieved by direct
  decomposition rather than internal reduction.

Migration impact: `HALTS_SK_STEP_APP_LEFT` and
`SK_ITER_APP_LEFT_HALTS` move from Bucket C (restate) to Bucket A
(delete outright).  All consumers re-wired to `HALTS_B_APP_DECOMP`.

### 4. `is_normal` definition coupling

`IS_NORMAL_DEF` is `sk_step X = X`.  The bullet world's natural
normality test is `sk_bullet X = X`.  These *should* be equivalent
(both equivalent to "has no redex"), but if the existing codebase
reasons about `is_normal` via `sk_step` somewhere the bullet plan
touches, you may need to prove
`IS_NORMAL_BULLET_FIXED : is_normal X = (sk_bullet X = X)`.
Not hard but not free; not currently in the plan's budget.

### 5. nat0 induction friction on the 3-way orbit invariant

The orbit-membership induction (`bullet_iter n Omega_t IN
{Omega, T1, T2}`) has an IH with a 3-way right-associated disjunct;
the step case-splits on three IH branches and applies the matching
orbit equation.  Clean on paper, but DSL-level friction with
disjunction destructure + `BULLET_ITER_SUC` unfold + simp-matching
the result could push it past the budgeted 30 lines.  Bounded
risk; will surface immediately in Layer 2.

## What this doesn't fix

- `sk_step` (single LMO contraction) survives — used as a concrete
  notion of reduction outside the halting pipeline.  Only `sk_iter`
  (the iteration) and the par-relation machinery go away.

- The semantic content of "halting" changes: `halts_b` is the
  Takahashi-strategy halting notion ("the bullet trajectory reaches
  normal") rather than the deterministic-LMO notion ("the leftmost-
  outermost reduction reaches normal").  Classically equivalent (by
  standardization), but in this codebase the equivalence is exactly
  the deleted `STANDARDIZATION_NORMAL`.  If the equivalence is later
  required for some other purpose, it returns as a fresh obligation;
  the migration only removes it from the *halting undecidability*
  critical path.

## Files touched

- `halting.py`: the migration site; ~3000 lines deleted, ~400 lines
  added.
- `outside/sk_par.py`: empirical witness for Ω's bullet orbit; **no
  change** — used as reference for `OMEGA_NON_HALTING_BULLET` but
  not consumed by the kernel.
- `outside/sk_trace.py`: unchanged.
