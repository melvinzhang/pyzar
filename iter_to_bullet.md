# Migration: `halts` over `sk_iter` → `halts_b` over `bullet_iter`

> **Strategy revised 2026-05-13** (post composite-H stress test).
> The original "bullet everywhere, including DIAG_TERM" path was
> falsified empirically — see [Post-spike audit](#post-spike-audit-2026-05-13-composite-h-falsifies-bullet-only-diag_term).
> The migration now adopts **Option C**: keep `halts_b` (bullet) as
> the user-facing halt predicate and the basis for everything except
> the diagonal; prove DIAG_TERM in par form using `sk_par_step`'s
> REFL freedom; bridge the result back to `halts_b` once via
> `HALTS_B_IFF_HALTS_PAR`.  `sk_iter` still goes away.  Some of the
> par-relation infrastructure originally slated for deletion is
> retained — see the updated [Bucket D](#bucket-d--sk_par_step--sk_par_steps-ecosystem-partial-keep).

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

## Post-spike audit (2026-05-13): composite H falsifies bullet-only DIAG_TERM

The original spike treated `H` as an opaque atom — both in the
simulator (`('H',)` as a leaf) and implicitly in the trajectory
claim.  A follow-up stress test in `outside/sk_par.py` instantiated
H to representative composite SK terms (every `is_sk_term`
inhabitant the universal quantifier `!H` ranges over):

| H instantiation | iter 4 outcome | App H d reachable? |
|-----------------|----------------|-----|
| atomic, K, S, S K | iter 4 = App H d exactly | ✓ |
| K K (normal, K-headed) | iter 3 collapses to bare `K` | ✗ |
| K (S K) (normal, K-headed) | iter 3 collapses to `S K` | ✗ |
| K K K (K-redex) | iter 4 = `App K (...)`, H has reduced | ✗ |
| I = S K K (S-redex) | period-4 cycle; iter 4 = original d | ✗ |

The trajectory equation `bullet_iter 4 d = App_t H d` is therefore
**false** as a universal statement over `is_sk_term H`.  Two
distinct obstructions:

1. **App-H-d-as-redex.** When H = `App_t K_t a` (any K-headed App)
   or H = `App_t (App_t S_t a) b` (S-headed-1arg), the term
   `App_t H d` is *itself* a K- or S-redex.  At iter 2 the trajectory
   already produces an `App_t H (residue)` subterm; the next bullet
   step fires the new redex and collapses the App-shape before iter 4.
2. **H-reduces-mid-trajectory.** When `sk_bullet H ≠ H` (H itself is
   non-normal, e.g. `K K K` or any Y-encoded decider), the H subterms
   inside the iter trajectory reduce in place, so the H-residue at
   iter 4 is no longer the H we started with.

The docstring obstruction analysis filed in `halting.py:_DIAG_BULLET_TRAJ`
(claiming `sk_bullet^k H` residual accumulation) was inaccurate; the
simulator faithfully reflects HOL's `SK_BULLET_DEF` (D4 fires on any
non-App leaf, giving `sk_bullet H = H` for atomic H), so the actual
obstructions are (1) and (2) above.

### Alternative-witness spike: Turing's Θ = AA (EXP 6)

A second spike (sk_par.py EXP 6) tested whether a different fixed-
point combinator might avoid the obstruction.  Result: **strictly
worse** than Curry under bullet.  Turing's `Θ H = A A H` with
`A = S(K(SI))(SII)` never reaches `App H (Θ H)` exactly — for **any**
H, including atomic.  Bullet's eager parallel reduction destroys the
fixed-point identity `Θ H →_β H (Θ H)`, which crucially requires
*not* reducing the inner Θ H.

For atomic H, Turing's trajectory builds an unbounded H-stack
(`H (H (H (...)))`) at the head instead of stabilizing on
`App H (Θ H)`.  For composite H, it collapses similarly to Curry.

This isn't a defect of Turing's specific encoding — every fixed-
point combinator relies on the same "keep one copy un-reduced"
trick, which bullet's complete-development semantics rules out.
No bullet-only diagonal witness exists.

### Why Option C is forced

Three other options were considered:

- **(a)** Strengthen the hypothesis on H (`is_normal H` plus K/S-head
  guards).  Excludes Y-combinator-based deciders, which are the
  natural construction.  Weakens the theorem to "no head-stable,
  non-K/S-headed SK term decides halting."  Too weak.
- **(K)** Semantic / confluence argument: prove `?N M. bullet_iter N
  d = bullet_iter M (App H d)` without an explicit trajectory.
  Common reducts always exist empirically (verified for all stress
  cases; N ranges 0..18, M ranges 0..2), but proving the existence
  in HOL still requires Church-Rosser for bullet, which requires
  par as an auxiliary calculus.  K is cosmetically distinct from
  Option C but the proof cost is the same.
- **(L)** Different witness (Turing-style).  Falsified empirically
  by EXP 6, as documented above.

That leaves **Option C**: par-step has `PAR_REFL`, which is the
"keep un-reduced" operation that fixed-point combinators (and the
classical Curry diagonal under composite H) require.  Bullet stays
right for the determinism-friendly parts of halting; par enters as
a one-off auxiliary for the diagonal proof, gated by a single
bridge lemma.

## Status

| Item | State |
|------|-------|
| `sk_bullet` + 5 SK_BULLET_* unfolds (S_T, K_T, K_REDEX, S_REDEX, APP_OTHER) | **shipped** |
| `bullet_iter` | not yet defined |
| `HALTS_B_DEF`, `HALTS_B_AT` | not yet shipped |
| `OMEGA_NON_HALTING_BULLET` | not yet shipped |
| `HALTS_B_APP_DECOMP` + `BULLET_APP_DISTRIB_ATOMHEAD` | **likely not needed** under Option C (audit Layer 4) |
| `HALTS_PAR_DEF`, `HALTS_PAR_AT` | **shipped, retained for Option C** |
| `sk_par_step` + REFL/K/S/APP intros + `sk_par_steps` RTC | **shipped, retained for Option C** |
| `BULLET_REFL` | **shipped, retained — feeds the bridge** |
| `SK_BULLET_TRIANGLE` + `_TRIANGLE_APP_CLOSURE` (stubbed) | **shipped (stub), needed for bridge — must close** |
| `HALTS_B_IFF_HALTS_PAR` (bridge) | **new — not yet shipped** |
| `OMEGA_NON_HALTING_PAR` + T1_T/T2_T par-orbit helpers | **shipped but discardable** (bullet version replaces) |
| `PAR_STEP_K_APP_INV`, `PAR_STEP_S_T_APP_INV`, `PAR_STEP_S_APP_APP_INV` | **shipped, discardable if not needed by triangle** |
| `PAR_STEP_DIAMOND`, `PAR_STEPS_STRIP`, `PAR_STEPS_CONFLUENT` | **shipped, discardable** (triangle alone suffices for bridge) |
| Bucket A deletions | not yet executed |
| Bucket B deletions | not yet executed |
| Bucket C bullet restatements | not yet executed |
| Bucket D **partial** deletions (revised) | not yet executed |
| Bucket E deletions | not yet executed |

Under **Option C**, the `sk_par_step` ecosystem is no longer
wholesale deletable.  The minimal kept set is:

- `sk_par_step` relation + four intro rules (REFL, PAR_K, PAR_S, PAR_APP)
- `sk_par_steps` RTC + `PAR_STEPS_REFL`, `_STEP`, `_TRANS`, `_APP_LEFT`,
  `PAR_STEP_TO_STEPS`
- `BULLET_REFL` (each bullet step is a par-step)
- `SK_BULLET_TRIANGLE` + `_TRIANGLE_APP_CLOSURE`
- `NORMAL_STABILITY_PAR_STEP` / `_PAR_STEPS`
- `HALTS_PAR_DEF` + `HALTS_PAR_AT`

The deletable subset stays Bucket D: iter/step↔par bridges (go away
with `sk_iter`), `OMEGA_NON_HALTING_PAR` (replaced by bullet 3-cycle),
T1_T/T2_T par-orbit helpers, the impredicative `_par_step_to_P` /
`_par_steps_to_P` and inversion templates (only used by the abandoned
par-everywhere plan), and — pending audit — DIAMOND/STRIP/CONFLUENT
(the bridge needs *triangle* but not general confluence).

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

## Bucket D — `sk_par_step` / `sk_par_steps` ecosystem (partial keep)

Under Option C the parallel-reduction relation is retained as the
auxiliary calculus for the diagonal, plus the bridge `HALTS_B_IFF_HALTS_PAR`.
The deletable subset is everything that supported the abandoned
"par everywhere, including halt predicate" plan.

| Proof / definition | Role | Fate |
|--------------------|------|------|
| `sk_par_step`, `SK_PAR_STEP_DEF`, `_PAR_STEP_CLOSURE` | the relation | **keep** |
| `PAR_REFL`, `PAR_K`, `PAR_S`, `PAR_APP` | intro rules | **keep** |
| `sk_par_steps`, `SK_PAR_STEPS_DEF` | RTC | **keep** |
| `PAR_STEPS_REFL`, `PAR_STEPS_STEP`, `PAR_STEP_TO_STEPS` | RTC operations | **keep** |
| `PAR_STEPS_TRANS`, `PAR_STEPS_APP_LEFT` | RTC composition | **keep** |
| `par_chain` (context manager) | DSL helper | **keep** (used by par DIAG_TERM) |
| `_par_step_to_P`, `_par_steps_to_P` | impredicative helpers | delete if unused by bridge/diag |
| `PAR_STEP_S_T_INV`, `PAR_STEP_K_T_INV` | atom inversions | delete if unused by triangle |
| `_par_step_atom_inv` (helper) | atom-inversion template | delete if unused |
| `_par_step_app_atom_inv` (helper) | App-atom-inversion template | delete if unused |
| `PAR_STEP_K_APP_INV`, `PAR_STEP_S_T_APP_INV`, `PAR_STEP_S_APP_APP_INV` | App-shape inversions | delete if unused by triangle |
| `BULLET_REFL` | `par_step W (sk_bullet W)` bridge | **keep** (used by bridge forward dir) |
| `_TRIANGLE_APP_CLOSURE` | triangle's App-rule case | **keep — must close stub** |
| `SK_BULLET_TRIANGLE`, `TRIANGLE_EXISTS` | the triangle | **keep — must close stub** |
| `PAR_STEP_DIAMOND` | Takahashi diamond | delete (triangle alone suffices) |
| `PAR_STEPS_STRIP`, `PAR_STEPS_CONFLUENT` | confluence | delete (triangle alone suffices) |
| `NORMAL_STABILITY_PAR_STEP`, `NORMAL_STABILITY_PAR_STEPS` | normal under par | **keep** (used by bridge backward dir) |
| `SK_PAR_STEP_TO_SK_STEP`, `SK_STEP_TO_PAR_STEPS` | iter/step ↔ par bridges | **delete** (goes with `sk_iter`) |
| `HALTS_PAR_DEF`, `HALTS_PAR_AT` | par-form halts | **keep** (one side of bridge) |
| `OMEGA_NON_HALTING_PAR` + supporting helpers | par-form non-halting | **delete** (replaced by bullet version) |
| `T1_T_DEF`, `T2_T_DEF`, `SK_BULLET_OMEGA_T`, `SK_BULLET_T1_T`, `SK_BULLET_T2_T`, `T1_T_NOT_NORMAL`, `T2_T_NOT_NORMAL`, `OMEGA_ORBIT_REACH` | par-orbit helpers | **delete** (bullet 3-cycle replaces) |

Audit each "delete if unused by bridge/diag" entry once the bridge
and par-form DIAG_TERM are written — anything not in a call chain
goes.

Total: ~800 lines deleted (Bucket D revised), ~500 lines of par
infrastructure retained for the bridge + diagonal.

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

### `HALTS_B_IFF_HALTS_PAR` (the bridge — Option C's new central lemma)

```
HALTS_B_IFF_HALTS_PAR : |- !X. halts_b X = halts_par X.
```

This is the one-off bridge that lets the par-form DIAG_TERM
discharge a `halts_b` goal.  Two directions:

**Forward (`halts_b X ==> halts_par X`)**: trivial via `BULLET_REFL`.
Each `bullet_iter` step is one `sk_par_step` (BULLET_REFL gives
`par_step W (sk_bullet W)`), so a finite bullet trajectory to a
normal form witnesses `sk_par_steps X N /\ is_normal N`.
~10 lines.

**Backward (`halts_par X ==> halts_b X`)**: the substantive direction.
Suppose `?N. sk_par_steps X N /\ is_normal N`.  Induct on the
par-step count to show `?n. is_normal (bullet_iter n X)`:

- **0 steps**: `X = N`, so `bullet_iter 0 X = X = N` is normal.  ✓
- **k+1 steps**: there exists `Y` with `par_step X Y` and
  `sk_par_steps Y N`.  By `SK_BULLET_TRIANGLE`, `par_step Y (sk_bullet X)`.
  Compose: `sk_par_steps (sk_bullet X) N` (via PAR_STEPS_STEP +
  PAR_STEPS_TRANS).  By the inductive hypothesis applied to
  `sk_bullet X`, `?m. is_normal (bullet_iter m (sk_bullet X)) =
  is_normal (bullet_iter (m+1) X)`.  ✓

Total: ~50 lines, gated on `SK_BULLET_TRIANGLE` closing.

The bridge consumes triangle but not diamond/confluence/strip:
those are needed only for *general* CR theorems; the bridge's
asymmetric "par→bullet" direction collapses on triangle alone.

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

### Layer 5 — `DIAG_TERM` in par form + bridge to bullet

Under Option C, DIAG_TERM is proved in *par form* (where `PAR_REFL`
makes it tractable for arbitrary `is_sk_term H`), then bridged to
the bullet form via `HALTS_B_IFF_HALTS_PAR`.  Three sub-proofs:

**5a. `SK_BULLET_TRIANGLE` (closing the existing stub).**  The
shipped triangle is a sorry-stubbed lemma with `_TRIANGLE_APP_CLOSURE`
as its missing inductive case.  Structural induction on the par-step
derivation:

- REFL: trivial.
- PAR_K, PAR_S: redex cases — compute both sides via `SK_BULLET_K_REDEX`
  / `SK_BULLET_S_REDEX` and conclude par-step on the residuals using
  IH on the sub-derivations.
- PAR_APP: the residual case `_TRIANGLE_APP_CLOSURE` — case-split on
  whether the App is a K-redex shape, S-redex shape, or App-other.
  Each branch fires the matching `SK_BULLET_*` and reassembles
  with the IH on subterms.

Cost: ~150-250 lines.  Largest residual risk in the migration —
see Risks #1.

**5b. Par-form `DIAG_TERM`.**

```
DIAG_TERM_PAR : |- !H. is_sk_term H ==>
                       ?d. is_sk_term d /\
                           ?N. sk_par_steps d N /\ sk_par_steps (App_t H d) N.
```

Witness `d = App_t e e` with `e = S (K H) SII` (Curry, classical).
The par-step chain (using `par_chain`):

1. `d = (S (K H) SII) e  →_PAR_S  (K H e) (SII e)`  — fire outer S
   with `x = K H`, `y = SII`, `z = e`, all REFL.
2. `(K H e) (SII e) →_PAR_K-on-left  (H) (SII e)`  — fire inner K
   on the left with `a = H`, leaving `SII e` untouched via REFL.
   Output: `App H (SII e)`.
3. To reach a common par-reduct with `App H d`, both sides reduce
   `SII e ↠_par e e = d`: via PAR_S on `(S I I) e` plus PAR_K on the
   resulting `(I e)(I e)` (each `I e = (S K K) e →_PAR_S (K e)(K e)
   →_PAR_K e`).  Two par-steps.

Total: ~80-120 lines using `par_chain` DSL.  The crucial difference
from the bullet-form proof: at step 2, `PAR_K` allows leaving `SII e`
unreduced via REFL — bullet cannot.  This is the move that bullet
forbids and that the composite-H stress test broke.

**5c. `DIAGONAL_TERM_EXISTS` (Bucket C entry, derived).**

```
DIAGONAL_TERM_EXISTS : |- !H. is_sk_term H ==>
                              ?d. is_sk_term d /\ halts_b d = halts_b (App_t H d).
```

Proof: choose H, apply `DIAG_TERM_PAR` to get `d`, `N` with
`sk_par_steps d N` and `sk_par_steps (App_t H d) N`.  These give
`halts_par d = halts_par N = halts_par (App_t H d)` (par-step
preserves halt status via NORMAL_STABILITY).  Lift through
`HALTS_B_IFF_HALTS_PAR` on both sides.  ~10-15 lines.

Total Layer 5: ~250-400 lines (triangle dominates).

### Layer 6 — Delete Buckets A, B, D (revised), E

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

After Layer 5: **zero** sorries in the halting pipeline, gated on
`SK_BULLET_TRIANGLE` / `_TRIANGLE_APP_CLOSURE` closing (~150-250
lines; see Risk #1).

The triangle stub is the single load-bearing sorry remaining.  The
abandoned par-everywhere plan needed triangle + DIAMOND + STRIP +
CONFLUENT + 6 bullet/orbit helpers; Option C needs *only* triangle.
DIAMOND and confluence are not on the critical path because the
bridge's "par→bullet" direction is asymmetric — it uses triangle
to march bullet forward along a par chain, never needing to join
two par-reducts.

## Comparison: three plans

| Property | Par-relation (abandoned) | Bullet-only (falsified by composite-H) | **Option C (current)** |
|----------|--------------------------|----------------------------------------|------------------------|
| New definition cost | ~50 lines (`halts_par`) | ~50 lines (`halts_b` + `bullet_iter`) | ~50 lines (both — `halts_b` user-facing, `halts_par` internal) |
| Non-halting proof | ~250 lines (orbit-reach + 5 stub helpers) | ~120 lines (3-cycle enum) | ~120 lines (same bullet 3-cycle) |
| Par stack (retained) | ~1000 lines (full, including DIAMOND/STRIP/CONFLUENT) | 0 | ~500 lines (relation + RTC + triangle + normal-stability, no DIAMOND) |
| Bridge `HALTS_B_IFF_HALTS_PAR` | n/a | n/a | ~50 lines (gated on triangle) |
| Triangle stack | needed (~250-400 lines incl. App closure) | not needed | needed (~150-250 lines, App closure only) |
| `HALTS_B_APP_DECOMP` family | n/a | ~70 lines | **likely unneeded** (no Bucket C consumer requires it) |
| `DIAG_TERM` rewrite | par-form (~250 lines) | bullet-form ~300 lines (FALSIFIED for composite H) | par-form (~100 lines, classical Curry) |
| Total infrastructure added | ~1000 lines | ~400 lines (broken) | ~700 lines |
| Total deleted | ~1500 lines | ~3000 lines | ~2500 lines |
| Open sorries after migration | 0 if triangle + DIAMOND close | 0 — but **theorem statement weakens** | 0 if triangle closes |
| Theorem strength | full `!H. is_sk_term H ==> …` | partial (excludes Y-encoded H) | full `!H. is_sk_term H ==> …` |

Option C is the **smallest plan that preserves the theorem strength**.
Bullet-only is smaller on paper but its DIAG_TERM is empirically
falsified for composite H — so the line count is moot.

## Output convention change (chosen resolution for Risk 1)

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

### Pipeline (revised for Option C)

1. `bullet_iter` + `halts_b` (Layer 1, unchanged).
2. `OMEGA_NON_HALTING_BULLET` (Layer 2, unchanged).
3. `BULLET_APP_DISTRIB_ATOMHEAD` + `HALTS_B_APP_DECOMP` (Layer 3 —
   **audit whether still needed**; no Bucket C consumer references
   them under the chosen convention).
4. `BULLET_ITER_INVARIANT` (~15 lines).  Useful regardless; keeps
   the existential-offset rewrite on `halts_b` available.
5. **`SK_BULLET_TRIANGLE`** (Layer 5a, ~150-250 lines).  Close the
   existing stub via structural induction on par-step derivation;
   `_TRIANGLE_APP_CLOSURE` is the missing case.  This is the single
   load-bearing piece of Option C.
6. **`HALTS_B_IFF_HALTS_PAR`** (Layer 5a continued, ~50 lines).
   Bridge via BULLET_REFL (forward) and triangle (backward).
7. **`DIAG_TERM_PAR`** (Layer 5b, ~100 lines).  Classical Curry
   diagonal in par form using `par_chain` and `PAR_REFL` to leave
   sub-terms unreduced.  Works for arbitrary `is_sk_term H`.
8. **`DIAGONAL_TERM_EXISTS`** (Layer 5c, ~10-15 lines).  Compose
   `DIAG_TERM_PAR` with `HALTS_B_IFF_HALTS_PAR` and
   `NORMAL_STABILITY_PAR_STEPS` to land on
   `?d. is_sk_term d /\ halts_b d = halts_b (App_t H d)`.
9. **HALTING_UNDECIDABLE** (simplified):
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

Total halting pipeline: ~700 lines (under Option C, triangle
dominates).  No K/KI Omega trick, no Omega in the diagonal, no
standardization.  Triangle is needed but contained.

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

## Risks

All design-level unknowns have been resolved — see "Resolved during
design" below.  The remaining risks are HOL-discharge cost estimates;
the design is stable.  Ranked by volume of residual risk.

### 1. `SK_BULLET_TRIANGLE` HOL discharge (~150-250 lines, untested)

The triangle property
```
|- !X Y. sk_par_step X Y ==> sk_par_step Y (sk_bullet X)
```
is shipped as a sorry in halting.py.  Closing it is the single
load-bearing piece of Option C — every other Layer-5 step composes
existing machinery.  The missing inductive case is
`_TRIANGLE_APP_CLOSURE`: the PAR_APP rule's residual obligation
where both subterms have par-step witnesses.

Structural induction on the par-step derivation, four cases:
- PAR_REFL → trivial (sk_bullet X par-steps to itself via REFL).
- PAR_K, PAR_S → redex cases.  `SK_BULLET_K_REDEX` /
  `SK_BULLET_S_REDEX` compute `sk_bullet X` directly; the par-step
  on the residual is reassembled from IH on sub-derivations.
- PAR_APP → the residual case.  Case-split on whether `X = App_t a b`
  is a K-redex shape, S-redex shape, or App-other; in each branch
  fire the matching `SK_BULLET_*` unfold and compose IHs.

Plausible range: 150-250 lines.  Heavier than the bullet-only
Layer 5's per-iteration term reasoning, but a single proof.

**De-risking move**: write the PAR_REFL and PAR_K cases first
(simplest); calibrate per-case line cost; extrapolate.  If the
App-shape case-split grows past 100 lines, consider routing through
intermediate lemmas (one per K/S/App-other shape) rather than a
monolithic case-split.

### 1b. `DIAG_TERM_PAR` HOL discharge (~80-150 lines)

Par-form classical Curry diagonal using `par_chain`.  The
trajectory:
```
  d = (S (K H) SII) e  →_PAR_S  (K H e) (SII e)
                       →_PAR_K_left  H (SII e)
  App H d = H ((S (K H) SII) e)  →_PAR_REFL on H, PAR_S on e
                                  H ((K H e)(SII e))  →_PAR_K_inside  ...
```
needs both sides to reach a common par-reduct of the form
`App H ((I e)(I e))` or equivalent.  `par_chain` makes the
chaining mechanical; the friction is the term-size of the
intermediate equations.

### 2. OMEGA_NON_HALTING_BULLET orbit equations (~75 lines, untested)

`sk_bullet Omega_t = T1`, `sk_bullet T1 = T2`, `sk_bullet T2 = Omega_t`
were stubbed earlier in halting.py but never discharged.  The middle
equation is the trickiest: T1 contains `App I_t SII_t` sub-terms,
and bullet recognizes the S-redex inside only after `I_T_DEF` is
folded into the existential proof inside `_sk_bullet_F`'s D2
disjunct.  No calibration on actual line cost.

### 3. is_sk_term cascade for the par-form diagonal (~40-60 lines)

Mirrors the existing iter-form `DIAG_TERM` cascade
(halting.py:11424-11458) but for the smaller Curry witness
(`e = S (K H) SII`, no `K Omega` term).  Structurally simpler, so
should be shorter.  Bounded but worth budgeting.

### 4. OMEGA_NON_HALTING_BULLET orbit-membership induction (~30-50 lines)

`!n. bullet_iter n Omega_t IN {Omega, T1, T2}` by nat0 induction.
The 3-way right-associated disjunct in the IH branch has DSL friction
(disjunction destructure + `BULLET_ITER_SUC` unfold + simp-matching);
could push past the 30-line budget but bounded.

### 5. Possibly redundant: HALTS_B_APP_DECOMP under Option C

The four lemmas `HALTS_B_APP_DECOMP` was meant to support
(`HALTS_K_OMEGA_FALSE`, `HALTS_KI_OMEGA_TRUE`, `CHURCH_*_REDUCES`)
are Bucket D deletions under the output-convention swap.  The
remaining Layer-5 entries (`DIAG_TERM_PAR`, `HALTS_B_IFF_HALTS_PAR`,
`DIAGONAL_TERM_EXISTS`, `HALTING_UNDECIDABLE`) all route through
the bridge — *not* through App-decomposition.  So
`HALTS_B_APP_DECOMP` + `BULLET_APP_DISTRIB_ATOMHEAD` (Layer 3) may
dissolve entirely, saving ~70 lines.

Confirm during Layer 4 audit before committing the work.

### 6. Audit Bucket D's "delete if unused" entries

Several par-relation items are tentatively retained but may turn out
unused once the bridge + DIAG_TERM_PAR are written: the impredicative
`_par_step_to_P` / `_par_steps_to_P`, the atom/App inversions, and
the `_par_step_atom_inv` / `_par_step_app_atom_inv` templates.

If the triangle proof requires inversions (likely for the App-shape
case-split in `_TRIANGLE_APP_CLOSURE`), they stay.  If not, they
delete.  Final accounting in Layer 6.

### Resolved during design

| # | Risk | Status | Resolution |
|---|------|--------|------------|
| R1 | DIAG_TERM consumer-contract mismatch | resolved | Output convention swap (this doc) |
| R2 | `_STABLE` catalog size | dissolved | Bridge avoids the need; `HALTS_B_APP_DECOMP` family also probably unneeded — see Risk 5 |
| R3 | `HALTS_SK_STEP_APP_LEFT` semantic mismatch | dissolved | Lemma has no purpose under bullet; not on Option C's critical path |
| R4 | `is_normal` definition coupling | friction | Bullet pipeline uses `is_normal` only via existing `IS_NORMAL_DEF`; non-normality lemmas via direct `sk_step ≠ self`.  No conversion lemma needed. |
| R5 | Bullet-only `DIAG_TERM` blocks composite H | **dissolved (pivot)** | Adopted Option C: par-form diagonal + bridge. See [Post-spike audit](#post-spike-audit-2026-05-13-composite-h-falsifies-bullet-only-diag_term). |

**Risk concentration** (Option C): triangle (1) is ~50% of remaining
risk by volume; par DIAG_TERM (1b) is ~15%; orbit equations (2) are
~20%; (3)-(6) are bookkeeping.  Design is stable; residual risks are
all HOL-discharge unknowns.

## What this doesn't fix

- `sk_step` (single LMO contraction) survives — used as a concrete
  notion of reduction outside the halting pipeline.  Only `sk_iter`
  (the iteration) goes away.

- The par-relation `sk_par_step` survives under Option C as the
  diagonal's calculus.  Not deleted, but downgraded from "halting's
  primary relation" to "internal scaffolding for one bridge proof
  and one diagonal."

- The semantic content of "halting" changes: `halts_b` is the
  Takahashi-strategy halting notion ("the bullet trajectory reaches
  normal") rather than the deterministic-LMO notion.  Classically
  equivalent to LMO halting (by standardization), but in this
  codebase the LMO equivalence is the deleted `STANDARDIZATION_NORMAL`.
  If the LMO equivalence is later required for some other purpose,
  it returns as a fresh obligation; the migration only removes it
  from the *halting undecidability* critical path.

- The bullet/par equivalence (`HALTS_B_IFF_HALTS_PAR`) does *not*
  go away — it's the new bridge.  But it's a single, contained
  lemma rather than a pervasive structural assumption.

## Files touched

- `halting.py`: the migration site; ~2500 lines deleted, ~700 lines
  added (Option C net).
- `outside/sk_par.py`: empirical witness for Ω's bullet orbit + the
  composite-H DIAG_TERM stress test (EXP 5) + Turing's Θ spike
  (EXP 6); not consumed by the kernel.
- `outside/sk_trace.py`: unchanged.
