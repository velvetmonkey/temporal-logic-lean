/- SPDX-License-Identifier: MIT -/

import Temporal.Defs
import AttentionLean.ParityWindow

/-!
# Angle B — parallel bounded-observation monitor (attention-lean load-bearing)

The dual of `Temporal.BoundedMonitor` (Angle A). There the bound was on
*sequential memory* carried across steps; here there is **no** cross-step state,
but each observation is *budget-limited*: the verdict is an aggregate of `k`
sub-decisions, each a decision list reading a bounded window of at most `t`
positions (`FixableK · t` — attention-lean's `AttentionLean.ParityWindow`).

## Honest provenance

The counting engine is attention-lean's `collision_of_fixableK` (`k` t-fixable
functions cost at most `k·t` pinned coordinates, so when `k·t < n` free coordinates
remain a parity-flipping collision survives). This module is the **transport** of
that bound into the monitor-enforcement setting: the monitor model (`ObsMonitor`),
the threat-model reading (`parity_action_innocuous`), and the explicit bypass
(`obs_monitor_bypass`) are new; the inequality is attention-lean's.

## The finding (paired with Angle A)

The assembled violation here is `parityN` — the sharpest "individually-innocuous"
target: flipping **any single** action flips the verdict (`parity_action_innocuous`
= attention-lean's `parityN_update_ne`), so no bounded observer can read the attack
off any one action. This is a *different* blade from Angle A: parity is trivially
catchable by a one-bit *sequential* monitor (running XOR), so it is only a lower
bound against *bounded observation*, `k·t < n` — not against bounded memory.
Bounded guards fail two independent ways; neither is closed by "a bit more".
-/

namespace Temporal

open Finset

/-- A bounded-observation execution monitor over `n` step-markers. It reaches its
verdict through `k` sub-decisions, each a decision list reading a bounded window of
at most `t` positions (`FixableK (sub i) t`), combined by an arbitrary aggregator.
No cross-step memory — the complementary resource bound to Angle A. -/
structure ObsMonitor (n t : ℕ) where
  /-- Number of sub-decisions (observation windows). -/
  k : ℕ
  /-- Each sub-decision as a Boolean function of the full observation. -/
  sub : Fin k → (Fin n → Bool) → Bool
  /-- Each sub-decision is a decision list of budget `t` (reads ≤ `t` positions). -/
  hfix : ∀ i, FixableK (sub i) t
  /-- The aggregator combining the `k` sub-verdicts. -/
  agg : (Fin k → Bool) → Bool

/-- The monitor's decision on a full length-`n` observation. -/
def ObsMonitor.call {n t : ℕ} (M : ObsMonitor n t) (x : Fin n → Bool) : Bool :=
  M.agg (fun i => M.sub i x)

/-- **Individually innocuous = maximal sensitivity.** Every single action, flipped
in isolation, flips the assembled verdict, so no bounded observer can tell from any
one action whether the attack is being assembled. This is attention-lean's
`parityN_update_ne` restated as the threat-model property. -/
theorem parity_action_innocuous {n : ℕ} (x : Fin n → Bool) (j : Fin n) :
    parityN (Function.update x j (!x j)) ≠ parityN x :=
  parityN_update_ne x j

/-- Shared setup: the `k` sub-decisions as a `FixableK`-`t` list, and the free-
coordinate count of the empty subcube. -/
private theorem obs_collision {n t : ℕ} (M : ObsMonitor n t) (hbudget : M.k * t < n) :
    ∃ x y : Fin n → Bool, (∀ i, M.sub i x = M.sub i y) ∧ parityN x ≠ parityN y := by
  have hfs : ∀ f ∈ List.ofFn M.sub, FixableK f t := by
    intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    exact M.hfix i
  have hcardeq :
      (univ.filter fun i : Fin n => (fun _ => (none : Option Bool)) i = none).card = n := by
    rw [Finset.filter_true_of_mem (fun i _ => rfl), Finset.card_univ, Fintype.card_fin]
  obtain ⟨x, y, _, _, hpar, hagree⟩ :=
    collision_of_fixableK (List.ofFn M.sub) hfs (fun _ => none)
      (by rw [List.length_ofFn, hcardeq]; exact hbudget)
  exact ⟨x, y, fun i => hagree (M.sub i) (List.mem_ofFn.mpr ⟨i, rfl⟩), hpar⟩

/-- **Angle B headline — the quantitative observation lower bound.** A
bounded-observation monitor whose total observation budget `k · t` is below the
number of step-markers `n` cannot compute the parity-assembled violation. The
`k · t < n` collision produces two observations the monitor scores identically, one
a violation and one safe — no "a few more windows" fix short of `k · t ≥ n`. -/
theorem obs_monitor_misses_assembly {n t : ℕ} (M : ObsMonitor n t)
    (hbudget : M.k * t < n) : M.call ≠ parityN := by
  intro hcall
  obtain ⟨x, y, hsub, hpar⟩ := obs_collision M hbudget
  have hxy : M.call x = M.call y := by
    simp only [ObsMonitor.call]; congr 1; funext i; exact hsub i
  rw [hcall] at hxy
  exact hpar hxy

/-- **Kernel-checked decomposition bypass (Angle B).** The `k · t < n` collision as
an explicit pair: two observations the monitor scores identically across every one
of its `k` sub-decisions (hence the same aggregate verdict), yet of opposite safety
status. -/
theorem obs_monitor_bypass {n t : ℕ} (M : ObsMonitor n t) (hbudget : M.k * t < n) :
    ∃ x y : Fin n → Bool,
      (∀ i, M.sub i x = M.sub i y) ∧ M.call x = M.call y ∧ parityN x ≠ parityN y := by
  obtain ⟨x, y, hsub, hpar⟩ := obs_collision M hbudget
  refine ⟨x, y, hsub, ?_, hpar⟩
  simp only [ObsMonitor.call]; congr 1; funext i; exact hsub i

end Temporal
