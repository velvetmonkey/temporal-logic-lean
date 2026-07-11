/- SPDX-License-Identifier: MIT -/

import Temporal.Prefix

/-!
# Bounded-monitor impossibility — the quantitative memory / observation lower bounds

A finite-memory execution monitor over an agent's action trace **cannot** enforce
a safety property whose violation is *assembled* across steps — a destructive
effect composed from N individually-innocuous actions. This module makes that
quantitative, in two independent ways, and exhibits kernel-checked
decomposition-bypass counterexamples.

## Honest provenance (do NOT round up)

This is a **machine-checked transport of a known bound** into the execution-monitor
enforcement setting, plus a checked bypass witness — NOT a newly discovered
impossibility. The two methods are classic:

* **Angle A** is the Myhill–Nerode / automaton-state pigeonhole (recognising
  "every symbol appears" needs `2^N` states). New here: the *execution-monitor
  enforcement* framing (`enforces` = sound **and** complete verdict) and the
  explicit confused-trace pair.
* **Angle B** transports attention-lean's parity / decision-list counting bound
  (`AttentionLean.ParityWindow`) — see `BoundedObs.lean`.

## The finding these two angles together record

The naive brief conflates two *different* lower bounds. The sharpest
"individually-innocuous" target — parity, where flipping any single action flips
the verdict — is **sequentially trivial**: a one-bit running-XOR monitor computes
it. So "bounded memory" and "bounded per-step observation window" are **separate
blades**, and neither is closed by "a bit more state":

* bounded **sequential memory** is defeated by an *all-N-pieces* assembly
  (needs `2^N` memory) — Angle A, here;
* bounded **parallel observation** is defeated by a *parity* assembly
  (blind when `k·t < n`) — Angle B, `BoundedObs.lean`.

## Angle A — sequential bounded-memory monitor

A monitor is a finite-state machine `(Mem, init, step, verdict)` folded over the
observed prefix (`List State`, the runtime shape from `Prefix.lean`). The
assembled violation is: **all `N` distinct pieces have been delivered**
(`assembled`). Its Myhill–Nerode class is the *subset of pieces seen so far*, so a
monitor whose state space is smaller than `2^N` must confuse two distinct subsets;
a suffix that completes one but not the other then forces an identical verdict on a
violating and a safe trace — the monitor is neither sound nor complete.

Not claimed: unbounded monitors CAN enforce this (it is a safety property with a
finite bad prefix — Schneider 2000 / `alpern_schneider`). The result is orthogonal
to that qualitative dichotomy: it bounds the *memory*, about which Schneider is
silent.
-/

namespace Temporal

universe u

/-- A finite-state execution monitor: it folds a bounded memory over the observed
prefix and emits a Boolean verdict. `memFin` witnesses that the memory — the total
state the monitor can carry across steps — is finite; its cardinality is the
quantity the lower bound constrains. -/
structure BoundedMonitor (State : Type u) where
  /-- The monitor's memory type (its entire cross-step state). -/
  Mem : Type
  /-- The memory is finite — this is the resource the bound limits. -/
  memFin : Fintype Mem
  /-- Initial memory. -/
  init : Mem
  /-- One observed action updates the memory. -/
  step : Mem → State → Mem
  /-- The current accept (`true`) / block (`false`) decision. -/
  verdict : Mem → Bool

namespace BoundedMonitor

variable {State : Type u}

/-- Fold the monitor over an observed prefix. -/
def run (M : BoundedMonitor State) (pre : List State) : M.Mem :=
  pre.foldl M.step M.init

/-- The monitor's verdict on an observed prefix. -/
def accepts (M : BoundedMonitor State) (pre : List State) : Bool :=
  M.verdict (M.run pre)

@[simp] theorem run_append (M : BoundedMonitor State) (a b : List State) :
    M.run (a ++ b) = b.foldl M.step (M.run a) := by
  simp [run, List.foldl_append]

end BoundedMonitor

/-- The assembled violation over `N` distinct action pieces: **every** piece has
been delivered. Each individual piece is innocuous; only the complete set is the
destructive effect. -/
def assembled {N : ℕ} (pre : List (Fin N)) : Prop :=
  ∀ j : Fin N, j ∈ pre

instance {N : ℕ} (pre : List (Fin N)) : Decidable (assembled pre) :=
  inferInstanceAs (Decidable (∀ j : Fin N, j ∈ pre))

/-- A monitor **enforces** the assembly property iff its verdict is both sound and
complete: it accepts exactly the prefixes that are not yet a completed assembly. -/
def BoundedMonitor.enforces {N : ℕ} (M : BoundedMonitor (Fin N)) : Prop :=
  ∀ pre : List (Fin N), M.accepts pre = true ↔ ¬ assembled pre

/-- **The collision lemma.** If a monitor collapses two subset-prefixes `S`, `T`
to the same memory and `S ⊄ T`, it cannot be enforcing: appending the pieces
missing from `S` completes `S`'s assembly (a violation) while leaving `T` short of
the witness `j ∈ S \ T` (safe), yet the shared memory forces one verdict on both. -/
theorem enforces_no_collision {N : ℕ} (M : BoundedMonitor (Fin N))
    (henf : M.enforces) {S T : Finset (Fin N)}
    (hcol : M.run S.toList = M.run T.toList) (hnsub : ¬ S ⊆ T) : False := by
  -- suffix supplying exactly the pieces missing from S
  set w := (Sᶜ).toList with hw
  -- collision survives any common suffix
  have hcol' : M.run (S.toList ++ w) = M.run (T.toList ++ w) := by
    simp only [BoundedMonitor.run_append, hcol]
  have hacc : M.accepts (S.toList ++ w) = M.accepts (T.toList ++ w) := by
    simp only [BoundedMonitor.accepts, hcol']
  -- S's trace is a completed assembly
  have hS : assembled (S.toList ++ w) := by
    intro j
    simp only [hw, List.mem_append, Finset.mem_toList, Finset.mem_compl]
    exact em (j ∈ S)
  -- T's trace still misses the witness j ∈ S \ T
  have hT : ¬ assembled (T.toList ++ w) := by
    obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.mp hnsub
    intro hcontra
    have hmem := hcontra j
    simp only [hw, List.mem_append, Finset.mem_toList, Finset.mem_compl] at hmem
    exact hmem.elim hjT (fun h => h hjS)
  -- enforcement forces opposite verdicts, contradicting the shared memory
  have hnotS : M.accepts (S.toList ++ w) ≠ true := fun h => (henf _).mp h hS
  have hyesT : M.accepts (T.toList ++ w) = true := (henf _).mpr hT
  exact hnotS (hacc.trans hyesT)

/-- **Angle A headline — the quantitative memory lower bound.** A bounded-memory
monitor with fewer than `2^N` memory states cannot enforce the `N`-piece assembly
property: some two of the `2^N` subset-prefixes collide, and the collision is a
decomposition bypass. Contrapositive: enforcing this assembly requires ≥ `2^N`
states — exponential in the decomposition width, so no "a bit more memory" fix. -/
theorem bounded_monitor_memory_lower_bound {N : ℕ} (M : BoundedMonitor (Fin N))
    (hcard : @Fintype.card M.Mem M.memFin < 2 ^ N) : ¬ M.enforces := by
  intro henf
  have hlt : @Fintype.card M.Mem M.memFin < Fintype.card (Finset (Fin N)) := by
    rw [Fintype.card_finset, Fintype.card_fin]; exact hcard
  obtain ⟨S, T, hne, hcol⟩ :=
    @Fintype.exists_ne_map_eq_of_card_lt (Finset (Fin N)) M.Mem _ M.memFin
      (fun U => M.run U.toList) hlt
  by_cases hST : S ⊆ T
  · exact enforces_no_collision M henf hcol.symm
      (fun hTS => hne (Finset.Subset.antisymm hST hTS))
  · exact enforces_no_collision M henf hcol hST

/-! ### Kernel-checked decomposition-bypass counterexample

`seenZeroGuard` is a one-bit monitor over two pieces (`Fin 2`): its whole memory is
"have I seen piece `0`". Two pieces need `2^2 = 4 > 2` memory states to track which
subset has arrived, so the general bound already gives `¬ enforces`. Concretely, the
guard is **memory-indistinguishable** on the completed attack `[0, 1]` (both pieces —
a violation) and the benign prefix `[0]` (safe): it emits the same verdict on both,
so the assembled attack slips through decomposed. -/

/-- A one-bit guard whose memory only records "seen piece `0`". -/
def seenZeroGuard : BoundedMonitor (Fin 2) where
  Mem := Bool
  memFin := inferInstance
  init := false
  step m s := m || (s == 0)
  verdict m := m

/-- The one-bit guard cannot enforce the two-piece assembly (needs `4` states). -/
theorem seenZeroGuard_not_enforces : ¬ seenZeroGuard.enforces :=
  bounded_monitor_memory_lower_bound seenZeroGuard (by decide)

/-- The bypass, kernel-checked: the guard's verdict cannot separate the completed
attack from the benign prefix. -/
theorem seenZeroGuard_bypass :
    seenZeroGuard.accepts [0, 1] = seenZeroGuard.accepts [0]
      ∧ assembled ([0, 1] : List (Fin 2)) ∧ ¬ assembled ([0] : List (Fin 2)) := by
  refine ⟨by decide, by decide, by decide⟩

end Temporal
