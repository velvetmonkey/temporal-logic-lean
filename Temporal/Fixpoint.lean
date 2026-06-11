import Temporal.Defs

/-!
# T3 — Fixpoint identities

These are the conceptual bridge from the semantics to the runtime monitor and
the reachable-set checker. Pulled forward (council 2fc86cd0) so they sit next
to safety, not as a side-quest.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- `G φ ↔ φ ∧ X G φ`. -/
theorem globally_unfold (σ : Stream' State) (φ : Formula State) :
    sat σ (G φ) ↔ sat σ (.conj φ (X (G φ))) := by
  sorry

/-- `F ψ ↔ ψ ∨ X F ψ`. -/
theorem eventually_unfold (σ : Stream' State) (ψ : Formula State) :
    sat σ (F ψ) ↔ sat σ (.disj ψ (X (F ψ))) := by
  sorry

/-- Until expansion: `φ U ψ ↔ ψ ∨ (φ ∧ X (φ U ψ))`. -/
theorem until_unfold (σ : Stream' State) (φ ψ : Formula State) :
    sat σ (.«until» φ ψ) ↔ sat σ (.disj ψ (.conj φ (X (.«until» φ ψ)))) := by
  sorry

end Temporal
