import Temporal.Defs

/-!
# T2 — Duality lemmas

Mathlib is classical, so these should fall to `push_neg` / `not_exists` etc.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- `¬ F φ ↔ G ¬ φ`. -/
theorem not_eventually (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (F φ)) ↔ sat σ (G φ) := by
  sorry

/-- `¬ X φ ↔ X ¬ φ`. -/
theorem not_next (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (X φ)) ↔ sat σ (X (.neg φ)) := by
  sorry

/-- `¬ G φ ↔ F ¬ φ`. -/
theorem not_globally (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (G φ)) ↔ sat σ (F (.neg φ)) := by
  sorry

end Temporal
