import Temporal.Defs

/-!
# T2 — Duality lemmas

Mathlib is classical, so these should fall to `push_neg` / `not_exists` etc.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- `¬ F φ ↔ G ¬ φ`.

Note: the formalized statement uses `G (.neg φ)` on the right (matching the
documented `G ¬ φ`). The original `sorry` stub wrote `G φ`, which is unprovable:
`sat σ (.neg (F φ))` is `¬ sat σ (F φ)`, whereas `sat σ (G φ)` unfolds to
`¬ sat σ (F (.neg φ))`. The fix preserves the intended meaning. -/
theorem not_eventually (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (F φ)) ↔ sat σ (G (.neg φ)) := by
  show ¬ sat σ (F φ) ↔ sat σ (G (.neg φ))
  rw [sat_eventually, sat_globally]
  push_neg
  rfl

/-- `¬ X φ ↔ X ¬ φ`. -/
theorem not_next (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (X φ)) ↔ sat σ (X (.neg φ)) := by
  -- By definition of `sat`, we can rewrite the goal using the definitions of `X` and `neg`.
  simp [sat]

/-- `¬ G φ ↔ F ¬ φ`. -/
theorem not_globally (σ : Stream' State) (φ : Formula State) :
    sat σ (.neg (G φ)) ↔ sat σ (F (.neg φ)) := by
  convert Classical.not_not

end Temporal