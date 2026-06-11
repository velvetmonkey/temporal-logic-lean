import Temporal.Defs

/-!
# T4 — Safety as `G` of a state predicate

`Safety p σ` says the state predicate `p` holds at every position. This is the
shape the Safety Seal cares about, and the object the runtime monitor (T5) and
the reachable-set checker (T6) both certify.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- An invariant safety property: `p` holds at every position of the trace. -/
def Safety (p : State → Prop) (σ : Stream' State) : Prop :=
  ∀ n, p (σ n)

/-
`Safety p` is exactly `sat σ (G (atom p))`.
-/
theorem safety_iff_globally_atom (p : State → Prop) (σ : Stream' State) :
    Safety p σ ↔ sat σ (G (.atom p)) := by
  apply Iff.intro;
  · intro h;
    rw [ sat_globally ];
    exact fun n => h _;
  · intro h;
    convert sat_globally σ ( Formula.atom p ) |>.1 h using 1;
    simp +decide [ Safety, sat ];
    rfl

/-
Safety is closed under conjunction of predicates.
-/
theorem safety_and (p q : State → Prop) (σ : Stream' State) :
    Safety (fun s => p s ∧ q s) σ ↔ Safety p σ ∧ Safety q σ := by
  exact ⟨ fun h => ⟨ fun n => h n |>.1, fun n => h n |>.2 ⟩, fun h n => ⟨ h.1 n, h.2 n ⟩ ⟩

end Temporal