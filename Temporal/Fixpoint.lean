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
  convert ( Temporal.sat_globally σ φ ) using 1;
  -- Apply the definition of `sat` to the conjunction.
  simp [sat];
  constructor <;> intro h;
  · intro n; induction' n with n ih <;> simp_all +decide [ Temporal.sat_globally ] ;
  · exact ⟨ h 0, by rw [ Temporal.sat_globally ] ; exact fun n => h ( n + 1 ) ⟩

/-- `F ψ ↔ ψ ∨ X F ψ`. -/
theorem eventually_unfold (σ : Stream' State) (ψ : Formula State) :
    sat σ (F ψ) ↔ sat σ (.disj ψ (X (F ψ))) := by
  convert Temporal.sat_eventually σ ψ using 1;
  constructor <;> intro H;
  · cases H;
    · exact ⟨ 0, by simpa using ‹sat σ ψ› ⟩;
    · obtain ⟨ n, hn ⟩ := Temporal.sat_eventually ( Stream'.tail σ ) ψ |>.1 ‹_›; use n + 1; aesop;
  · obtain ⟨ n, hn ⟩ := H;
    induction' n with n ih;
    · exact Or.inl hn;
    · -- By definition of `sat`, we know that `sat (Stream'.drop (n + 1) σ) ψ` implies `sat (Stream'.drop n (Stream'.tail σ)) ψ`.
      have h_drop : sat (Stream'.drop n (Stream'.tail σ)) ψ := by
        convert hn using 1;
      exact Or.inr ( by exact Temporal.sat_eventually _ _ |>.2 ⟨ n, h_drop ⟩ )

/-- Until expansion: `φ U ψ ↔ ψ ∨ (φ ∧ X (φ U ψ))`. -/
theorem until_unfold (σ : Stream' State) (φ ψ : Formula State) :
    sat σ (.«until» φ ψ) ↔ sat σ (.disj ψ (.conj φ (X (.«until» φ ψ)))) := by
  constructor <;> intro h;
  · cases' h with i hi;
    rcases i with ( _ | i ) <;> simp_all +decide [ Temporal.sat ];
    exact Or.inr ⟨ hi.2 0 bot_le, i, hi.1, fun j hj => hi.2 _ ( Nat.succ_le_of_lt hj ) ⟩;
  · cases h;
    · exact ⟨ 0, by assumption, by simp +decide ⟩;
    · rename_i h;
      obtain ⟨hφ, hψ⟩ := h;
      obtain ⟨ i, hi ⟩ := hψ;
      refine' ⟨ i + 1, _, _ ⟩ <;> simp_all +decide;
      intro j hj; induction' j with j ih <;> simp_all +decide;

end Temporal