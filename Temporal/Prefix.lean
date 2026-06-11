import Temporal.Defs
import Temporal.Safety

/-!
# M2 — Finite prefixes + Alpern–Schneider safety

Finite prefixes are modelled as `List State`, the runtime monitor's input
shape (council 798c9d99: `List State`, not `Fin n → State`). We avoid relying
on the exact argument order of `Stream'.take` by defining the length-`n`
prefix directly as `(List.range n).map σ`.

The Alpern–Schneider characterisation states the safety/liveness boundary:
a trace violates an invariant iff it has a finite *bad* prefix that no
infinite extension can repair. This is the highest-risk proof in M2
(quantifier alternation across the `List`/`Stream'` boundary).

Scope discipline (council 2fc86cd0): everything here is about the SAFETY
fragment `Safety p ≡ G (atom p)`. No `X`/`F`/`U` bad-prefix machinery, which
would reintroduce the rejected Büchi/automata path.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- The length-`n` finite prefix of a trace, as a `List State`. -/
def take (σ : Stream' State) (n : Nat) : List State :=
  (List.range n).map σ

/-
The length of a length-`n` prefix is `n`.
-/
theorem length_take (σ : Stream' State) (n : Nat) :
    (take σ n).length = n := by
  simp [take, List.length_map, List.length_range]

/-- A finite prefix is *bad* for `p` if some observed state violates `p`. -/
def badPrefix (p : State → Prop) (pre : List State) : Prop :=
  ∃ s ∈ pre, ¬ p s

/-- `τ` extends the finite prefix `pre` if `pre` is `τ`'s first `pre.length`
states. -/
def Extends (pre : List State) (τ : Stream' State) : Prop :=
  take τ pre.length = pre

/-
A bad finite prefix witnesses a safety violation.
-/
theorem badPrefix_violates (p : State → Prop) (σ : Stream' State) (n : Nat)
    (h : badPrefix p (take σ n)) : ¬ Safety p σ := by
  -- By definition of badPrefix, there exists some state s in take σ n such that ¬ p s.
  obtain ⟨s, hs⟩ : ∃ s ∈ take σ n, ¬ p s := h;
  obtain ⟨ k, hk ⟩ := List.mem_map.mp hs.1;
  exact fun h => hs.2 ( hk.2 ▸ h k )

/-
Every safety violation is witnessed by a bad finite prefix.
-/
theorem violation_has_badPrefix (p : State → Prop) (σ : Stream' State)
    (h : ¬ Safety p σ) : ∃ n, badPrefix p (take σ n) := by
  obtain ⟨ k, hk ⟩ := not_forall.mp h;
  exact ⟨ k + 1, σ k, by simp +decide [ take, List.range_succ ], hk ⟩

/-
**Alpern–Schneider (safety fragment).** A trace violates the invariant
iff it has a finite prefix that no infinite extension can satisfy.
This is the irrefutability of safety: violations are detectable in finite
time and cannot be undone by the future.
-/
theorem alpern_schneider (p : State → Prop) (σ : Stream' State) :
    ¬ Safety p σ ↔
      ∃ n, ∀ τ : Stream' State, Extends (take σ n) τ → ¬ Safety p τ := by
  refine' ⟨ fun h => _, _ ⟩;
  · obtain ⟨ k, hk ⟩ := not_forall.mp h;
    refine' ⟨ k + 1, fun τ hτ => _ ⟩;
    unfold Extends at hτ; simp_all +decide [ take ] ;
    exact fun h => hk <| hτ k le_rfl ▸ h k;
  · rintro ⟨ n, hn ⟩ h;
    exact hn σ ( by unfold Extends take; aesop ) h

end Temporal