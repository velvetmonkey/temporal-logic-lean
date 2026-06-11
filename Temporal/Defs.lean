import Mathlib

/-!
# Temporal logic over infinite traces (LTL)

Design decisions locked by council 2fc86cd0:
- A trace is `Stream' State = ℕ → State`. No coinduction, no Büchi.
  `X/F/G/U` collapse to ∃/∀ over ℕ via `Stream'.drop`.
- `sat` is `Prop`-valued. Executable `Bool` monitors/checkers live in later
  files with explicit soundness bridges, kept separate from this semantics.

Atomic propositions are taken directly as state predicates `State → Prop`,
so we never need a separate atom type + valuation.
-/

namespace Temporal

universe u
variable {State : Type u}

/-- LTL formulas over a state type. Atoms are state predicates. -/
inductive Formula (State : Type u) where
  | atom : (State → Prop) → Formula State
  | tt   : Formula State
  | ff   : Formula State
  | neg  : Formula State → Formula State
  | conj : Formula State → Formula State → Formula State
  | disj : Formula State → Formula State → Formula State
  | next : Formula State → Formula State
  | «until» : Formula State → Formula State → Formula State

/-- Satisfaction of an LTL formula by an infinite trace. -/
def sat : Stream' State → Formula State → Prop
  | σ, .atom p   => p (σ.head)
  | _, .tt       => True
  | _, .ff       => False
  | σ, .neg φ    => ¬ sat σ φ
  | σ, .conj φ ψ => sat σ φ ∧ sat σ ψ
  | σ, .disj φ ψ => sat σ φ ∨ sat σ ψ
  | σ, .next φ   => sat σ.tail φ
  | σ, .«until» φ ψ => ∃ i, sat (σ.drop i) ψ ∧ ∀ j, j < i → sat (σ.drop j) φ

/-- Eventually: `F ψ := tt U ψ`. -/
def eventually (ψ : Formula State) : Formula State := .«until» .tt ψ

/-- Globally: `G φ := ¬ F ¬ φ`. -/
def globally (φ : Formula State) : Formula State := .neg (eventually (.neg φ))

@[inherit_doc] prefix:80 "X " => Formula.next
@[inherit_doc] prefix:80 "F " => eventually
@[inherit_doc] prefix:80 "G " => globally

/-
`G φ` unfolds to "φ holds at every suffix". The bridge to invariant safety.
-/
theorem sat_globally (σ : Stream' State) (φ : Formula State) :
    sat σ (G φ) ↔ ∀ n, sat (σ.drop n) φ := by
  simp +decide only [globally];
  simp +decide [ eventually, sat ]

/-
`F ψ` unfolds to "ψ holds at some suffix".
-/
theorem sat_eventually (σ : Stream' State) (ψ : Formula State) :
    sat σ (F ψ) ↔ ∃ n, sat (σ.drop n) ψ := by
  constructor;
  · exact fun h => by obtain ⟨ n, hn ⟩ := h; exact ⟨ n, hn.1 ⟩ ;
  · rintro ⟨ n, hn ⟩;
    -- By definition of `eventually`, we need to show that there exists some `i` such that `sat (σ.drop i) ψ`.
    use n;
    exact ⟨ hn, fun j hj => trivial ⟩

end Temporal