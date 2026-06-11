import Temporal.Defs
import Temporal.Safety

/-!
# Safety Seal property + trust boundaries

The seal's invariant is `G (executed → allowed)`, NOT `G (¬ denied)`:
a deny decision is not itself bad; *executing after a deny* is bad
(council 2fc86cd0, Codex).

Two trust boundaries are stated as explicit hypotheses. The temporal proof
sits ON TOP of them; if either fails the proof is vacuous. They are NOT
provable inside Lean — they are obligations discharged by the seal's
construction (canonical serialization) and by inline enforcement.
-/

namespace Temporal

universe u

/-- An observed tool-call event. `allowed` is the seal's decision; `executed`
is whether the upstream server actually ran the call. -/
structure Event where
  allowed  : Prop
  executed : Prop

/-- The seal safety property: never execute a call the seal did not allow. -/
def sealSafe (σ : Stream' Event) : Prop :=
  Safety (fun e => e.executed → e.allowed) σ

/-! ## Trust boundary 1 — parser-differential / canonical serialization

The abstract trace `σ : Stream' Event` is faithful to reality only if the
bytes the seal classified are the bytes the upstream server executed.
`Canonical` is that obligation, discharged by the M3 canonical-serialization
roundtrip, NOT by this library. -/
axiom Canonical : Prop

/-! ## Trust boundary 2 — enforcement

The seal must be inline (a proxy), so that a deny decision actually prevents
execution. `enforcement_sound` is read off the deployment, not proved here. -/
axiom enforcement_sound :
    ∀ (σ : Stream' Event) (n : Nat), ¬ (σ n).allowed → ¬ (σ n).executed

/-- With enforcement, the seal property holds on every trace. The honest
content of the seal: its *behavioural* guarantee reduces to `enforcement_sound`
under the `Canonical` boundary. -/
theorem sealSafe_of_enforcement (h : Canonical) (σ : Stream' Event) :
    sealSafe σ := by
  sorry

end Temporal
