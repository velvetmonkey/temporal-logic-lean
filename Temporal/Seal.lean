import Temporal.Defs
import Temporal.Safety

/-!
# Safety Seal property + trust boundaries

The seal's invariant is `G (executed → allowed)`, NOT `G (¬ denied)`:
a deny decision is not itself bad; *executing after a deny* is bad
(council 2fc86cd0, Codex).

## M2 change — enforcement localised (council 798c9d99)

M1 stated enforcement as a GLOBAL axiom `∀ σ n, ¬allowed → ¬executed`.
Because `Event` admits `{allowed := False, executed := True}`, a constant
such stream made that axiom globally inconsistent (Lean could derive `False`).
M2 replaces it with a per-trace predicate `Enforced σ` and PROVES
`Enforced σ → sealSafe σ`.

The old `Canonical` axiom (parser-differential / canonical-serialization
trust boundary) is retired from the Lean source: it was inert (used only as a
vacuous hypothesis) and a naked `axiom` is optically weak under
`lake exe min_print_axioms`. It remains a documented deployment obligation,
discharged by the M3 canonical-serialization roundtrip, not by this library.
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

/-- Enforcement as a per-trace predicate (M2: localised from the old global
axiom). On this trace, no denied call ever executes. -/
def Enforced (σ : Stream' Event) : Prop :=
  ∀ n, ¬ (σ n).allowed → ¬ (σ n).executed

/-
With enforcement on a trace, the seal property holds on that trace. The
honest content of the seal: its behavioural guarantee reduces to `Enforced`,
now a hypothesis we discharge for gate-generated traces (see `Monitor`),
rather than a global axiom.
-/
theorem sealSafe_of_enforced (σ : Stream' Event) (h : Enforced σ) :
    sealSafe σ := by
  exact fun n => by contrapose! h; tauto;

end Temporal