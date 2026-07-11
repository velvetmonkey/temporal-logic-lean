import Temporal

/-!
# Axiom-footprint gate for temporal-logic-lean

Every public LTL / safety / monitor soundness result must sit on the standard
axiom set only — some combination of `{propext, Classical.choice, Quot.sound}`,
several of them axiom-free — with no `sorryAx` and no `Lean.ofReduceBool`. Each
expected footprint is pinned with `#guard_msgs`, so any axiom drift (a stray
`sorry`, a `native_decide`, a newly-classical proof) fails the build itself, at
compile time.

Footprints observed via `#print axioms` on 2026-07-04.
-/

-- LTL semantics (Temporal/Defs.lean): G/F suffix unfoldings.

/--
info: 'Temporal.sat_globally' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.sat_globally

/-- info: 'Temporal.sat_eventually' does not depend on any axioms -/
#guard_msgs in #print axioms Temporal.sat_eventually

-- Duality lemmas (Temporal/Duality.lean).

/--
info: 'Temporal.not_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.not_eventually

/-- info: 'Temporal.not_next' depends on axioms: [propext] -/
#guard_msgs in #print axioms Temporal.not_next

/--
info: 'Temporal.not_globally' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.not_globally

-- Fixpoint identities (Temporal/Fixpoint.lean).

/--
info: 'Temporal.globally_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.globally_unfold

/-- info: 'Temporal.eventually_unfold' depends on axioms: [propext] -/
#guard_msgs in #print axioms Temporal.eventually_unfold

/--
info: 'Temporal.until_unfold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.until_unfold

-- Safety as `G` of a state predicate (Temporal/Safety.lean).

/--
info: 'Temporal.safety_iff_globally_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.safety_iff_globally_atom

/-- info: 'Temporal.safety_and' does not depend on any axioms -/
#guard_msgs in #print axioms Temporal.safety_and

-- Finite prefixes + Alpern–Schneider (Temporal/Prefix.lean).

/-- info: 'Temporal.length_take' depends on axioms: [propext] -/
#guard_msgs in #print axioms Temporal.length_take

/-- info: 'Temporal.badPrefix_violates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Temporal.badPrefix_violates

/--
info: 'Temporal.violation_has_badPrefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.violation_has_badPrefix

/--
info: 'Temporal.alpern_schneider' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.alpern_schneider

-- Safety Seal property (Temporal/Seal.lean): enforcement discharges seal safety.

/--
info: 'Temporal.sealSafe_of_enforced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.sealSafe_of_enforced

-- Executable monitor + enforcement discharge (Temporal/Monitor.lean).

/-- info: 'Temporal.monitor_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Temporal.monitor_sound

/--
info: 'Temporal.monitor_rejects_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.monitor_rejects_iff

/-- info: 'Temporal.gateTrace_enforced' depends on axioms: [propext] -/
#guard_msgs in #print axioms Temporal.gateTrace_enforced

/--
info: 'Temporal.gateTrace_sealSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.gateTrace_sealSafe

-- Bounded-monitor impossibility, Angle A: sequential memory lower bound
-- (Temporal/BoundedMonitor.lean).

/--
info: 'Temporal.bounded_monitor_memory_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.bounded_monitor_memory_lower_bound

/--
info: 'Temporal.enforces_no_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.enforces_no_collision

/--
info: 'Temporal.seenZeroGuard_not_enforces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.seenZeroGuard_not_enforces

/--
info: 'Temporal.seenZeroGuard_bypass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.seenZeroGuard_bypass

-- Bounded-monitor impossibility, Angle B: parallel observation lower bound,
-- attention-lean parity/decision-list engine (Temporal/BoundedObs.lean).

/--
info: 'Temporal.obs_monitor_misses_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.obs_monitor_misses_assembly

/--
info: 'Temporal.obs_monitor_bypass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.obs_monitor_bypass

/--
info: 'Temporal.parity_action_innocuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Temporal.parity_action_innocuous

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
