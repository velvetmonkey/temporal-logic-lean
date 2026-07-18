# temporal-logic-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![CI](https://github.com/velvetmonkey/temporal-logic-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/velvetmonkey/temporal-logic-lean/actions/workflows/ci.yml)

A small, `sorry`-free [Lean 4](https://lean-lang.org) formalization of **linear temporal logic (LTL) over infinite traces**, ending in an **executable safety monitor** whose soundness turns the Safety Seal's enforcement guarantee from an *axiom* into a *theorem*.

Every public result is pinned to the standard axiom set at compile time. No `sorry`, no `native_decide`, no `Lean.ofReduceBool`.

Two further modules prove the **converse**, and it is the sharper claim for security: a monitor with too little memory, or too small an observation budget, provably **cannot** enforce an assembled-violation property, with a kernel-checked bypass exhibited. Finite heuristic guards are defeatable by construction; exact-match mediation is the boundary that holds. See [the impossibility half](#the-impossibility-half-bounded-monitors-provably-fail).

## What this is, and why it matters

The headline theorem is `gateTrace_sealSafe` in `Temporal/Monitor.lean`. It proves that every trace constructed from the model's input streams satisfies its LTL safety specification.

The trace constructor establishes the per-trace `Enforced` predicate by construction, and `sealSafe_of_enforced` converts that predicate into the temporal trace-safety property. Supporting modules give `Prop`-valued LTL semantics, finite bad prefixes, and an executable `List.all` safety monitor with a soundness theorem.

The conclusion is limited to traces produced by `gateTrace`; it says nothing about arbitrary event streams or implementations that do not follow that constructor. Connecting concrete observations to the model remains a deployment obligation. The separate bounded-monitor results are model-specific impossibility theorems and are not part of the headline statement.

## The story

The Safety Seal makes one behavioural promise: **a tool call is never executed unless the gate allowed it.** The question this repo answers is: what does that promise actually *reduce to*, once you stop hand-waving?

The chain is short and fully checked:

1. Define LTL over infinite traces (`Stream' State = ℕ → State`) with a `Prop`-valued satisfaction relation. Deliberately no coinduction, no Büchi automata (design locked by council `2fc86cd0`): `X`, `F`, `G`, `U` all collapse to `∃`/`∀` over `ℕ` via suffixes.
2. Pin down **safety** as `G (atom p)` and prove the **Alpern–Schneider** boundary: a trace violates an invariant iff it has a finite *bad prefix* that no infinite extension can repair. That is the theorem that says safety is a prefix-checkable property.
3. Build the **executable monitor** for the safety fragment (`List.all` of a decidable predicate) and prove it accepts a prefix iff the invariant held at every observed step.
4. Show the seal's guarantee `G (executed → allowed)` follows, **with no enforcement axiom in the trust base**, for every trace the verified gate can generate.

The headline is step 4: `gateTrace_sealSafe`.

## What is proven

All statements below are machine-checked and axiom-gated (see [Axiom discipline](#axiom-discipline)).

**LTL semantics** — `Temporal/Defs.lean`
- `sat_globally` — `G φ` holds iff `φ` holds on every suffix.
- `sat_eventually` — `F ψ` holds iff `ψ` holds on some suffix. *(axiom-free)*

**Duality** — `Temporal/Duality.lean`
- `not_eventually` (`¬ F φ ↔ G ¬ φ`), `not_next`, `not_globally`.

**Fixpoint identities** — `Temporal/Fixpoint.lean`
- `globally_unfold` (`G φ ↔ φ ∧ X G φ`), `eventually_unfold`, `until_unfold`.

**Safety** — `Temporal/Safety.lean`
- `safety_iff_globally_atom` — `Safety p ≡ sat σ (G (atom p))`.
- `safety_and` — safety is closed under conjunction of predicates. *(axiom-free)*

**Finite prefixes + Alpern–Schneider** — `Temporal/Prefix.lean`
- `length_take`, `badPrefix_violates`, `violation_has_badPrefix`.
- `alpern_schneider` — `¬ Safety p σ ↔ ∃ n, every extension of the length-n prefix still violates`. The safety/liveness boundary, and the highest-risk proof here (quantifier alternation across the `List`/`Stream'` seam).

**Safety Seal** — `Temporal/Seal.lean`
- The invariant is `G (executed → allowed)`, **not** `G (¬ denied)`: a deny is not itself bad; *executing after a deny* is bad.
- `sealSafe_of_enforced` — enforcement on a trace discharges seal safety on that trace.

**Executable monitor + enforcement discharge** — `Temporal/Monitor.lean`
- `monitor_sound` — the monitor accepts the length-n prefix iff the predicate held at every position below n.
- `monitor_rejects_iff` — it rejects exactly when a bad prefix exists.
- `gateTrace_enforced` — every trace the gate generates satisfies `Enforced` by construction, no axiom.
- **`gateTrace_sealSafe`** — every gate-generated trace is seal-safe, with no enforcement axiom in the trust base.

## The impossibility half: bounded monitors provably fail

Monitor *soundness* (above) proves a correct monitor enforces. The dual question is the one that matters for security: can a monitor that is **too small** enforce at all? Two machine-checked lower bounds answer no, and hand you the bypass. This is the formal reason exact-match mediation beats heuristic monitoring, from two independent angles.

**Bounded memory** — `Temporal/BoundedMonitor.lean`
- **`bounded_monitor_memory_lower_bound`** — a finite-state monitor with fewer than `2^N` memory states provably cannot enforce the `N`-piece assembled-violation property: two distinct subset-histories must collide, so its verdict cannot separate a completed violation from an innocent prefix.
- `enforces_no_collision` — the collision lemma the bound rests on.
- `seenZeroGuard_not_enforces` / `seenZeroGuard_bypass` — a concrete one-bit guard, kernel-checked, that fails to enforce the two-piece assembly (which needs 4 states). The bypass is a theorem, not a demo.

**Bounded observation** — `Temporal/BoundedObs.lean` (reuses [attention-lean](https://github.com/velvetmonkey/attention-lean)'s `Fixable` decision-list bound)
- **`obs_monitor_misses_assembly`** — a monitor that makes `k` sub-decisions, each over a `t`-bounded observation window, provably cannot decide an `n`-marker parity assembly once its budget `k · t < n`.
- `parity_action_innocuous` — every single action is individually innocuous: flipping any one marker flips the verdict, so there is no local tell for a per-action guard to catch. Maximal sensitivity, zero locality.
- `obs_monitor_bypass` — the `k · t < n` collision made concrete.

Both angles are pinned to `{propext, Classical.choice, Quot.sound}` in `Test/Axioms.lean`; the attention-lean dependency is pinned to a public commit in `lakefile.toml`.

## Honest boundaries — what this does NOT claim

- **Gate-generated traces, not arbitrary streams.** `gateTrace_sealSafe` covers traces the verified gate produces (`executed := requested ∧ allowed`). It does not claim safety for an arbitrary observed event stream, which no library can promise. This is the honest form of the enforcement claim.
- **The M1 global enforcement axiom was retired, not hidden.** An earlier version stated enforcement as a global axiom `∀ σ n, ¬allowed → ¬executed`. Because `Event` admits `{allowed := False, executed := True}`, a constant such stream made that axiom globally inconsistent. It is replaced by a per-trace `Enforced` predicate that is *proved* for gate traces.
- **The `Canonical` (parser-differential / canonical-serialization) trust boundary is a deployment obligation, not a theorem here.** It was inert in the Lean source (a vacuous hypothesis) and a naked `axiom` reads weak, so it is removed from the source and documented instead. It is discharged by the canonical-serialization roundtrip at the deployment layer, not by this library.
- **`Prop`-valued semantics.** The general LTL semantics is `Prop`-valued. The *executable* `Bool` monitor is provided for the safety fragment only, by design (council `798c9d99`): a parallel general-LTL `Bool` AST would smuggle back the automata machinery this formalization deliberately avoids.
- **Depends on Mathlib** (classical logic). Footprints are reported honestly below rather than claimed to be constructive.
- **The bounded-monitor lower bounds are model-level.** They prove that a monitor below the memory or observation threshold cannot enforce a specific abstract assembled-violation property; they are a lower bound on that model, not a claim that every real-world monitor is broken. The value is the *direction*: it shows a finite guard has a provable blind spot, which is exactly what exact-match mediation removes.

## Axiom discipline

Every public result is pinned with `#guard_msgs` in `Test/Axioms.lean`, so any axiom drift (a stray `sorry`, a `native_decide`, a proof that silently goes classical) **fails the build at compile time**. Footprints sit on a subset of `{propext, Classical.choice, Quot.sound}`; several results are axiom-free (`sat_eventually`, `safety_and`).

```bash
lake exe axiom_check   # prints: "axiom gate passed: all checks pinned by #guard_msgs at compile time"
```

## Build and check

Toolchain: `leanprover/lean4:v4.28.0` (see `lean-toolchain`), Mathlib pinned to `v4.28.0`.

```bash
lake exe cache get     # fetch prebuilt Mathlib (recommended)
lake build             # build the library + gate
lake exe axiom_check   # re-run the axiom-footprint gate
```

## Module map

| File | Contents |
| --- | --- |
| `Temporal/Defs.lean` | LTL `Formula` + `Prop`-valued `sat`; `X`/`F`/`G`/`U`; suffix unfoldings |
| `Temporal/Duality.lean` | Negation-duality lemmas |
| `Temporal/Fixpoint.lean` | `G`/`F`/`U` fixpoint unfoldings |
| `Temporal/Safety.lean` | `Safety p ≡ G (atom p)`; conjunction closure |
| `Temporal/Prefix.lean` | Finite prefixes as `List State`; Alpern–Schneider |
| `Temporal/Seal.lean` | `Event`, `sealSafe`, `Enforced`, enforcement discharge |
| `Temporal/Monitor.lean` | Executable monitor + `gateTrace_sealSafe` capstone |
| `Temporal/BoundedMonitor.lean` | Bounded-memory impossibility: `bounded_monitor_memory_lower_bound`, concrete one-bit bypass |
| `Temporal/BoundedObs.lean` | Bounded-observation impossibility via attention-lean `Fixable`: `obs_monitor_misses_assembly` |
| `Test/Axioms.lean` | `#guard_msgs` axiom-footprint gate (`lake exe axiom_check`) |

## License

MIT © 2026 Ben Cassie.

---

Part of the [velvetmonkey Lean 4 proof corpus](https://velvetmonkey.github.io/lean/).
