import ActualityGround
import Lean.Util.CollectAxioms

/-!
This command inspects the kernel environment of the built module, traverses
every theorem's transitive dependencies, and fails on any nonstandard axiom.
It also rejects any axiom declaration in our namespace, used or unused.
The command does not construct proofs or assert new propositions.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`ActualityGround).isPrefixOf name then
      match info with
      | .axiomInfo _ =>
        throwError "Unexpected axiom declaration: {name}"
      | .thmInfo _ =>
        count := count + 1
        let dependencies ← Lean.collectAxioms name
        for dependency in dependencies do
          unless allowed.contains dependency do
            throwError "Forbidden axiom {dependency} in theorem {name}"
      | _ => pure ()
  if count < 40 then
    throwError "Expected at least 40 audited theorems, found {count}"
  logInfo m!"PASS: audited all {count} theorems in ActualityGround; no project axioms or admitted-proof dependencies. Allowed foundations: propext, Classical.choice, Quot.sound."
