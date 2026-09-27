import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Walks every constant in the environment whose name begins with `L2.`, `Langford.`, `_private.L2.`
or `_private.Solution.` (every declaration of this development and the private auxiliaries Lean
generates for them; `Challenge.lean` is not imported), and collects the axioms each depends on.
Anything outside `propext`, `Classical.choice`, `Quot.sound` is reported with `logError`, which
fails `lake build`. The audit also fails if it matched fewer constants than the floor below (so a
renamed namespace cannot make it pass vacuously) or if any of the six compared theorems is missing
from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "L2." || label.startsWith "Langford." ||
        label.startsWith "_private.L2." || label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 600 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 600"
  for n in [`Langford.twoFold_exists_iff, `Langford.necessary, `Langford.tight_exists,
      `Langford.order_one_iff, `Langford.not_threeFold_six_three, `Langford.not_sufficient] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
