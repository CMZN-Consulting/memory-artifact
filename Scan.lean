import Lean
import MemoryArtifact
open Lean Elab Command

def std : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  let mut total := 0
  let mut bad : Array (Name × List Name) := #[]
  let mut thms := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mod := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[mod.toNat]!
    unless mn.getRoot == `MemoryArtifact do continue
    match ci with
    | .thmInfo _ | .defnInfo _ | .axiomInfo _ | .opaqueInfo _ => pure ()
    | _ => continue
    total := total + 1
    if ci matches .thmInfo _ then thms := thms + 1
    let ax := (← collectAxioms n).toList
    if ax.any (fun a => !std.contains a) then bad := bad.push (n, ax.filter (fun a => !std.contains a))
  logInfo m!"constants scanned: {total}, theorems: {thms}, with nonstandard axioms: {bad.size}"
  for (n, a) in bad.toList.take 40 do logInfo m!"{n}: {a}"
  -- fail, so that a run in CI stops on the first constant that leans on `sorryAx` or on any axiom beyond Lean's three
  unless bad.isEmpty do throwError "{bad.size} constants depend on a nonstandard axiom"
