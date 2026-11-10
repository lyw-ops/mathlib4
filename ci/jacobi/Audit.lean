module

import all Mathlib.LinearAlgebra.Matrix.AdjugateTrace
import all Mathlib.Analysis.Matrix.Determinant
import Lean

run_cmd do
  let env ← Lean.getEnv
  let modules := #["Mathlib.LinearAlgebra.Matrix.AdjugateTrace",
    "Mathlib.Analysis.Matrix.Determinant"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let localDecl := match env.getModuleIdxFor? name with
      | some i => modules.contains env.header.moduleNames[i.toNat]!.toString
      | none => false
    unless localDecl do continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    unless axioms.all (allowed.contains ·) do
      throwError "{name} has unexpected axioms: {axioms}"
    Lean.logInfo m!"AXIOM_REPORT {name}: {axioms}"
  if count == 0 then throwError "No candidate declarations audited"
  Lean.logInfo m!"AUDITED {count} candidate declarations"
