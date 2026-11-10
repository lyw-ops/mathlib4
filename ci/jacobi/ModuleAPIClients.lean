module

public import Mathlib.Analysis.Matrix.Determinant

import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

-- The example is copied verbatim from the new module documentation.
open scoped Matrix.Norms.Operator ContDiff in
example : ContDiff ℝ ∞ (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :=
  Matrix.contDiff_det

open scoped Matrix.Norms.Operator ContDiff

example {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]
    (A H : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A H = ∑ i, (A.updateRow i (H i)).det := by
  rw [Matrix.fderiv_det_apply_eq_sum_updateRow]

example {n : Type*} [Fintype n] [DecidableEq n] (A H : Matrix n n ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ Matrix.det (A + t • H)) := by
  fun_prop

-- A direct consumer of the refactored one-dimensional chain rule.
example {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]
    (H : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ Matrix.det (1 + t • H)) (Matrix.trace H) 0 :=
  Matrix.hasDerivAt_det_one_add_smul H
