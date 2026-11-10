module

public import Mathlib.Analysis.Matrix.Determinant

public section

variable {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- No matrix norm scope: the pointwise property should use the new composition rule.
example {f : E → Matrix n n 𝕜} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y ↦ (f y).det) x := by
  fun_prop

-- Direct dot notation is available without a matrix norm scope as well.
example {f : E → Matrix n n 𝕜} {x : E} (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y ↦ (f y).det) x :=
  hf.matrix_det

-- This global property already worked; do not regress it or require another wrapper.
example {f : E → Matrix n n 𝕜} (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y ↦ (f y).det) := by
  fun_prop

section Frobenius

open scoped Matrix.Norms.Frobenius

-- Check both matrix source and matrix target under the alternative norm scope.
example {f : Matrix n n 𝕜 → Matrix n n 𝕜} {x : Matrix n n 𝕜}
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y ↦ (f y).det) x := by
  fun_prop

example {f : Matrix n n 𝕜 → Matrix n n 𝕜} (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y ↦ (f y).det) := by
  fun_prop

end Frobenius
