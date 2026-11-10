module

public import Mathlib.Analysis.Matrix.Determinant

public section

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]

-- Exercise simp on the whole-map formula itself, without a matrix norm scope.
example (A H : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A H = (A.adjugate * H).trace := by
  simp [Matrix.fderiv_det]

-- The same simplification is independent of the ambient matrix norm scope.
open scoped Matrix.Norms.Frobenius in
example (A H : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A H = (A.adjugate * H).trace := by
  simp [Matrix.fderiv_det]

-- The inverse-matrix public map should simplify too, with no chosen matrix norm.
example {A : Matrix n n 𝕜} (hA : IsUnit A.det) (H : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A H = A.det * (A⁻¹ * H).trace := by
  simpa using DFunLike.congr_fun (Matrix.hasFDerivAt_det_of_isUnit hA).fderiv H

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Simplify the explicitly composed differential for an abstract normed source.
example {f : E → Matrix n n 𝕜} {f' : E →L[𝕜] Matrix n n 𝕜} {x : E}
    (hf : HasFDerivAt f f' x) (h : E) :
    fderiv 𝕜 (fun y ↦ (f y).det) x h = ((f x).adjugate * f' h).trace := by
  simpa using DFunLike.congr_fun hf.matrix_det.fderiv h
