module

public import Mathlib.Analysis.Matrix.Determinant

import Mathlib.Analysis.Calculus.Deriv.Mul

public section

section Trace

variable {n S M : Type*} [Fintype n] [Semiring S] [AddCommMonoid M]
  [Module S M] [TopologicalSpace M] [ContinuousAdd M]

-- The coefficient module does not need multiplication, a norm, or decidable equality on n.
example (A : Matrix n n M) : Matrix.traceCLM n S M A = A.trace := rfl

example (A : Matrix (Fin 0) (Fin 0) M) : Matrix.traceCLM (Fin 0) S M A = 0 := by
  simp [Matrix.trace]

end Trace

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]

-- None of the following first-derivative clients opens a matrix norm scope.
example (A : Matrix n n 𝕜) :
    HasStrictFDerivAt Matrix.det ((Matrix.traceCLM n 𝕜 𝕜).comp
      (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A :=
  Matrix.hasStrictFDerivAt_det A

example (A : Matrix n n 𝕜) :
    HasFDerivAt Matrix.det ((Matrix.traceCLM n 𝕜 𝕜).comp
      (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A :=
  Matrix.hasFDerivAt_det A

example (A : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A = (Matrix.traceCLM n 𝕜 𝕜).comp
      (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜)) := by
  rw [Matrix.fderiv_det]

example : HasFDerivAt (Matrix.det : Matrix n n 𝕜 → 𝕜) (Matrix.traceCLM n 𝕜 𝕜) 1 :=
  Matrix.hasFDerivAt_det_one

example {f : 𝕜 → Matrix n n 𝕜} {f' : Matrix n n 𝕜} {x : 𝕜}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  hf.matrix_det

example {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → Matrix n n 𝕜} {f' : E →L[𝕜] Matrix n n 𝕜} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y ↦ (f y).det)
      (((Matrix.traceCLM n 𝕜 𝕜).comp
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))).comp f') x :=
  hf.matrix_det

section Frobenius

open scoped Matrix.Norms.Frobenius

example (A H : Matrix n n 𝕜) : fderiv 𝕜 Matrix.det A H = (A.adjugate * H).trace := by
  rw [Matrix.fderiv_det_apply]

example {f : 𝕜 → Matrix n n 𝕜} {f' : Matrix n n 𝕜} {x : 𝕜}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  hf.matrix_det

example (A : Matrix n n 𝕜) : DifferentiableAt 𝕜 Matrix.det A := by
  fun_prop

end Frobenius

section Smooth

open scoped Matrix.Norms.Operator ContDiff

example {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {r : ℕ∞ω} {f : E → Matrix n n 𝕜} (hf : ContDiff 𝕜 r f) :
    ContDiff 𝕜 r (fun x ↦ (f x).det) :=
  hf.matrix_det

example (A H : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ (A + (t * t) • H).det)
      ((A + H).adjugate * ((2 : 𝕜) • H)).trace 1 := by
  have ht : HasDerivAt (fun t : 𝕜 ↦ t * t) (2 : 𝕜) 1 := by
    simpa only [id_eq, mul_one, one_mul, one_add_one_eq_two] using
      (hasDerivAt_id (1 : 𝕜)).fun_mul (hasDerivAt_id (1 : 𝕜))
  have hm : HasDerivAt (fun t : 𝕜 ↦ A + (t * t) • H) ((2 : 𝕜) • H) 1 :=
    (ht.smul_const H).const_add A
  simpa using hm.matrix_det

end Smooth
