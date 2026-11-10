module

public import Mathlib.Analysis.Matrix.Determinant
public import Mathlib.Analysis.Normed.Group.Rat

import Mathlib.Analysis.Calculus.FDeriv.Add

public section

open scoped Matrix

section GeneralTrace

variable {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
  [TopologicalSpace M] [ContinuousAdd M]

-- A coefficient module with no multiplication is enough; the generated simp API works.
example (a b c d : M) : Matrix.traceCLM (Fin 2) S M !![a, b; c, d] = a + d := by
  simp [Matrix.trace, Fin.sum_univ_two]

end GeneralTrace

section NoMatrixNorm

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]

example {f : 𝕜 → Matrix n n 𝕜} {f' : Matrix n n 𝕜} {x : 𝕜}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  hf.matrix_det

-- The operator selected by the whole-map equation really evaluates to Jacobi's formula.
example (A H : Matrix n n 𝕜) :
    fderiv 𝕜 Matrix.det A H = (A.adjugate * H).trace := by
  rw [Matrix.fderiv_det]
  rfl

-- All directions in an empty matrix space have strict derivative zero.
example (A : Matrix (Fin 0) (Fin 0) 𝕜) :
    HasStrictFDerivAt Matrix.det (0 : Matrix (Fin 0) (Fin 0) 𝕜 →L[𝕜] 𝕜) A := by
  refine (Matrix.hasStrictFDerivAt_det A).congr_fderiv ?_
  ext H
  simp

-- A singular, nonsymmetric example detects an accidental transpose in the new map.
example : fderiv ℝ Matrix.det ( !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    !![0, 0; 1, 0] = -1 := by
  rw [Matrix.fderiv_det_apply]
  simp [Matrix.adjugate_fin_two, Matrix.trace, Fin.sum_univ_two]

-- Verify the advertised fun_prop integration, rather than invoking matrix_det directly.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : E → Matrix n n 𝕜} {f' : E →L[𝕜] Matrix n n 𝕜} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y ↦ (f y).det)
      (((Matrix.traceCLM n 𝕜 𝕜).comp
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))).comp f') x := by
  fun_prop

end NoMatrixNorm

section FrobeniusComposition

open scoped Matrix.Norms.Frobenius

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]

-- The source as well as the target may be the Frobenius-normed matrix space.
example (A H : Matrix n n 𝕜) :
    fderiv 𝕜 (fun B : Matrix n n 𝕜 ↦ B.det) A H = (A.adjugate * H).trace := by
  have hi : HasFDerivAt (fun B : Matrix n n 𝕜 ↦ B)
      (ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜)) A :=
    (ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜)).hasFDerivAt
  have h := DFunLike.congr_fun hi.matrix_det.fderiv H
  exact h

-- A two-parameter matrix field uses a normed product domain and Frobenius matrices.
-- The directional derivative from the new composition API is the expected H-direction.
example (A H J : Matrix n n 𝕜) :
    let L : 𝕜 × 𝕜 →L[𝕜] Matrix n n 𝕜 :=
      (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).smulRight H +
        (ContinuousLinearMap.snd 𝕜 𝕜 𝕜).smulRight J
    fderiv 𝕜 (fun p ↦ (A + L p).det) (0, 0) (1, 0) = (A.adjugate * H).trace := by
  intro L
  have hf : HasFDerivAt (fun p ↦ A + L p) L (0, 0) := L.hasFDerivAt.const_add A
  have h := DFunLike.congr_fun hf.matrix_det.fderiv (1, 0)
  simpa [L] using h

end FrobeniusComposition

section SmoothComposition

open scoped Matrix.Norms.Operator ContDiff

variable {n 𝕜 E : Type*} [Fintype n] [DecidableEq n] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

example {f : E → Matrix n n 𝕜} {m : ℕ∞ω} (hf : ContDiff 𝕜 m f) :
    ContDiff 𝕜 m (fun x ↦ (f x).det) := by
  fun_prop

end SmoothComposition

open scoped Matrix.Norms.Operator ContDiff in
-- No completeness is required even for analytic smoothness over Q and empty matrices.
example : ContDiff ℚ ω (Matrix.det : Matrix (Fin 0) (Fin 0) ℚ → ℚ) :=
  Matrix.contDiff_det
