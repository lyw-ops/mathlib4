module

public import Mathlib.Analysis.Matrix.Determinant
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Data.ZMod.Basic

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.AdjugateTrace

public section

open scoped Matrix Matrix.Norms.Operator

section Line

variable {𝕜 n : Type*} [NontriviallyNormedField 𝕜] [Fintype n] [DecidableEq n]

private theorem det_line (A H : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ (A + t • H).det) (Matrix.trace (A.adjugate * H)) 0 := by
  have h := (Matrix.hasFDerivAt_det A).comp_hasDerivAt_of_eq (0 : 𝕜)
    (((hasDerivAt_id (0 : 𝕜)).smul_const H).const_add A) (by simp)
  rw [one_smul] at h
  exact h.congr_deriv (by rfl)

-- A matrix-field consumer of the inverse form, as used in the Tau Ceti log-det proof.
example (A B : Matrix n n 𝕜) (t : 𝕜) (h : IsUnit (A + t • (B - A)).det) :
    HasDerivAt (fun s : 𝕜 ↦ (A + s • (B - A)).det)
      ((A + t • (B - A)).det * Matrix.trace ((A + t • (B - A))⁻¹ * (B - A))) t := by
  have hd := (Matrix.hasFDerivAt_det_of_isUnit h).comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const (B - A)).const_add A)
  rw [one_smul] at hd
  exact hd.congr_deriv (by rfl)

end Line

-- The determinant has derivative 1 in the missing diagonal direction at diag(1, 0).
example : HasDerivAt
    (fun t : ℝ ↦ ( !![1, 0; 0, 0] + t • !![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det)
    1 0 := by
  simpa [Matrix.adjugate_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] using
    det_line ( !![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) !![0, 0; 0, 1]

-- A nonsymmetric singular complex matrix detects the cofactor/transpose orientation.
example : HasDerivAt
    (fun t : ℂ ↦ ( !![0, 1; 0, 0] + t • !![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det)
    (-1) 0 := by
  simpa [Matrix.adjugate_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] using
    det_line ( !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 1, 0]

-- The same singular example over the incomplete normed field of rationals.
example : HasDerivAt
    (fun t : ℚ ↦ ( !![1, 0; 0, 0] + t • !![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).det)
    1 0 := by
  simpa [Matrix.adjugate_fin_two, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] using
    det_line ( !![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) !![0, 0; 0, 1]

-- The determinant of an empty matrix is constant, so every directional derivative is zero.
example (A H : Matrix (Fin 0) (Fin 0) ℝ) : fderiv ℝ Matrix.det A H = 0 := by
  rw [Matrix.fderiv_det_apply]
  simp

-- The purely algebraic identity also works over a ring with zero divisors.
example (A B : Matrix (Fin 2) (Fin 2) (ZMod 4)) :
    (A.updateRow 0 (B 0)).det + (A.updateRow 1 (B 1)).det = (A.adjugate * B).trace := by
  simpa [Fin.sum_univ_two] using Matrix.sum_det_updateRow_eq_trace_adjugate_mul A B
