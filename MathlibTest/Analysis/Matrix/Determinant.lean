module

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Determinant

/-! # Tests for the derivative and smoothness of the determinant -/

open Matrix
open scoped ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n]

section NoNorm

/-! The first-derivative statements need no norm on matrices. -/

example (A H : Matrix n n ℝ) : fderiv ℝ det A H = trace (A.adjugate * H) := by simp

example (f : ℝ → Matrix n n ℝ) (f' : Matrix n n ℝ) (x : ℝ) (hf : HasDerivAt f f' x) :
    deriv (fun t ↦ (f t).det) x = ((f x).adjugate * f').trace :=
  hf.matrix_det.deriv

example : Differentiable ℝ (fun A : Matrix n n ℝ ↦ A.det) := by fun_prop

example (f : ℝ → Matrix n n ℝ) (s : Set ℝ) (x : ℝ) (hf : DifferentiableWithinAt ℝ f s x) :
    DifferentiableWithinAt ℝ (fun t ↦ (f t).det) s x := by
  fun_prop

example (f : ℝ → Matrix n n ℝ) (s : Set ℝ) (hf : DifferentiableOn ℝ f s) :
    DifferentiableOn ℝ (fun t ↦ (f t).det) s := by
  fun_prop

end NoNorm

section Operator

open scoped Matrix.Norms.Operator

example : ContDiff ℝ ∞ (det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) := contDiff_det

example (f : ℝ → Matrix n n ℝ) (x : ℝ) (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 2 (fun t ↦ (f t).det) x := by
  fun_prop

example : Differentiable ℝ (fun A : Matrix n n ℝ ↦ (A * A).det) := by fun_prop

end Operator

section Elementwise

open scoped Matrix.Norms.Elementwise

example : ContDiff ℝ ∞ (det : Matrix n n ℝ → ℝ) := by fun_prop

example (f : ℝ → Matrix n n ℝ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (fun t ↦ (f t).det) := by
  fun_prop

end Elementwise

section Frobenius

open scoped Matrix.Norms.Frobenius

example : ContDiff ℝ ∞ (det : Matrix n n ℝ → ℝ) := by fun_prop

example (f : ℝ → Matrix n n ℝ) (s : Set ℝ) (hf : ContDiffOn ℝ 2 f s) :
    ContDiffOn ℝ 2 (fun t ↦ (f t).det) s := by
  fun_prop

/-- The first-derivative statements also apply when a norm is in scope. -/
example (B : Matrix n n ℝ) : HasDerivAt (fun t : ℝ ↦ det (1 + t • B)) B.trace 0 :=
  hasDerivAt_det_one_add_smul B

end Frobenius
