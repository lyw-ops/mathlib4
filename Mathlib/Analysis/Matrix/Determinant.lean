/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Module.Matrix

import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.AdjugateTrace

/-!
# Smoothness and derivatives of the determinant

Jacobi's formula gives the derivative of the determinant at any square matrix:
`H ↦ trace (adjugate A * H)`. No invertibility or completeness assumption is needed.
At an invertible matrix, the formula becomes `H ↦ det A * trace (A⁻¹ * H)`.

## Main results

* `Matrix.contDiff_det` and `ContDiff.matrix_det`: smoothness of the determinant.
* `Matrix.hasStrictFDerivAt_det` and `Matrix.hasFDerivAt_det`: Jacobi's formula.
* `Matrix.fderiv_det` and `Matrix.fderiv_det_apply`: formulas for the differential.
* `HasDerivAt.matrix_det` and `HasFDerivAt.matrix_det`: derivatives of matrix-valued functions.
* `DifferentiableAt.matrix_det`: differentiability of their determinants.
* `Matrix.hasFDerivAt_det_of_isUnit`: the inverse-matrix form of Jacobi's formula.

## Implementation details

The proof views the determinant as a continuous multilinear map of its rows.
In the differential, `B • ContinuousLinearMap.id 𝕜 _` is the map `H ↦ B * H`.
The first-derivative statements use the product topology on matrices, without choosing
a matrix norm. The smoothness statements use `Matrix.Norms.Operator`. In their proof,
`toRows` is the continuous linear identity into the sup-normed product of rows.

```lean
open scoped Matrix.Norms.Operator ContDiff in
example : ContDiff ℝ ∞ (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :=
  Matrix.contDiff_det
```

The proof is adapted from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/blob/ed6c0aa3acc0a3cb56901dc406167cdbad593f59/TauCeti/Analysis/Calculus/FDeriv/Det.lean)
and the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean).
-/

public section

open scoped ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace Matrix

private noncomputable def detMultilinear :
    ContinuousMultilinearMap 𝕜 (fun _ : n ↦ n → 𝕜) 𝕜 :=
  -- Represent the determinant on the product of its rows, with the sup norm.
  { (detRowAlternating : (n → 𝕜) [⋀^n]→ₗ[𝕜] 𝕜).toMultilinearMap with
    cont := continuous_id.matrix_det }

open scoped Matrix.Norms.Operator in
/-- The determinant is smooth for the operator norm on matrices. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) := by
  -- The identity from operator-normed matrices to the sup-normed product of rows.
  let toRows : Matrix n n 𝕜 →L[𝕜] (n → n → 𝕜) :=
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := continuous_id }
  exact (detMultilinear (n := n) (𝕜 := 𝕜)).contDiff.comp toRows.contDiff

/-- **Jacobi's formula:** the strict derivative at `A` sends `H` to
`trace (A.adjugate * H)`. -/
theorem hasStrictFDerivAt_det (A : Matrix n n 𝕜) :
    HasStrictFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ((traceCLM n 𝕜 𝕜).comp
        (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A := by
  refine (detMultilinear.hasStrictFDerivAt (fun i ↦ A i)).congr_fderiv ?_
  ext H
  -- The multilinear derivative replaces one row at a time.
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  exact sum_det_updateRow_eq_trace_adjugate_mul A H

/-- **Jacobi's formula:** the Fréchet derivative at `A` sends `H` to
`trace (A.adjugate * H)`.

For rewriting, use `Matrix.fderiv_det_apply`. -/
theorem hasFDerivAt_det (A : Matrix n n 𝕜) :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ((traceCLM n 𝕜 𝕜).comp
        (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A :=
  (hasStrictFDerivAt_det A).hasFDerivAt

/-- The determinant is differentiable. -/
@[fun_prop]
theorem differentiable_det : Differentiable 𝕜 (det : Matrix n n 𝕜 → 𝕜) :=
  fun A ↦ (hasFDerivAt_det A).differentiableAt

/-- Jacobi's formula as an equality of continuous linear maps. -/
theorem fderiv_det (A : Matrix n n 𝕜) :
    fderiv 𝕜 det A = (traceCLM n 𝕜 𝕜).comp
      (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜)) :=
  (hasFDerivAt_det A).fderiv

/-- Jacobi's formula evaluated on a matrix direction. -/
theorem fderiv_det_apply (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = trace (A.adjugate * H) :=
  DFunLike.congr_fun (fderiv_det A) H

/-- The differential of the determinant is the sum of determinants with one row replaced. -/
theorem fderiv_det_apply_eq_sum_updateRow (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = ∑ i, (A.updateRow i (H i)).det := by
  rw [fderiv_det_apply, sum_det_updateRow_eq_trace_adjugate_mul]

/-- The inverse form of Jacobi's formula at a matrix with invertible determinant. -/
theorem fderiv_det_apply_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = A.det * trace (A⁻¹ * H) := by
  -- Write the inverse as `A.det⁻¹ • A.adjugate`, then cancel `A.det`.
  rw [fderiv_det_apply, nonsing_inv_apply A hA, smul_mul_assoc, trace_smul, smul_eq_mul,
    ← mul_assoc, hA.mul_val_inv, one_mul]

/-- **Jacobi's formula** at a matrix `A` with invertible determinant: the Fréchet derivative is
`H ↦ A.det * trace (A⁻¹ * H)`. -/
theorem hasFDerivAt_det_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (A.det • (traceCLM n 𝕜 𝕜).comp
        (A⁻¹ • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A := by
  refine (differentiable_det A).hasFDerivAt.congr_fderiv ?_
  ext H
  exact fderiv_det_apply_of_isUnit hA H

/-- The Fréchet derivative of the determinant at the identity is the trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (traceCLM n 𝕜 𝕜) 1 := by
  refine (hasFDerivAt_det 1).congr_fderiv ?_
  ext H
  simp

end Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The derivative of the determinant of a matrix-valued function. -/
@[fun_prop]
theorem HasFDerivAt.matrix_det {f : E → Matrix n n 𝕜} {f' : E →L[𝕜] Matrix n n 𝕜}
    {x : E} (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y ↦ (f y).det)
      (((Matrix.traceCLM n 𝕜 𝕜).comp
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))).comp f') x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp x hf

/-- The determinant of a differentiable matrix-valued function is differentiable. -/
@[fun_prop]
theorem DifferentiableAt.matrix_det {f : E → Matrix n n 𝕜} {x : E}
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y ↦ (f y).det) x :=
  hf.hasFDerivAt.matrix_det.differentiableAt

/-- Jacobi's formula for a differentiable matrix-valued curve. -/
theorem HasDerivAt.matrix_det {f : 𝕜 → Matrix n n 𝕜} {f' : Matrix n n 𝕜}
    {x : 𝕜} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp_hasDerivAt x hf

open scoped Matrix.Norms.Operator in
/-- The determinant of a smooth matrix-valued function is smooth, using the operator norm
on matrices. -/
@[fun_prop]
theorem ContDiff.matrix_det {r : ℕ∞ω} {f : E → Matrix n n 𝕜} (hf : ContDiff 𝕜 r f) :
    ContDiff 𝕜 r (fun x ↦ (f x).det) :=
  Matrix.contDiff_det.comp hf

open scoped Matrix.Norms.Operator in
/-- The determinant along the line `1 + t • B` has derivative `trace B` at zero. -/
theorem Matrix.hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ Matrix.det (1 + t • B)) B.trace 0 := by
  have hsmul : HasDerivAt (fun t : 𝕜 ↦ t • B) B 0 :=
    ((hasDerivAt_id (0 : 𝕜)).smul_const B).congr_deriv (one_smul 𝕜 B)
  have hline : HasDerivAt (fun t : 𝕜 ↦ 1 + t • B) B 0 :=
    hsmul.const_add 1
  simpa using hline.matrix_det
