/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.AdjugateTrace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Smoothness and derivatives of the determinant

The determinant is smooth over any nontrivially normed field. Its strict Fréchet
derivative at `A` sends `H` to `trace (adjugate A * H)`, including when `A` is
singular. At an invertible matrix this is `det A * trace (A⁻¹ * H)`.
Finite index types may be empty; no completeness assumption on the field is needed.

## Main results

* `Matrix.contDiff_det`: smoothness of the determinant.
* `Matrix.hasStrictFDerivAt_det` and `Matrix.hasFDerivAt_det`: Jacobi's adjugate formula.
* `Matrix.fderiv_det_apply`: the differential evaluated on a matrix direction.
* `Matrix.hasFDerivAt_det_of_isUnit`: Jacobi's formula in terms of the inverse matrix.
* `Matrix.hasFDerivAt_det_one`: the differential at the identity is the trace.
* `Matrix.hasDerivAt_det_one_add_smul`: the derivative of `det (1 + t • B)` at zero.

## Implementation details

The proof treats the determinant as a continuous multilinear map of its rows.
The matrix norm used here is the `L∞` operator norm (`Matrix.Norms.Operator`).
The multilinear representation uses the sup norm on `n → n → 𝕜`. These norms differ,
but the topological structures are definitionally equal. Mathlib defines derivatives
using `IsLittleOTVS`, so the derivative statements transfer by unfolding without
identifying the norms. The continuous linear map in `Matrix.contDiff_det` makes
the change of norm explicit in the smoothness proof.

The multilinear proof is adapted from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/blob/ed6c0aa3acc0a3cb56901dc406167cdbad593f59/TauCeti/Analysis/Calculus/FDeriv/Det.lean),
which generalizes the real determinant calculus from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean).
-/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ContDiff

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

private noncomputable def detMultilinear :
    ContinuousMultilinearMap 𝕜 (fun _ : n ↦ n → 𝕜) 𝕜 :=
  -- Represent the determinant on the product of its rows, with the sup norm.
  { (detRowAlternating : (n → 𝕜) [⋀^n]→ₗ[𝕜] 𝕜).toMultilinearMap with
    cont := continuous_id.matrix_det }

/-- The determinant is smooth at every square matrix, including singular matrices. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) := by
  -- The identity from operator-normed matrices to the sup-normed product of rows.
  let L : Matrix n n 𝕜 →L[𝕜] (n → n → 𝕜) :=
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := continuous_id }
  exact (detMultilinear (n := n) (𝕜 := 𝕜)).contDiff.comp L.contDiff

/-- The determinant is differentiable without a completeness assumption on the field. -/
@[fun_prop]
theorem differentiable_det : Differentiable 𝕜 (det : Matrix n n 𝕜 → 𝕜) :=
  contDiff_det.differentiable one_ne_zero

/-- **Jacobi's formula** for the strict derivative, valid also at singular matrices. -/
theorem hasStrictFDerivAt_det (A : Matrix n n 𝕜) :
    HasStrictFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ((⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ : Matrix n n 𝕜 →L[𝕜] 𝕜).comp
        (ContinuousLinearMap.mul 𝕜 (Matrix n n 𝕜) A.adjugate)) A := by
  refine (detMultilinear.hasStrictFDerivAt (fun i ↦ A i)).congr_fderiv ?_
  ext H
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  exact sum_det_updateRow_eq_trace_adjugate_mul A H

/-- **Jacobi's formula** for the Fréchet derivative, with no invertibility premise.
For rewriting, use `Matrix.fderiv_det_apply`. -/
theorem hasFDerivAt_det (A : Matrix n n 𝕜) :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ((⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ : Matrix n n 𝕜 →L[𝕜] 𝕜).comp
        (ContinuousLinearMap.mul 𝕜 (Matrix n n 𝕜) A.adjugate)) A :=
  (hasStrictFDerivAt_det A).hasFDerivAt

/-- Jacobi's formula evaluated on a direction, including at singular matrices. -/
theorem fderiv_det_apply (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = trace (A.adjugate * H) :=
  congrArg (fun L : Matrix n n 𝕜 →L[𝕜] 𝕜 ↦ L H) (hasFDerivAt_det A).fderiv

/-- The differential of the determinant is the sum of determinants with one row replaced. -/
theorem fderiv_det_eq_sum_updateRow (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = ∑ i, (A.updateRow i (H i)).det := by
  rw [fderiv_det_apply, sum_det_updateRow_eq_trace_adjugate_mul]

/-- The inverse form of Jacobi's formula at a matrix with invertible determinant. -/
theorem fderiv_det_apply_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A.det)
    (H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = A.det * trace (A⁻¹ * H) := by
  rw [fderiv_det_apply, nonsing_inv_apply A hA, smul_mul_assoc, trace_smul, smul_eq_mul,
    ← mul_assoc, hA.mul_val_inv, one_mul]

/-- The inverse form of the Fréchet derivative of the determinant. -/
theorem hasFDerivAt_det_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (A.det • (⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ : Matrix n n 𝕜 →L[𝕜] 𝕜).comp
        (ContinuousLinearMap.mul 𝕜 (Matrix n n 𝕜) A⁻¹)) A := by
  refine (differentiable_det A).hasFDerivAt.congr_fderiv ?_
  ext H
  exact fderiv_det_apply_of_isUnit hA H

/-- The Fréchet derivative of the determinant at the identity is the trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ 1 :=
  (hasFDerivAt_det 1).congr_fderiv <| by
    ext H
    change trace (adjugate (1 : Matrix n n 𝕜) * H) = trace H
    simp

/-- The determinant along the line `1 + t • B` has derivative `trace B` at zero. -/
theorem hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ det (1 + t • B)) (trace B) 0 := by
  have h := hasFDerivAt_det_one.comp_hasDerivAt_of_eq (0 : 𝕜)
    (((hasDerivAt_id (0 : 𝕜)).smul_const B).const_add 1) (by simp)
  rwa [one_smul] at h

end Matrix
