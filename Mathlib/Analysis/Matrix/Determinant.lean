/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
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

* `Matrix.hasStrictFDerivAt_det` and `Matrix.hasFDerivAt_det`: Jacobi's formula.
* `Matrix.fderiv_det` and `Matrix.fderiv_det_apply`: formulas for the differential.
* `Matrix.hasFDerivAt_det_of_isUnit`: the inverse-matrix form of Jacobi's formula.
* `HasFDerivAt.matrix_det`, `HasDerivAt.matrix_det` and their strict and within-a-set
  variants: derivatives of determinants of matrix-valued functions.
* `DifferentiableAt.matrix_det` and its variants: differentiability of such determinants.
* `Matrix.contDiff_det`, `Matrix.contDiff_det_elementwise` and `Matrix.contDiff_det_frobenius`:
  smoothness of the determinant for the operator, elementwise and Frobenius norms.
* `ContDiff.matrix_det` and its variants: smoothness of determinants of matrix-valued
  functions, for the operator norm.

## Implementation details

The proof views the determinant as a continuous multilinear map of its rows.
In the differential, `B • ContinuousLinearMap.id 𝕜 _` is the map `H ↦ B * H`.
The first-derivative statements use the product topology on matrices, without choosing
a matrix norm.

Smoothness is only defined on normed spaces, so each smoothness statement fixes a matrix norm.
The composition lemmas `ContDiff.matrix_det`, `ContDiffAt.matrix_det`, ... use
`Matrix.Norms.Operator`; for the other two norms, compose with `Matrix.contDiff_det_elementwise`
or `Matrix.contDiff_det_frobenius`, or use `fun_prop`.

The proof is adapted from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/blob/ed6c0aa3acc0a3cb56901dc406167cdbad593f59/TauCeti/Analysis/Calculus/FDeriv/Det.lean)
and the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean).
-/

public section

open scoped ContDiff

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace Matrix

/-- The determinant as a continuous multilinear map of the rows of a matrix. -/
private noncomputable def detMultilinear :
    ContinuousMultilinearMap 𝕜 (fun _ : n ↦ n → 𝕜) 𝕜 :=
  { (detRowAlternating : (n → 𝕜) [⋀^n]→ₗ[𝕜] 𝕜).toMultilinearMap with
    cont := continuous_id.matrix_det }

/-- The determinant is smooth on any normed space `M` mapped continuously and linearly to
the product of rows. The matrix norms below apply this to the identity map, which is
continuous because each of them induces the product topology. -/
private theorem contDiff_detMultilinear_comp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {r : ℕ∞ω} (toRows : M →L[𝕜] (n → n → 𝕜)) :
    ContDiff 𝕜 r fun A ↦ detMultilinear (n := n) (𝕜 := 𝕜) (toRows A) :=
  detMultilinear.contDiff.comp toRows.contDiff

open scoped Matrix.Norms.Operator in
/-- The determinant is smooth for the operator norm on matrices. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) :=
  contDiff_detMultilinear_comp (M := Matrix n n 𝕜) (n := n) (𝕜 := 𝕜)
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := continuous_id }

open scoped Matrix.Norms.Elementwise in
/-- The determinant is smooth for the elementwise norm on matrices. -/
@[fun_prop]
theorem contDiff_det_elementwise {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) :=
  contDiff_detMultilinear_comp (M := Matrix n n 𝕜) (n := n) (𝕜 := 𝕜)
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := continuous_id }

open scoped Matrix.Norms.Frobenius in
/-- The determinant is smooth for the Frobenius norm on matrices. -/
@[fun_prop]
theorem contDiff_det_frobenius {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) :=
  contDiff_detMultilinear_comp (M := Matrix n n 𝕜) (n := n) (𝕜 := 𝕜)
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := continuous_id }

/-- **Jacobi's formula:** the strict derivative at `A` sends `H` to
`trace (A.adjugate * H)`. -/
theorem hasStrictFDerivAt_det (A : Matrix n n 𝕜) :
    HasStrictFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (traceCLM n 𝕜 𝕜 ∘L (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A := by
  -- `Matrix n n 𝕜` unfolds to the product of rows `n → n → 𝕜`, with the same topology.
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
      (traceCLM n 𝕜 𝕜 ∘L (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A :=
  (hasStrictFDerivAt_det A).hasFDerivAt

/-- The determinant is differentiable. -/
@[fun_prop]
theorem differentiable_det : Differentiable 𝕜 (det : Matrix n n 𝕜 → 𝕜) :=
  fun A ↦ (hasFDerivAt_det A).differentiableAt

/-- Jacobi's formula as an equality of continuous linear maps. -/
theorem fderiv_det (A : Matrix n n 𝕜) :
    fderiv 𝕜 det A = traceCLM n 𝕜 𝕜 ∘L (A.adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜)) :=
  (hasFDerivAt_det A).fderiv

/-- Jacobi's formula evaluated on a matrix direction. -/
@[simp]
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
      (A.det • traceCLM n 𝕜 𝕜 ∘L (A⁻¹ • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) A := by
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

section FDeriv

variable {f : E → Matrix n n 𝕜} {f' : E →L[𝕜] Matrix n n 𝕜} {x : E} {s : Set E}

/-- The strict derivative of the determinant of a matrix-valued function. -/
@[fun_prop]
theorem HasStrictFDerivAt.matrix_det (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun y ↦ (f y).det)
      ((Matrix.traceCLM n 𝕜 𝕜 ∘L
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) ∘L f') x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasStrictFDerivAt_det (f x)).comp x hf

/-- The derivative within a set of the determinant of a matrix-valued function. -/
@[fun_prop]
theorem HasFDerivWithinAt.matrix_det (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (fun y ↦ (f y).det)
      ((Matrix.traceCLM n 𝕜 𝕜 ∘L
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) ∘L f') s x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp_hasFDerivWithinAt x hf

/-- The derivative of the determinant of a matrix-valued function. -/
@[fun_prop]
theorem HasFDerivAt.matrix_det (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y ↦ (f y).det)
      ((Matrix.traceCLM n 𝕜 𝕜 ∘L
        ((f x).adjugate • ContinuousLinearMap.id 𝕜 (Matrix n n 𝕜))) ∘L f') x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp x hf

/-- The determinant of a matrix-valued function differentiable within a set at a point is
differentiable within that set at that point. -/
@[fun_prop]
theorem DifferentiableWithinAt.matrix_det (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y ↦ (f y).det) s x :=
  hf.hasFDerivWithinAt.matrix_det.differentiableWithinAt

/-- The determinant of a differentiable matrix-valued function is differentiable. -/
@[fun_prop]
theorem DifferentiableAt.matrix_det (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y ↦ (f y).det) x :=
  hf.hasFDerivAt.matrix_det.differentiableAt

/-- The determinant of a matrix-valued function differentiable on a set is differentiable
on that set. -/
@[fun_prop]
theorem DifferentiableOn.matrix_det (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y ↦ (f y).det) s :=
  fun x hx ↦ (hf x hx).matrix_det

/-- The determinant of a differentiable matrix-valued function is differentiable. -/
@[fun_prop]
theorem Differentiable.matrix_det (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (fun y ↦ (f y).det) :=
  fun x ↦ (hf x).matrix_det

end FDeriv

section Deriv

variable {f : 𝕜 → Matrix n n 𝕜} {f' : Matrix n n 𝕜} {x : 𝕜} {s : Set 𝕜}

/-- Jacobi's formula for a strictly differentiable matrix-valued curve. -/
theorem HasStrictDerivAt.matrix_det (hf : HasStrictDerivAt f f' x) :
    HasStrictDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasStrictFDerivAt_det (f x)).comp_hasStrictDerivAt x hf

/-- Jacobi's formula for a matrix-valued curve differentiable within a set. -/
theorem HasDerivWithinAt.matrix_det (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace s x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp_hasDerivWithinAt x hf

/-- Jacobi's formula for a differentiable matrix-valued curve. -/
theorem HasDerivAt.matrix_det (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).det) ((f x).adjugate * f').trace x :=
  open scoped Matrix.Norms.Operator in
    (Matrix.hasFDerivAt_det (f x)).comp_hasDerivAt x hf

end Deriv

section ContDiff

open scoped Matrix.Norms.Operator

variable {r : ℕ∞ω} {f : E → Matrix n n 𝕜} {x : E} {s : Set E}

/-- The determinant of a matrix-valued function smooth within a set at a point is smooth
within that set at that point, using the operator norm on matrices. -/
@[fun_prop]
theorem ContDiffWithinAt.matrix_det (hf : ContDiffWithinAt 𝕜 r f s x) :
    ContDiffWithinAt 𝕜 r (fun y ↦ (f y).det) s x :=
  Matrix.contDiff_det.comp_contDiffWithinAt hf

/-- The determinant of a matrix-valued function smooth at a point is smooth at that point,
using the operator norm on matrices. -/
@[fun_prop]
theorem ContDiffAt.matrix_det (hf : ContDiffAt 𝕜 r f x) :
    ContDiffAt 𝕜 r (fun y ↦ (f y).det) x :=
  Matrix.contDiff_det.comp_contDiffAt x hf

/-- The determinant of a matrix-valued function smooth on a set is smooth on that set,
using the operator norm on matrices. -/
@[fun_prop]
theorem ContDiffOn.matrix_det (hf : ContDiffOn 𝕜 r f s) :
    ContDiffOn 𝕜 r (fun y ↦ (f y).det) s :=
  Matrix.contDiff_det.comp_contDiffOn hf

/-- The determinant of a smooth matrix-valued function is smooth, using the operator norm
on matrices. -/
@[fun_prop]
theorem ContDiff.matrix_det (hf : ContDiff 𝕜 r f) :
    ContDiff 𝕜 r (fun y ↦ (f y).det) :=
  Matrix.contDiff_det.comp hf

end ContDiff

/-- The determinant along the line `1 + t • B` has derivative `trace B` at zero. -/
theorem Matrix.hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 ↦ Matrix.det (1 + t • B)) B.trace 0 := by
  open scoped Matrix.Norms.Operator in
  have hsmul : HasDerivAt (fun t : 𝕜 ↦ t • B) B 0 :=
    ((hasDerivAt_id (0 : 𝕜)).smul_const B).congr_deriv (one_smul 𝕜 B)
  have hline : HasDerivAt (fun t : 𝕜 ↦ 1 + t • B) B 0 := hsmul.const_add 1
  simpa using hline.matrix_det
