/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Matrix.Determinant
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Derivatives of the real log-determinant

The first derivative of the real log-determinant is `H ↦ trace (A⁻¹ * H)` whenever
`det A ≠ 0`. This includes matrices with negative determinant, since `Real.log` uses
`log |x|`. The mixed second derivative of a twice differentiable matrix field has the
usual inverse-product trace formula. The finite matrix index may be empty.

Matrices use Mathlib's `L∞` operator norm. Matrix inversion is differentiated by
`Matrix.nonsing_inv_eq_ringInverse` and the existing normed-algebra inverse rule.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Matrix.Norms.Operator Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `D(log det)(M)[N] = tr(M⁻¹ N)` for `det M ≠ 0`. -/
theorem fderiv_log_det_apply (M N : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M N = Matrix.trace (M⁻¹ * N) := by
  have hd : HasFDerivAt (fun Q : Matrix ι ι ℝ => Real.log Q.det) (M.det⁻¹ • fderiv ℝ det M) M :=
    (differentiable_det M).hasFDerivAt.log hM
  rw [hd.fderiv, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    fderiv_det_apply_of_isUnit hM.isUnit, ← mul_assoc, inv_mul_cancel₀ hM, one_mul]

/-- The real log-determinant is differentiable at each nonzero determinant. -/
@[fun_prop]
theorem differentiableAt_log_det (M : Matrix ι ι ℝ) (hM : M.det ≠ 0) :
    DifferentiableAt ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) M :=
  ((differentiable_det.differentiableAt).hasFDerivAt.log hM).differentiableAt

/-- Chain rule: `D(log det ∘ M)(x)[v] = tr(M(x)⁻¹ DM(x)[v])`. -/
theorem fderiv_log_det_comp_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : G → Matrix ι ι ℝ} {x : G} (hM : DifferentiableAt ℝ M x) (hdet : (M x).det ≠ 0) (v : G) :
    fderiv ℝ (fun y => Real.log (M y).det) x v = Matrix.trace ((M x)⁻¹ * fderiv ℝ M x v) := by
  have hc : fderiv ℝ (fun y => Real.log (M y).det) x =
      fderiv ℝ (fun Q : Matrix ι ι ℝ => Real.log Q.det) (M x) ∘L fderiv ℝ M x :=
    fderiv_comp x (differentiableAt_log_det (M x) hdet) hM
  rw [hc, ContinuousLinearMap.comp_apply, fderiv_log_det_apply (M x) _ hdet]

/-- The derivative of the inverse of a differentiable matrix field at a nonzero determinant. -/
theorem fderiv_inv_comp_apply {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {M : G → Matrix ι ι 𝕜} {x : G}
    (hM : DifferentiableAt 𝕜 M x) (hdet : (M x).det ≠ 0) (v : G) :
    fderiv 𝕜 (fun y ↦ (M y)⁻¹) x v = -((M x)⁻¹ * fderiv 𝕜 M x v * (M x)⁻¹) := by
  have : CompleteSpace (Matrix ι ι 𝕜) := FiniteDimensional.completeSpace 𝕜 _
  have hu : IsUnit (M x) := (isUnit_iff_isUnit_det _).mpr hdet.isUnit
  -- Matrix inversion is `Ring.inverse`, whose derivative at a unit `A` is `H ↦ -(A⁻¹ * H * A⁻¹)`.
  have hd := (hasFDerivAt_ringInverse (𝕜 := 𝕜) hu.unit).comp x hM.hasFDerivAt
  simp only [Function.comp_def, ← nonsing_inv_eq_ringInverse, coe_units_inv,
    IsUnit.unit_spec] at hd
  -- `hd` lives on the normed-ring structure of matrices; evaluating at `v` transfers it to the
  -- additive structure used in the statement (the two agree only up to unfolding).
  have hv : fderiv 𝕜 (fun y ↦ (M y)⁻¹) x v =
      (-ContinuousLinearMap.mulLeftRight 𝕜 (Matrix ι ι 𝕜) (M x)⁻¹ (M x)⁻¹ ∘L fderiv 𝕜 M x) v :=
    congrArg (fun L : G →L[𝕜] Matrix ι ι 𝕜 ↦ L v) hd.fderiv
  exact hv.trans (congrArg Neg.neg (ContinuousLinearMap.mulLeftRight_apply 𝕜 (Matrix ι ι 𝕜)
    (M x)⁻¹ (M x)⁻¹ (fderiv 𝕜 M x v)))

omit [DecidableEq ι] in
private theorem fderiv_trace_mul_apply {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {A B : G → Matrix ι ι ℝ} {x : G}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) (v : G) :
    fderiv ℝ (fun y ↦ (A y * B y).trace) x v =
      (fderiv ℝ A x v * B x + A x * fderiv ℝ B x v).trace := by
  classical
  let T : Matrix ι ι ℝ →L[ℝ] ℝ := ⟨traceLinearMap ι ℝ ℝ, continuous_id.matrix_trace⟩
  have hd := T.hasFDerivAt.comp x (hA.hasFDerivAt.mul' hB.hasFDerivAt)
  have hv := congrArg (fun L : G →L[ℝ] ℝ ↦ L v) hd.fderiv
  calc
    _ = T ((A x • fderiv ℝ B x + MulOpposite.op (B x) • fderiv ℝ A x) v) := hv
    _ = (A x * fderiv ℝ B x v + fderiv ℝ A x v * B x).trace := by
      simp only [add_apply, smul_apply, smul_eq_mul, op_smul_eq_mul]
      exact traceLinearMap_apply ι ℝ ℝ _
    _ = _ := congrArg trace (add_comm _ _)

/-- Mixed second variation of the real log-determinant along a C2 matrix field. -/
theorem fderiv_log_det_comp_second_apply {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G}
    (hM : ContDiffAt ℝ 2 M x) (hdet : (M x).det ≠ 0) (v w : G) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) x v =
      ((M x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y w) x v).trace -
        ((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹ * fderiv ℝ M x w).trace := by
  have hM0 : DifferentiableAt ℝ M x := hM.differentiableAt (by norm_num)
  have hDM : DifferentiableAt ℝ (fun y => fderiv ℝ M y w) x :=
    ((hM.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const w)
  have hInv := hM0.inverse ((isUnit_iff_isUnit_det (M x)).mpr
    (isUnit_iff_ne_zero.mpr hdet))
  simp only [← nonsing_inv_eq_ringInverse] at hInv
  have hnear :
    (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) =ᶠ[𝓝 x]
      (fun y => ((M y)⁻¹ * fderiv ℝ M y w).trace) := by
    have hn := hM.eventually (by norm_num)
    have hnz : ∀ᶠ y in 𝓝 x, (M y).det ≠ 0 :=
      (differentiable_det.differentiableAt.continuousAt.comp hM0.continuousAt).eventually_ne
        hdet
    filter_upwards [hn, hnz] with y hy hyz
    exact fderiv_log_det_comp_apply (hy.differentiableAt (by norm_num)) hyz w
  rw [hnear.fderiv_eq, fderiv_trace_mul_apply hInv hDM v,
    fderiv_inv_comp_apply hM0 hdet v, Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg]
  ring

/-- A locally constant nonzero determinant gives the first and mixed second trace identities.
These are the differential identities in Savin, DOI 10.1007/s00526-004-0275-8,
Proposition 4.1 proof (10)--(11). -/
theorem trace_identities_of_eventually_det_const {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {M : G → Matrix ι ι ℝ} {x : G} {c : ℝ}
    (hM : ContDiffAt ℝ 2 M x) (hc : c ≠ 0) (heq : ∀ᶠ y in 𝓝 x, (M y).det = c) :
    (∀ v : G, ((M x)⁻¹ * fderiv ℝ M x v).trace = 0) ∧
      ∀ v w : G,
        ((M x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y w) x v).trace =
          ((M x)⁻¹ * fderiv ℝ M x v * (M x)⁻¹ * fderiv ℝ M x w).trace := by
  have hd : (M x).det ≠ 0 := by rw [mem_of_mem_nhds heq]; exact hc
  have hg : (fun y => Real.log (M y).det) =ᶠ[𝓝 x] (fun _ => Real.log c) := by
    filter_upwards [heq] with y hy
    rw [hy]
  constructor
  · intro v
    rw [← fderiv_log_det_comp_apply (hM.differentiableAt (by norm_num)) hd v, hg.fderiv_eq]
    simp
  · intro v w
    have hz :
      (fun y => fderiv ℝ (fun z => Real.log (M z).det) y w) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hg.eventually_nhds] with y hy
      have hyy : (fun z => Real.log (M z).det) =ᶠ[𝓝 y] (fun _ => Real.log c) := hy
      rw [hyy.fderiv_eq]
      simp
    have hs := fderiv_log_det_comp_second_apply hM hd v w
    rw [hz.fderiv_eq] at hs
    have hz0 : fderiv ℝ (fun _ : G => (0 : ℝ)) x v = 0 := by simp
    rw [hz0] at hs
    exact sub_eq_zero.mp hs.symm

end Matrix
