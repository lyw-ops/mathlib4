/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Smooth extension using bump functions

A function that is `C^n` on an open set in a real normed space admitting smooth bumps agrees
near every point of that set with a globally `C^n` function. The same extension can preserve
the values on a prescribed compact subset. The target may be an incomplete normed space.

The smoothness order may be finite or infinite. Multiplication by one bump gives the local
extension; a finite family of bumps gives the compact-set extension.
-/

@[expose] public section

open Set Metric Filter Topology
open scoped ContDiff

namespace ContDiffOn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {f : E → F} {U : Set E}

private theorem contDiff_smul_of_eventuallyEq_zero (hf : ContDiffOn ℝ n f U)
    (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ n χ)
    (hzero : ∀ x ∉ U, χ =ᶠ[𝓝 x] 0) : ContDiff ℝ n (fun x ↦ χ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [hzero x hx] with y hy
    rw [hy, Pi.zero_apply, zero_smul]

variable [HasContDiffBump E]

/-- A function smooth on an open neighbourhood has a global smooth extension agreeing on
a smaller ball about the chosen point. -/
theorem exists_contDiff_eqOn_ball (hf : ContDiffOn ℝ n f U) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) :
    ∃ (r : ℝ) (g : E → F),
      0 < r ∧ ball x r ⊆ U ∧ ContDiff ℝ n g ∧ EqOn g f (ball x r) := by
  classical
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbU : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact (closedBall_subset_ball (half_lt_self hr)).trans hrU
  refine ⟨r / 4, fun y ↦ b y • f y, by positivity,
    (ball_subset_ball (by linarith)).trans hrU, ?_, ?_⟩
  · apply hf.contDiff_smul_of_eventuallyEq_zero hU b.contDiff
    intro y hy
    exact notMem_tsupport_iff_eventuallyEq.mp fun hby ↦ hy (hbU hby)
  · intro y hy
    change b y • f y = f y
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]

/-- A function smooth on an open neighbourhood agrees near each point with a globally
smooth function of the same order. -/
theorem exists_contDiff_eventuallyEq (hf : ContDiffOn ℝ n f U) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) : ∃ g : E → F, ContDiff ℝ n g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨r, g, hr, _, hg, heq⟩ := hf.exists_contDiff_eqOn_ball hU hx
  exact ⟨g, hg, Filter.eventuallyEq_iff_exists_mem.mpr ⟨ball x r, ball_mem_nhds x hr, heq⟩⟩

/-- A function smooth on a neighbourhood of a compact set has a global smooth extension
that agrees on the compact set. -/
theorem exists_contDiff_eqOn_of_isCompact (hf : ContDiffOn ℝ n f U) {K : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ g : E → F, ContDiff ℝ n g ∧ EqOn g f K := by
  classical
  choose ε hε hball using fun x : K ↦ Metric.isOpen_iff.mp hU x.1 (hKU x.2)
  let b (i : K) : ContDiffBump i.1 :=
    ⟨ε i / 4, ε i / 2, div_pos (hε i) (by norm_num), by linarith [hε i]⟩
  have hb (i : K) : ContDiff ℝ n (b i) := (b i).contDiff
  have hbU (i : K) : tsupport (b i : E → ℝ) ⊆ U := by
    rw [(b i).tsupport_eq]
    exact (closedBall_subset_ball (half_lt_self (hε i))).trans (hball i)
  have hcover : K ⊆ ⋃ i : K, ball i.1 (ε i / 4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (div_pos (hε ⟨x, hx⟩) (by norm_num))⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : K ↦ ball i.1 (ε i / 4))
    (fun _ ↦ isOpen_ball) hcover
  let χ (x : E) : ℝ := 1 - ∏ i ∈ t, (1 - b i x)
  have hχ : ContDiff ℝ n χ :=
    contDiff_const.sub (contDiff_prod fun i _ ↦ contDiff_const.sub (hb i))
  have hzero : ∀ x ∉ U, χ =ᶠ[𝓝 x] 0 := by
    intro x hx
    have hz (i : K) : (b i : E → ℝ) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp fun hbi ↦ hx (hbU i hbi)
    filter_upwards [(Filter.eventually_all_finset t).2 fun i _ ↦ hz i] with y hy
    have hp : (∏ i ∈ t, (1 - b i y)) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by rw [hy i hi, Pi.zero_apply, sub_zero]
    change 1 - ∏ i ∈ t, (1 - b i y) = 0
    rw [hp, sub_self]
  have hone : EqOn χ (fun _ ↦ 1) K := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hx)
    obtain ⟨hit, hxi⟩ := mem_iUnion.mp hi
    have hbi : b i x = 1 := (b i).one_of_mem_closedBall (ball_subset_closedBall hxi)
    have hp : (∏ j ∈ t, (1 - b j x)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨i, hit, by rw [hbi, sub_self]⟩
    change 1 - ∏ i ∈ t, (1 - b i x) = 1
    rw [hp, sub_zero]
  refine ⟨fun x ↦ χ x • f x, hf.contDiff_smul_of_eventuallyEq_zero hU hχ hzero, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hone hx, one_smul]

end ContDiffOn
