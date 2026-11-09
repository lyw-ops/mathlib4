/-
Copyright (c) 2022 Yury Kudryashov, 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, kls-lean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Convex

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Measure and boundedness of convex sets

Let `E` be a finite-dimensional real vector space, let `μ` be a Haar measure on `E`, let `s` be a
convex set in `E`. Then the frontier of `s` has measure zero (see `Convex.addHaar_frontier`), hence
`s` is a `NullMeasurableSet` (see `Convex.nullMeasurableSet`).

A convex set with nonempty interior and finite additive Haar measure is bounded
(`Convex.isBounded_of_measure_lt_top`). This does not require a finite-dimensionality assumption.
The packing argument is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean).
-/

public section


open MeasureTheory MeasureTheory.Measure Set Metric Filter Bornology Function

open Module (finrank)

open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}

namespace Convex

/-- Haar measure of the frontier of a convex set is zero. -/
theorem addHaar_frontier (hs : Convex ℝ s) : μ (frontier s) = 0 := by
  /- If `s` is included in a hyperplane, then `frontier s ⊆ closure s` is included in the same
    hyperplane, hence it has measure zero. -/
  rcases ne_or_eq (affineSpan ℝ s) ⊤ with hspan | hspan
  · refine measure_mono_null ?_ (addHaar_affineSubspace _ _ hspan)
    exact frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan _ _) (affineSpan ℝ s).isClosed_of_finiteDimensional)
  rw [← hs.interior_nonempty_iff_affineSpan_eq_top] at hspan
  rcases hspan with ⟨x, hx⟩
  /- Without loss of generality, `s` is bounded. Indeed, `∂s ⊆ ⋃ n, ∂(s ∩ ball x (n + 1))`, hence it
    suffices to prove that `∀ n, μ (s ∩ ball x (n + 1)) = 0`; the latter set is bounded.
    -/
  suffices H : ∀ t : Set E, Convex ℝ t → x ∈ interior t → IsBounded t → μ (frontier t) = 0 by
    let B : ℕ → Set E := fun n => ball x (n + 1)
    have : μ (⋃ n : ℕ, frontier (s ∩ B n)) = 0 := by
      refine measure_iUnion_null fun n =>
        H _ (hs.inter (convex_ball _ _)) ?_ (isBounded_ball.subset inter_subset_right)
      rw [interior_inter, isOpen_ball.interior_eq]
      exact ⟨hx, mem_ball_self (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)⟩
    refine measure_mono_null (fun y hy => ?_) this; clear this
    set N : ℕ := ⌊dist y x⌋₊
    refine mem_iUnion.2 ⟨N, ?_⟩
    have hN : y ∈ B N := by simp [B, N, Nat.lt_floor_add_one]
    suffices y ∈ frontier (s ∩ B N) ∩ B N from this.1
    rw [frontier_inter_open_inter isOpen_ball]
    exact ⟨hy, hN⟩
  intro s hs hx hb
  /- Since `s` is bounded, we have `μ (interior s) ≠ ∞`, hence it suffices to prove
    `μ (closure s) ≤ μ (interior s)`. -/
  replace hb : μ (interior s) ≠ ∞ := (hb.subset interior_subset).measure_lt_top.ne
  suffices μ (closure s) ≤ μ (interior s) by
    rwa [frontier, measure_sdiff interior_subset_closure isOpen_interior.nullMeasurableSet hb,
      tsub_eq_zero_iff_le]
  /- Due to `Convex.closure_subset_image_homothety_interior_of_one_lt`, for any `r > 1` we have
    `closure s ⊆ homothety x r '' interior s`, hence `μ (closure s) ≤ r ^ d * μ (interior s)`,
    where `d = finrank ℝ E`. -/
  set d : ℕ := Module.finrank ℝ E
  have : ∀ r : ℝ≥0, 1 < r → μ (closure s) ≤ ↑(r ^ d) * μ (interior s) := fun r hr ↦ by
    refine (measure_mono <|
      hs.closure_subset_image_homothety_interior_of_one_lt hx r hr).trans_eq ?_
    rw [addHaar_image_homothety, ← NNReal.coe_pow, NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
  have : ∀ᶠ (r : ℝ≥0) in 𝓝[>] 1, μ (closure s) ≤ ↑(r ^ d) * μ (interior s) :=
    mem_of_superset self_mem_nhdsWithin this
  -- Taking the limit as `r → 1`, we get `μ (closure s) ≤ μ (interior s)`.
  refine ge_of_tendsto ?_ this
  refine (((ENNReal.continuous_mul_const hb).comp
    (ENNReal.continuous_coe.comp (continuous_pow d))).tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
  simp

/-- A convex set in a finite-dimensional real vector space is null measurable with respect to an
additive Haar measure on this space. -/
protected theorem nullMeasurableSet (hs : Convex ℝ s) : NullMeasurableSet s μ :=
  nullMeasurableSet_of_null_frontier (hs.addHaar_frontier μ)

end Convex


private theorem isBounded_of_ball_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure] {s : Set E} (hcs : Convex ℝ s)
    (hms : m s < ∞) {r : ℝ} (hr : 0 < r) (hball : ball (0 : E) r ⊆ s) : IsBounded s := by
  have hzero : (0 : E) ∈ s := hball (mem_ball_self hr)
  -- Every ball of radius `r / 2` has the same positive measure `b`; `N` such balls outweigh `s`.
  set b := m (ball (0 : E) (r / 2))
  have hbne : b ≠ 0 := (measure_ball_pos m 0 (half_pos hr)).ne'
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hbne hms.ne
  refine (isBounded_iff_subset_closedBall (0 : E)).2 ⟨2 * N * r, fun x hx => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  by_contra! hlarge
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (by positivity) hlarge
  -- Otherwise the `N` disjoint balls `B(i * r / ‖x‖ • x, r / 2)`, `i < N`, all lie in `s`.
  let f : Fin N → E := fun i => ((i.val : ℝ) * r / ‖x‖) • x
  have hinside (i : Fin N) : ball (f i) (r / 2) ⊆ s := by
    intro z hz
    let t : ℝ := (i.val : ℝ) * r / ‖x‖
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have hi : (i.val : ℝ) < (N : ℝ) := by exact_mod_cast i.isLt
    have hir : (i.val : ℝ) * r < (N : ℝ) * r := mul_lt_mul_of_pos_right hi hr
    have htupper : 2 * t ≤ 1 := by
      dsimp [t]
      rw [← mul_div_assoc, div_le_iff₀ hxpos]
      nlinarith [hir, hlarge]
    have hu : (2 : ℝ) • (z - t • x) ∈ s := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hz' : ‖z - t • x‖ < r / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        simpa [f, t] using hz
      linarith
    have hv : (2 * t) • x ∈ s := by
      have hv' :=
        hcs hzero hx (a := 1 - 2 * t) (b := 2 * t) (by linarith) (by positivity) (by ring)
      simpa using hv'
    have hm :=
      hcs hu hv (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (by norm_num)
    have he : (1 / 2 : ℝ) • ((2 : ℝ) • (z - t • x)) + (1 / 2 : ℝ) • ((2 * t) • x) = z := by
      module
    rwa [he] at hm
  have hdis : Pairwise (Disjoint on fun i => ball (f i) (r / 2)) := by
    intro i j hij
    apply ball_disjoint_ball
    have hdist : dist (f i) (f j) = |(i.val : ℝ) - (j.val : ℝ)| * r := by
      dsimp [f]
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have he :
        (i.val : ℝ) * r / ‖x‖ - (j.val : ℝ) * r / ‖x‖ =
          ((i.val : ℝ) - (j.val : ℝ)) * (r / ‖x‖) := by
        ring
      rw [he, abs_mul, abs_of_pos (div_pos hr hxpos)]
      field_simp [ne_of_gt hxpos]
    have habs : (1 : ℝ) ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      have h : (i.val : ℤ) - j.val ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Fin.val_ne_of_ne hij)
      exact_mod_cast Int.one_le_abs h
    rw [hdist]
    nlinarith
  have hmass : (N : ℝ≥0∞) * b ≤ m s := calc
    (N : ℝ≥0∞) * b = ∑ i : Fin N, m (ball (f i) (r / 2)) := by
      simp [b, addHaar_ball_center m _ (r / 2)]
    _ = m (⋃ i, ball (f i) (r / 2)) :=
      ((measure_iUnion hdis fun _ => measurableSet_ball).trans (tsum_fintype _)).symm
    _ ≤ m s := measure_mono (iUnion_subset hinside)
  exact lt_irrefl _ (hmass.trans_lt hN)

/-- A convex set with nonempty interior and finite additive Haar measure is bounded.
The interior premise is essential: lower-dimensional affine subspaces can have zero measure
and be unbounded. No closedness, set measurability or explicit dimension premise is needed. -/
theorem Convex.isBounded_of_measure_lt_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : Convex ℝ s) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hμ : μ s < ∞) (hi : (interior s).Nonempty) : Bornology.IsBounded s := by
  obtain ⟨z, hz⟩ := hi
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  -- Translate `s` so that the interior ball is centred at the origin.
  have ht : IsBounded ((z + ·) ⁻¹' s) := by
    refine isBounded_of_ball_subset μ (hs.translate_preimage_right z)
      (by simpa only [measure_preimage_add] using hμ) hr fun y hy => hball ?_
    simpa only [mem_ball, dist_eq_norm_sub, add_sub_cancel_left, sub_zero] using hy
  rw [← image_preimage_eq s (add_left_surjective z)]
  exact (isometry_add_left z).lipschitzWith.isBounded_image ht
