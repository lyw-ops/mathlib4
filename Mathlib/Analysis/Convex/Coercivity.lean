/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Order.Compact

/-!
# Compact sublevels and attained minima of integrable convex potentials

If a finite convex real function has integrable negative exponential for an additive Haar
measure, its sublevels are compact and it attains a global minimum. This is the coercivity
step for convex potentials. A finite-dimensional real normed space suffices;
no inner product or positive-dimension assumption is used.

Adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean).
-/

public section

open MeasureTheory Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {φ : E → ℝ}

/-- Every sublevel of a finite convex potential with integrable negative exponential
is compact. The ambient real normed space may have dimension zero. -/
theorem ConvexOn.isCompact_sublevel_of_integrable_exp_neg
    (hφ : ConvexOn ℝ univ φ) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hint : Integrable (fun x => Real.exp (-φ x)) μ) (c : ℝ) :
    IsCompact {x | φ x ≤ c} := by
  have hcont : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  let d : ℝ := max c (φ 0 + 1)
  have hcd : c ≤ d := le_max_left _ _
  have hzero : φ (0 : E) < d := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hfinite : μ {x | φ x ≤ d} < ∞ := by
    simpa only [Real.exp_le_exp, neg_le_neg_iff] using
      hint.measure_ge_lt_top (Real.exp_pos (-d))
  have hconvex : Convex ℝ {x | φ x ≤ d} := by
    simpa only [Set.mem_univ, true_and] using hφ.convex_le d
  have hbounded := hconvex.isBounded_of_measure_lt_top μ hfinite
    ⟨0, mem_interior_iff_mem_nhds.mpr <|
      Filter.mem_of_superset ((isOpen_lt hcont continuous_const).mem_nhds hzero)
        fun x hx => le_of_lt hx⟩
  exact Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
    (hbounded.subset fun _ hx => hx.trans hcd)

/-- A finite convex potential with integrable negative exponential attains its global
minimum. Neither probability normalization nor a positive-dimension hypothesis is required. -/
theorem ConvexOn.exists_forall_le_of_integrable_exp_neg
    (hφ : ConvexOn ℝ univ φ) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hint : Integrable (fun x => Real.exp (-φ x)) μ) : ∃ a, ∀ x, φ a ≤ φ x := by
  have hcont : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  obtain ⟨a, ha, hmin⟩ :=
    (hφ.isCompact_sublevel_of_integrable_exp_neg μ hint (φ 0)).exists_isMinOn
      (show ({x | φ x ≤ φ 0} : Set E).Nonempty from ⟨0, by simp⟩) hcont.continuousOn
  refine ⟨a, fun x => ?_⟩
  by_cases hx : φ x ≤ φ 0
  · exact hmin hx
  · exact ha.trans (lt_of_not_ge hx).le
