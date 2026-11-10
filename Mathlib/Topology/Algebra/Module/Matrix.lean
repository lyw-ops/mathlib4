/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuous linear maps on matrices

This file bundles the matrix trace as `Matrix.traceCLM`. It uses the product topology
on matrices and requires only continuous addition on the coefficient module.
-/

public section

namespace Matrix

/-- The matrix trace as a continuous linear map. -/
@[expose, simps!]
def traceCLM (n α R : Type*) [Fintype n] [Semiring α] [AddCommMonoid R]
    [Module α R] [TopologicalSpace R] [ContinuousAdd R] : Matrix n n R →L[α] R :=
  ⟨traceLinearMap n α R, continuous_id.matrix_trace⟩

end Matrix
