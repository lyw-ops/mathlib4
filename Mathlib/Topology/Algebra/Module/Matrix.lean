/-
Copyright (c) 2026 Lazyfill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazyfill
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
def traceCLM (n 𝕜 R : Type*) [Fintype n] [Semiring 𝕜] [AddCommMonoid R]
    [Module 𝕜 R] [TopologicalSpace R] [ContinuousAdd R] : Matrix n n R →L[𝕜] R :=
  ⟨traceLinearMap n 𝕜 R, continuous_id.matrix_trace⟩

end Matrix
