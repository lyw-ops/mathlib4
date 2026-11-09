/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Determinant

/-!
# Smoothness of the determinant of a continuous linear endomorphism

`ContinuousLinearMap.contDiff_det` transfers determinant smoothness from matrices
using coordinates in a finite basis. The scalar field is complete; the finite-dimensional
normed space need not be equipped with an inner product.

Adapted from the Tau Ceti determinant calculus used by the KLS formalization.
-/

@[expose] public section

open scoped Matrix.Norms.Operator ContDiff

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

/-- The determinant of an endomorphism of a finite-dimensional normed space is smooth. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} :
    ContDiff 𝕜 r (fun f : E →L[𝕜] E ↦ LinearMap.det (f : E →ₗ[𝕜] E)) := by
  let b := Module.finBasis 𝕜 E
  -- `f ↦ LinearMap.toMatrix b b f` is linear on a finite-dimensional space, hence smooth,
  -- and `det f` is the determinant of this matrix.
  let L := LinearMap.toContinuousLinearMap
    ((LinearMap.toMatrix b b).toLinearMap ∘ₗ ContinuousLinearMap.coeLM 𝕜)
  convert (Matrix.contDiff_det (r := r)).comp L.contDiff using 1
  funext f
  exact (LinearMap.det_toMatrix b _).symm

end ContinuousLinearMap
