/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap.AdjointComp

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Von Neumann's theorem for closed operators

If `T` is a closed densely defined operator between Hilbert spaces over `ℝ` or `ℂ`, then
`LinearPMap.adjointComp T`, the maximal-domain operator `T†T`, is self-adjoint and densely
defined. The map `x ↦ x + T†T x` on its domain is surjective.

Surjectivity follows by projecting `(z, 0)` onto the graph of `T` in the Hilbert product.
The domain density is proved directly from surjectivity and the form identity, before it
is used to establish self-adjointness.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
* The real-Hilbert argument in the KLS formalization,
  `Analysis/Semigroup/VonNeumann.lean`, at
  https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d.
-/

public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The form identity for `T†T` needs density of the domain of `T`, but not closedness. -/
theorem inner_adjointComp {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) {y : E} (hy : y ∈ T.domain) :
    ⟪adjointComp T x, y⟫ =
      ⟪T ⟨x, adjointCompDomain_le T x.2⟩, T ⟨y, hy⟩⟫ := by
  rw [adjointComp_apply]
  exact adjoint_isFormalAdjoint hd _ ⟨y, hy⟩

/-- The maximal-domain operator `T†T` is a formal adjoint of itself. -/
theorem adjointComp_isFormalAdjoint {T : E →ₗ.[𝕜] F}
    (hd : Dense (T.domain : Set E)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  rw [inner_adjointComp hd x (adjointCompDomain_le T y.2), adjointComp_apply]
  exact (adjoint_isFormalAdjoint hd (T := T)).symm
    ⟨x, adjointCompDomain_le T x.2⟩
    ⟨T ⟨y, adjointCompDomain_le T y.2⟩, (mem_adjointCompDomain.mp y.2).choose_spec⟩

variable [CompleteSpace F]

/-- Orthogonal projection onto the closed graph solves the weak equation for `I + T†T`. -/
private theorem exists_inner_sub_eq_inner (T : E →ₗ.[𝕜] F) (hT : T.IsClosed) (z : E) :
    ∃ u : T.domain, ∀ v : T.domain, ⟪z - (u : E), (v : E)⟫ = ⟪T u, T v⟫ := by
  let e := WithLp.prodContinuousLinearEquiv 2 𝕜 E F
  let K : Submodule 𝕜 (WithLp 2 (E × F)) := T.graph.comap e.toLinearMap
  have hK : _root_.IsClosed (K : Set (WithLp 2 (E × F))) := hT.preimage e.continuous
  let : CompleteSpace K := hK.completeSpace_coe
  let a : WithLp 2 (E × F) := WithLp.toLp 2 (z, (0 : F))
  let p := K.starProjection a
  have hp : e p ∈ T.graph := K.starProjection_apply_mem a
  rw [show e p = WithLp.ofLp p from WithLp.prodContinuousLinearEquiv_apply ..] at hp
  obtain ⟨u, hu1, hu2⟩ := T.mem_graph_iff.mp hp
  refine ⟨u, fun v ↦ ?_⟩
  have hv : WithLp.toLp 2 ((v : E), T v) ∈ K := by
    change e (WithLp.toLp 2 ((v : E), T v)) ∈ T.graph
    rw [show e (WithLp.toLp 2 ((v : E), T v)) = ((v : E), T v) from
      WithLp.prodContinuousLinearEquiv_apply ..]
    exact T.mem_graph v
  have h := K.starProjection_inner_eq_zero a _ hv
  simp only [inner_sub_left, WithLp.prod_inner_apply, a,
    inner_zero_left, add_zero] at h
  change ⟪z, (v : E)⟫ -
    (⟪(WithLp.ofLp p).1, (v : E)⟫ + ⟪(WithLp.ofLp p).2, T v⟫) = 0 at h
  rw [← hu1, ← hu2] at h
  rw [inner_sub_left]
  linear_combination h

/-- For a closed densely defined `T`, every vector is `x + T†T x` for a point in the maximal
composition domain. -/
theorem surjective_add_adjointComp (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    Function.Surjective (fun x : (adjointComp T).domain ↦ (x : E) + adjointComp T x) := by
  intro z
  obtain ⟨u, hu⟩ := exists_inner_sub_eq_inner T hT z
  have hTu : T u ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨z - (u : E), hu⟩
  refine ⟨⟨u, mem_adjointComp_domain.mpr ⟨u.2, hTu⟩⟩, ?_⟩
  dsimp only
  rw [adjointComp_apply]
  change (u : E) + T† ⟨T u, hTu⟩ = z
  rw [adjoint_apply_eq hd _ hu]
  abel

/-- The maximal domain of `T†T` is dense for a closed densely defined operator `T`. -/
theorem dense_adjointComp_domain (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Dense ((adjointComp T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, hx⟩ := surjective_add_adjointComp T hT hd z
  dsimp only at hx
  have hzero : ⟪(x : E), z⟫ = 0 := hz (x : E) x.2
  have hsum : RCLike.re ⟪(x : E), (x : E)⟫ +
      RCLike.re ⟪T ⟨x, adjointCompDomain_le T x.2⟩,
        T ⟨x, adjointCompDomain_le T x.2⟩⟫ = 0 := by
    have h := congrArg RCLike.re hzero
    rw [← hx, inner_add_right, _root_.map_add RCLike.re,
      inner_re_symm (x : E) (adjointComp T x),
      inner_adjointComp hd x (adjointCompDomain_le T x.2)] at h
    simpa only [_root_.map_zero] using h
  have hx0 : (x : E) = 0 := re_inner_self_nonpos.mp <| by
    have hn : 0 ≤ RCLike.re ⟪T ⟨x, adjointCompDomain_le T x.2⟩,
        T ⟨x, adjointCompDomain_le T x.2⟩⟫ := inner_self_nonneg
    linarith
  have hx' : x = 0 := Subtype.ext hx0
  rw [← hx, hx']
  simp

/-- **Von Neumann's theorem:** `T†T` on its maximal domain is self-adjoint when `T` is closed
and densely defined. -/
theorem isSelfAdjoint_adjointComp (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : IsSelfAdjoint (adjointComp T) := by
  have hdA := dense_adjointComp_domain T hT hd
  have hsym := adjointComp_isFormalAdjoint hd
  have hle : adjointComp T ≤ (adjointComp T)† := hsym.le_adjoint hdA
  have hfa := (adjoint_isFormalAdjoint hdA (T := adjointComp T)).symm
  -- It remains to show that `(T†T)†` has no larger domain. For `y` in that domain, solve
  -- `u + T†T u = y + (T†T)† y`; then `y - u` is orthogonal to every `x + T†T x`, i.e. to `E`.
  have hmem (y : ((adjointComp T)†).domain) : (y : E) ∈ (adjointComp T).domain := by
    obtain ⟨u, hu⟩ := surjective_add_adjointComp T hT hd ((y : E) + (adjointComp T)† y)
    dsimp only at hu
    have hperp (z : E) : ⟪z, (y : E) - u⟫ = 0 := by
      obtain ⟨x, rfl⟩ := surjective_add_adjointComp T hT hd z
      dsimp only
      rw [inner_sub_right, inner_add_left, inner_add_left, hfa x y, hsym x u,
        ← inner_add_right, ← inner_add_right, hu, sub_self]
    have hyu : (y : E) = u := sub_eq_zero.mp (inner_self_eq_zero.mp (hperp _))
    exact hyu ▸ u.2
  rw [isSelfAdjoint_def]
  exact (eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun y hy ↦ hmem ⟨y, hy⟩)).symm

end LinearPMap
