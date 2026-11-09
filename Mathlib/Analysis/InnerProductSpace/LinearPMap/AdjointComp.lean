/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# The maximal-domain operator `T†T`

For a partially defined operator `T`, `LinearPMap.adjointComp T` is the operator `T†T`
with domain `{x ∈ T.domain | T x ∈ T†.domain}`. This is the maximal composition domain;
it does not require all values of `T` to belong to the domain of its adjoint.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]
* Adapted from the KLS formalization, `Analysis/Semigroup/AdjointComp.lean` at
  https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The maximal domain of the composition `T†T`. -/
def adjointCompDomain (T : E →ₗ.[𝕜] F) : Submodule 𝕜 E :=
  (Submodule.comap T.toFun T†.domain).map T.domain.subtype

/-- Membership in the maximal domain of `T†T`. -/
@[simp]
theorem mem_adjointCompDomain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ adjointCompDomain T ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain := by
  constructor
  · rintro ⟨⟨y, hy⟩, h, rfl⟩
    exact ⟨hy, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

/-- The domain of `T†T` is contained in the domain of `T`. -/
theorem adjointCompDomain_le (T : E →ₗ.[𝕜] F) : adjointCompDomain T ≤ T.domain :=
  fun _ hx ↦ (mem_adjointCompDomain.mp hx).1

/-- The composition `T†T` on its maximal domain. -/
def adjointComp (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] E where
  domain := adjointCompDomain T
  toFun := T†.toFun.comp
    ((T.toFun.comp (Submodule.inclusion (adjointCompDomain_le T))).codRestrict T†.domain
      fun x ↦ (mem_adjointCompDomain.mp x.2).choose_spec)

/-- The domain of `adjointComp T` is `adjointCompDomain T`. -/
@[simp]
theorem adjointComp_domain (T : E →ₗ.[𝕜] F) :
    (adjointComp T).domain = adjointCompDomain T := rfl

/-- The domain of `adjointComp T` is precisely the maximal composition domain. -/
theorem mem_adjointComp_domain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ (adjointComp T).domain ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain :=
  mem_adjointCompDomain

/-- Evaluation of the maximal-domain composition. -/
@[simp]
theorem adjointComp_apply (T : E →ₗ.[𝕜] F) (x : (adjointComp T).domain) :
    adjointComp T x = T† ⟨T ⟨x, adjointCompDomain_le T x.2⟩,
      (mem_adjointCompDomain.mp x.2).choose_spec⟩ := rfl

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The maximal-domain composition for a bounded operator restricted to a dense submodule
is the restriction of its bounded adjoint composition to the same submodule. -/
theorem toPMap_adjointComp (A : E →L[𝕜] F) {p : Submodule 𝕜 E}
    (hp : Dense (p : Set E)) :
    LinearPMap.adjointComp (A.toPMap p) = (A.adjoint.comp A).toPMap p := by
  have ha := A.toPMap_adjoint_eq_adjoint_toPMap_of_dense hp
  ext x hx hy
  · simp only [LinearPMap.mem_adjointComp_domain, LinearMap.toPMap_domain, ha,
      Submodule.mem_top, exists_prop, and_true]
  · rw [LinearPMap.adjointComp_apply]
    exact LinearPMap.adjoint_apply_eq hp _ (fun v ↦ A.adjoint_inner_left _ _)

end ContinuousLinearMap
