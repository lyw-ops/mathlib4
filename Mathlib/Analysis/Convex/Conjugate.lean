/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Lyu Yuwei
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The Legendre–Fenchel conjugate for a bilinear pairing

For real modules paired by `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`, the conjugate of `f : E → EReal` is
`LinearMap.fenchelConjugate B f y = ⨆ x, (B x y - f x)`. No nondegeneracy or topology is
required for this definition, the Fenchel–Young inequality, the antitone Galois connection,
the biconjugate inequality, or the triple-conjugate identity.

Every conjugate has a convex real epigraph. It is lower semicontinuous for any topology on
`F` making each functional `B x` continuous. The Fenchel–Moreau theorem for a compatible
pairing on a locally convex space is proved in `Mathlib.Analysis.Convex.FenchelMoreau`.

The values `⊥` and `⊤` are allowed. Only a real number is subtracted from an extended value
or vice versa in the definition, so no `∞ - ∞` occurs. The additive Fenchel–Young inequality
has explicit hypotheses excluding `⊥ + ⊤`.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton Mathematical Series 28, 1970, §12.
* The dual-pair formulation in `TauCeti/Analysis/Convex/Conjugate.lean` at
  https://github.com/TauCetiProject/TauCeti/tree/d2083f0f1dd2136d02467ba36efbbe1af612e89c.
-/

public section

noncomputable section

namespace LinearMap

variable {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]

/-- The Legendre–Fenchel conjugate of `f : E → EReal` with respect to the pairing `B`, the function
`y ↦ ⨆ x, (B x y - f x)` on `F`. The subtraction is of an extended real from a real, so it is
always defined; the supremum is `⊥` exactly when `f ≡ ⊤`, and it is `⊤` as soon as `f` takes the
value `⊥`. -/
def fenchelConjugate (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (y : F) : EReal :=
  ⨆ x, ((B x y : EReal) - f x)

variable (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {f : E → EReal} {g : F → EReal} {x : E} {y : F} {a : EReal}

/-- The defining formula for the Legendre–Fenchel conjugate. -/
theorem fenchelConjugate_apply (f : E → EReal) (y : F) :
    fenchelConjugate B f y = ⨆ x, ((B x y : EReal) - f x) := (rfl)

/-! ### The Fenchel–Young inequality -/

/-- **The Fenchel–Young inequality**, in the form that holds with no hypothesis: every point of `E`
bounds the conjugate from below. -/
theorem sub_le_fenchelConjugate (f : E → EReal) (x : E) (y : F) :
    (B x y : EReal) - f x ≤ fenchelConjugate B f y :=
  le_iSup (fun x => (B x y : EReal) - f x) x

/-- An upper bound for the conjugate at a point is an upper bound for every term of the
supremum. -/
theorem fenchelConjugate_le_iff :
    fenchelConjugate B f y ≤ a ↔ ∀ x, (B x y : EReal) - f x ≤ a :=
  iSup_le_iff

/-- A bound valid for every term of the supremum bounds the conjugate. -/
theorem fenchelConjugate_le (h : ∀ x, (B x y : EReal) - f x ≤ a) : fenchelConjugate B f y ≤ a :=
  iSup_le h

/-- The conjugate is `⊤` everywhere as soon as `f` takes the value `⊥` somewhere. -/
theorem fenchelConjugate_eq_top_of_eq_bot (hx : f x = ⊥) (y : F) :
    fenchelConjugate B f y = ⊤ :=
  top_le_iff.1 <| by
    have h := sub_le_fenchelConjugate B f x y
    rwa [hx, EReal.coe_sub_bot] at h

/-- The conjugate takes the value `⊥` exactly when `f` is identically `⊤`. -/
@[simp]
theorem fenchelConjugate_eq_bot_iff : fenchelConjugate B f y = ⊥ ↔ ∀ x, f x = ⊤ := by
  simp only [fenchelConjugate_apply, iSup_eq_bot, sub_eq_add_neg, EReal.add_eq_bot_iff,
    EReal.coe_ne_bot, false_or, EReal.neg_eq_bot_iff]

/-- The conjugate is not `⊥` as soon as `f` is finite or `⊥` somewhere. -/
theorem fenchelConjugate_ne_bot (hx : f x ≠ ⊤) (y : F) : fenchelConjugate B f y ≠ ⊥ :=
  fun h => hx ((fenchelConjugate_eq_bot_iff B).1 h x)

/-- **The Fenchel–Young inequality** in additive form, `⟪x, y⟫ ≤ f x + f⋆ y`, valid whenever
neither summand is `⊥`; the second summand is `⊥` only when `f ≡ ⊤`. -/
theorem le_add_fenchelConjugate (hx : f x ≠ ⊥) (hy : fenchelConjugate B f y ≠ ⊥) :
    (B x y : EReal) ≤ f x + fenchelConjugate B f y := by
  rcases eq_or_ne (f x) ⊤ with hx' | hx'
  · rw [hx', EReal.top_add_of_ne_bot hy]
    exact le_top
  · rw [add_comm]
    exact (EReal.sub_le_iff_le_add (.inl hx) (.inl hx')).1 (sub_le_fenchelConjugate B f x y)

/-- The conjugate of the constant `⊤` is the constant `⊥`. -/
@[simp]
theorem fenchelConjugate_top (y : F) : fenchelConjugate B (⊤ : E → EReal) y = ⊥ :=
  (fenchelConjugate_eq_bot_iff B).2 fun _ => rfl

/-- The conjugate of the constant `⊥` is the constant `⊤`. -/
@[simp]
theorem fenchelConjugate_bot (y : F) : fenchelConjugate B (⊥ : E → EReal) y = ⊤ :=
  fenchelConjugate_eq_top_of_eq_bot B (x := 0) rfl y

/-! ### The Galois connection and the biconjugate -/

/-- `f⋆ ≤ g` and `g⋆ ≤ f`, the latter for the transposed pairing, both express the Fenchel–Young
inequality for the pair `(f, g)`, so they are equivalent, with no finiteness hypothesis. -/
theorem fenchelConjugate_le_iff_fenchelConjugate_flip_le :
    fenchelConjugate B f ≤ g ↔ fenchelConjugate B.flip g ≤ f := by
  constructor
  · intro h x
    refine fenchelConjugate_le B.flip fun y => ?_
    rw [LinearMap.flip_apply]
    exact EReal.coe_sub_le_comm.1 ((sub_le_fenchelConjugate B f x y).trans (h y))
  · intro h y
    refine fenchelConjugate_le B fun x => ?_
    have hxy := (sub_le_fenchelConjugate B.flip g y x).trans (h x)
    rw [LinearMap.flip_apply] at hxy
    exact EReal.coe_sub_le_comm.1 hxy

/-- The conjugate for `B` and the conjugate for the transposed pairing `B.flip` form an antitone
Galois connection between the functions on `E` and the functions on `F`. Order reversal, the
biconjugate inequality and the triple-conjugate identity are its standard consequences. -/
theorem fenchelConjugate_galoisConnection :
    GaloisConnection (fun g : (F → EReal)ᵒᵈ => fenchelConjugate B.flip (OrderDual.ofDual g))
      (fun f : E → EReal => OrderDual.toDual (fenchelConjugate B f)) := fun _ _ =>
  (fenchelConjugate_le_iff_fenchelConjugate_flip_le B).symm

/-- The conjugate reverses the pointwise order. -/
theorem fenchelConjugate_antitone : Antitone (fenchelConjugate B) := fun _ _ h y =>
  (fenchelConjugate_galoisConnection B).monotone_u h y

/-- **The biconjugate inequality**: `f⋆⋆ ≤ f`, where the second conjugate is taken for the
transposed pairing. -/
theorem fenchelConjugate_flip_fenchelConjugate_le (f : E → EReal) :
    fenchelConjugate B.flip (fenchelConjugate B f) ≤ f :=
  (fenchelConjugate_galoisConnection B).l_u_le f

/-- The triple conjugate is the conjugate: `f⋆⋆⋆ = f⋆`. -/
theorem fenchelConjugate_fenchelConjugate_flip_fenchelConjugate (f : E → EReal) :
    fenchelConjugate B (fenchelConjugate B.flip (fenchelConjugate B f)) =
      fenchelConjugate B f :=
  OrderDual.toDual.injective ((fenchelConjugate_galoisConnection B).u_l_u_eq_u f)

/-- Every affine minorant `x ↦ B x y + c` of `f` lies below the biconjugate `f⋆⋆`: the
minorant bounds `f⋆ y` by `-c`. -/
theorem coe_add_le_fenchelConjugate_flip_fenchelConjugate {c : ℝ}
    (h : ∀ x, ((B x y + c : ℝ) : EReal) ≤ f x) (x : E) :
    ((B x y + c : ℝ) : EReal) ≤ fenchelConjugate B.flip (fenchelConjugate B f) x := by
  have hy : fenchelConjugate B f y ≤ ((-c : ℝ) : EReal) := fenchelConjugate_le B fun x' => by
    rw [EReal.coe_sub_le_comm, ← EReal.coe_sub, sub_neg_eq_add]
    exact h x'
  have hxy := sub_le_fenchelConjugate B.flip (fenchelConjugate B f) y x
  rw [LinearMap.flip_apply] at hxy
  refine le_trans ?_ hxy
  rw [← sub_neg_eq_add, EReal.coe_sub]
  exact EReal.sub_le_sub le_rfl hy

/-- Adding a real constant to a function subtracts it from the conjugate. -/
@[simp]
theorem fenchelConjugate_add_const (f : E → EReal) (r : ℝ) (y : F) :
    fenchelConjugate B (fun x => f x + (r : EReal)) y = fenchelConjugate B f y - (r : EReal) := by
  simp only [fenchelConjugate_apply]
  rw [← EReal.iSup_sub_coe]
  exact iSup_congr fun x => EReal.coe_sub_add_coe (f x) (B x y) r

/-! ### Convexity and lower semicontinuity -/

/-- The real epigraph `{(y, r) | f⋆ y ≤ r}` of a conjugate is convex: it is the intersection over
`x` of the half-spaces `{(y, r) | B x y - r ≤ f x}`, each of which is the whole space when
`f x = ⊤` and empty when `f x = ⊥`. -/
theorem convex_epigraph_fenchelConjugate (f : E → EReal) :
    Convex ℝ {p : F × ℝ | fenchelConjugate B f p.1 ≤ (p.2 : EReal)} := by
  have hset : {p : F × ℝ | fenchelConjugate B f p.1 ≤ (p.2 : EReal)} =
      ⋂ x, {p : F × ℝ | ((B x p.1 - p.2 : ℝ) : EReal) ≤ f x} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, fenchelConjugate_le_iff, EReal.coe_sub,
      EReal.coe_sub_le_comm]
  rw [hset]
  refine convex_iInter fun x => ?_
  generalize f x = z
  induction z with
  | bot =>
    simp only [le_bot_iff, EReal.coe_ne_bot, Set.ofPred_false]
    exact convex_empty
  | coe s =>
    simp only [EReal.coe_le_coe_iff]
    exact convex_halfSpace_le ((B x).comp (LinearMap.fst ℝ F ℝ) - LinearMap.snd ℝ F ℝ).isLinear s
  | top =>
    simp only [le_top, Set.ofPred_true]
    exact convex_univ

/-- A conjugate is lower semicontinuous for every topology on `F` in which each functional `B x`
is continuous, since it is a supremum of continuous or constant extended-real functions. -/
theorem lowerSemicontinuous_fenchelConjugate [TopologicalSpace F] (hB : ∀ x, Continuous (B x))
    (f : E → EReal) : LowerSemicontinuous (fenchelConjugate B f) := by
  refine lowerSemicontinuous_iSup fun x => ?_
  simpa only [sub_eq_add_neg, Function.comp_def] using EReal.lowerSemicontinuous_add.comp
    ((continuous_coe_real_ereal.comp (hB x)).prodMk (continuous_const (y := -f x)))

end LinearMap

end

end
