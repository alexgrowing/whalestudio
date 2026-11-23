import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_opens_preimage_eq_of_sqZero_aug (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
    (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀)
    (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (W : X₁.Opens) :
    ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  have hcomp : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun r ↦ q.commutes r
  have hsp : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  let i : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀))
    (by rw [Category.id_comp, Category.assoc, hsp, Category.comp_id])
  have hi1 : i ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hi2 : i ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (i ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hi1, hsp]; exact IsPullback.id_horiz s₀
  have hsq : IsPullback i s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hi2 hp
  have hsurj : Function.Surjective (q : R₁ →+* R₀) := fun r ↦ ⟨algebraMap R₀ R₁ r, q.commutes r⟩
  have hI : (RingHom.ker (q : R₁ →+* R₀)) ^ 2 = 0 := by
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro y hy y' hy'
    exact (Ideal.mem_bot).2 (hq y y' (RingHom.mem_ker.1 hy) (RingHom.mem_ker.1 hy'))
  have hisurj : Surjective i := surjective_of_isPullback_sqZero hI hsurj rfl hsq
  have key : ∀ x : X₁, i.base (pr.base x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hisurj.surj x
    have h : pr.base (i.base y) = y := by rw [← Scheme.Hom.comp_apply, hi1]; rfl
    rw [h]
  refine ⟨i ⁻¹ᵁ W, ?_⟩
  ext x
  change i.base (pr.base x) ∈ W ↔ x ∈ W
  rw [key]

end GlobalTheory.LiftSys
