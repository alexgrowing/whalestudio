import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem isPullback_whiskerLeft_snd_left {S : Scheme.{0}} (A : Over S) {B' B : Over S} (j : B' ⟶ B) :
    IsPullback (A ◁ j).left (snd A B').left (snd A B).left j.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst A.hom B.hom) (v₁₃ := A.hom) (h₂₂ := B.hom)
    ?_ ?_ (IsPullback.of_hasPullback A.hom B.hom)
  · have hw : j.left ≫ B.hom = B'.hom := Over.w j
    rw [Over.whiskerLeft_left_fst, hw]
    exact IsPullback.of_hasPullback A.hom B'.hom
  · simp

theorem isOpenImmersion_whiskerLeft_left_and_range {S : Scheme.{0}} (A : Over S) {B' B : Over S}
    (j : B' ⟶ B) [IsOpenImmersion j.left] :
    IsOpenImmersion (A ◁ j).left ∧
      Set.range (A ◁ j).left = (snd A B).left ⁻¹' Set.range j.left := by
  have h := isPullback_whiskerLeft_snd_left A j
  refine ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) h.flip
    inferInstance, ?_⟩
  simpa [Set.image_univ] using Scheme.image_preimage_eq_of_isPullback h.flip Set.univ

end GlobalTheory.DualCon
