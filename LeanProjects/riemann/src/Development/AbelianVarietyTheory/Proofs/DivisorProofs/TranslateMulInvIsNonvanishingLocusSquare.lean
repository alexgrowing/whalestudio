import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareLocus

set_option maxHeartbeats 1000000 in

theorem translate_mul_inv_isLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  intro S _ A _ hA c V hV T a h
  have hsq := GlobalTheory.T.theorem_of_square_cechPicard_translates S A hA c (A ⊗ T) (fst A T) (snd A T ≫ a)
  have e1 : (snd A T ≫ a)⁻¹ = snd A T ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
  have e2 : (1 : A ⊗ T ⟶ A) = snd A T ≫ (1 : T ⟶ A) := (MonObj.comp_one _).symm
  have h0 : pull (snd A T ≫ a).left c + pull (snd A T ≫ a)⁻¹.left c
      - 2 • pull (1 : A ⊗ T ⟶ A).left c = 0 := by
    rw [e1, e2, Over.comp_left, Over.comp_left, Over.comp_left, pull_comp, pull_comp, pull_comp,
      ← map_nsmul, ← map_add, ← map_sub, h, map_zero]
  have h2 : pull (fst A T * (snd A T ≫ a)).left c + pull (fst A T * (snd A T ≫ a)⁻¹).left c
      = 2 • pull (fst A T).left c := by
    rw [hsq, ← sub_eq_zero, ← h0]
    abel
  have hl := (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)).left c V hV).add
    (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)⁻¹).left c V hV)
  rw [h2] at hl
  exact hl

end GlobalTheory.SquareLocus
