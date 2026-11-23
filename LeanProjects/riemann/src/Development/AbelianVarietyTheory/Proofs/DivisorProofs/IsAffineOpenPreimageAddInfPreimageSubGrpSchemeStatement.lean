import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens), IsAffineOpen V → ∀ (T : Over (Sp R)) [IsAffine T.left] (a : T ⟶ A), IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | exact GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | (intros; apply GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub <;> assumption)
