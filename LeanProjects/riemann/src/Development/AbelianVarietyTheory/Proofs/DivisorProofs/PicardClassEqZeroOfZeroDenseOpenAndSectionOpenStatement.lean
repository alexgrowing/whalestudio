import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picardClass_eq_zero_of_zero_dense_open_and_section_open : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  first | exact @GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero | exact GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero | (intros; apply GlobalTheory.PicGlue.eq_zero_of_pull_eq_zero <;> assumption)
