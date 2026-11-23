import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_theorem_pic_class_over_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  first | exact @GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | exact GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | (intros; apply GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens <;> assumption)
