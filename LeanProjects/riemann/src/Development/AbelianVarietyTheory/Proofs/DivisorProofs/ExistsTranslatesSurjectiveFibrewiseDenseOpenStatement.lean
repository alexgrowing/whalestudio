import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesSurjectiveFibrewiseDenseOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translates_surjective_fibrewise_dense_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (B : Over S) (j : B ⟶ A), (∀ b, j.left b ∈ V) → Smooth B.hom → GeometricallyIntegral B.hom → Surjective ((((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((fst (A ⊗ A) B ≫ fst A A) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)).left ⁻¹ᵁ V ⊓ ((snd (A ⊗ A) B ≫ j) * (fst (A ⊗ A) B ≫ snd A A)⁻¹).left ⁻¹ᵁ V).ι ≫ (fst (A ⊗ A) B ≫ fst A A).left) := by
  first | exact @GlobalTheory.TranslateSurj.exists_translates_surjective | exact GlobalTheory.TranslateSurj.exists_translates_surjective | (intros; apply GlobalTheory.TranslateSurj.exists_translates_surjective <;> assumption)
