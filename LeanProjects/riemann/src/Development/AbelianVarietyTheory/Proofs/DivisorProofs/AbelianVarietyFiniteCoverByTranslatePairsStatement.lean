import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairs
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_finite_cover_by_translate_pairs : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  first | exact @GlobalTheory.AbCover.cover | exact GlobalTheory.AbCover.cover | (intros; apply GlobalTheory.AbCover.cover <;> assumption)
