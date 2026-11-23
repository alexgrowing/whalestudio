import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommRingCatIsPullbackFlatBaseChangeSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commRingCat_isPullback_flat_baseChange_surjective : ∀ (P C₁ C₂ C₀ E E₁ E₂ E₀ : CommRingCat.{0}) (p₁ : P ⟶ C₁) (p₂ : P ⟶ C₂) (q₁ : C₁ ⟶ C₀) (q₂ : C₂ ⟶ C₀), IsPullback p₁ p₂ q₁ q₂ → Function.Surjective q₂.hom → ∀ (g : P ⟶ E) (g₁ : C₁ ⟶ E₁) (g₂ : C₂ ⟶ E₂) (g₀ : C₀ ⟶ E₀) (i₁ : E ⟶ E₁) (i₂ : E ⟶ E₂) (r₁ : E₁ ⟶ E₀) (r₂ : E₂ ⟶ E₀), g.hom.Flat → IsPushout g p₁ i₁ g₁ → IsPushout g p₂ i₂ g₂ → IsPushout g₂ q₂ r₂ g₀ → i₁ ≫ r₁ = i₂ ≫ r₂ → g₁ ≫ r₁ = q₁ ≫ g₀ → IsPullback i₁ i₂ r₁ r₂ := by
  first | exact @GlobalTheory.MilFlat.isPullback_of_flat | exact GlobalTheory.MilFlat.isPullback_of_flat | (intros; apply GlobalTheory.MilFlat.isPullback_of_flat <;> assumption)
