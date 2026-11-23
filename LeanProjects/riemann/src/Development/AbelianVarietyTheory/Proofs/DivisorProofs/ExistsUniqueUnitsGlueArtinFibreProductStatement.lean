import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueUnitsGlueArtinFibreProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_units_glue_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y : Over (Spec P)) (Y₁ : Over (Spec R₁)) (Y₂ : Over (Spec R₂)) (Y₀ : Over (Spec R₀)) (j₁ : Y₁.left ⟶ Y.left) (j₂ : Y₂.left ⟶ Y.left) (i₁ : Y₀.left ⟶ Y₁.left) (i₂ : Y₀.left ⟶ Y₂.left), Flat Y.hom → IsPullback j₁ Y₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ Y₂.hom Y.hom (Spec.map f₂) → IsPullback i₁ Y₀.hom Y₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ Y₂.hom = Y₀.hom ≫ Spec.map g₂ → (∀ (U : Y.left.Opens) (a₁ : Γ(Y₁.left, j₁ ⁻¹ᵁ U)ˣ) (a₂ : Γ(Y₂.left, j₂ ⁻¹ᵁ U)ˣ), (∀ x : Y₀.left, i₁ x ∈ j₁ ⁻¹ᵁ U → gm i₁ x (j₁ ⁻¹ᵁ U) a₁ = gm i₂ x (j₂ ⁻¹ᵁ U) a₂) → ∃ d : Γ(Y.left, U)ˣ, pullU j₁ U d = a₁ ∧ pullU j₂ U d = a₂) ∧ (∀ (U : Y.left.Opens) (d d' : Γ(Y.left, U)ˣ), pullU j₁ U d = pullU j₁ U d' → pullU j₂ U d = pullU j₂ U d' → d = d') := by
  first | exact @GlobalTheory.PinchUnits.main | exact GlobalTheory.PinchUnits.main | (intros; apply GlobalTheory.PinchUnits.main <;> assumption)
