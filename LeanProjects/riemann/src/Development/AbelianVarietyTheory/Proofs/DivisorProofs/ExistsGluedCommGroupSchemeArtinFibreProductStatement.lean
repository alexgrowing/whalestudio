import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_commGroupScheme_artinFibreProduct : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsCommMonObj A₁ → IsCommMonObj A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∀ (Y : Over (Spec P)) (j₁ : A₁.left ⟶ Y.left) (j₂ : A₂.left ⟶ Y.left), IsPullback j₁ A₁.hom Y.hom (Spec.map f₁) → IsPullback j₂ A₂.hom Y.hom (Spec.map f₂) → Flat Y.hom → IsPushout ψ₁ ψ₂ j₁ j₂ → ∃ _ : GrpObj Y, IsCommMonObj Y ∧ IsGrpPullback A₁ Y (Spec.map f₁) j₁ ∧ IsGrpPullback A₂ Y (Spec.map f₂) j₂ := by
  first | exact @GlobalTheory.GlueGrpLaw.exists_glued_grp | exact GlobalTheory.GlueGrpLaw.exists_glued_grp | (intros; apply GlobalTheory.GlueGrpLaw.exists_glued_grp <;> assumption)
