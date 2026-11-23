import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationRelativeDimZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelProductClosedImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeDimClosedImmersionProductStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.DomThird

theorem exists_normal_dominating : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ B₂ : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B), f₁.relDim = 0 → f₂.relDim = 0 → ∃ (B₃ : GlobalTheory.Vert.Model O) (h₁ : GlobalTheory.Vert.Model.Hom B₃ B₁) (h₂ : GlobalTheory.Vert.Model.Hom B₃ B₂), GlobalTheory.IsNormalScheme B₃.X ∧ h₁.relDim = 0 ∧ h₂.relDim = 0 ∧ h₁.f ≫ f₁.f = h₂.f ≫ f₂.f := by
  intro O _ _ _ p _ _ _ B B₁ B₂ f₁ f₂ e₁ e₂
  obtain ⟨Z, h₁, h₂, w, hc⟩ := GlobalTheory.T.model_product_closed_immersion O B B₁ B₂ f₁ f₂
  have hd := GlobalTheory.T.relative_dim_closed_immersion_product O B B₁ B₂ Z f₁ f₂ h₁ h₂ w hc
  obtain ⟨Z', n, hn, n0⟩ := GlobalTheory.T.exists_normalization_relative_dim_zero O Z
  have l₁ := f₁.relDim_le
  have l₂ := f₂.relDim_le
  have l₃ := h₁.relDim_le
  have l₄ := n.relDim_le
  simp only [GlobalTheory.Vert.Model.Hom.relDim] at e₁ e₂ n0 ⊢
  refine ⟨Z', n.comp h₁, n.comp h₂, hn, ?_, ?_, ?_⟩
  · change Z'.relDim - B₁.relDim = 0
    omega
  · change Z'.relDim - B₂.relDim = 0
    omega
  · change (n.f ≫ h₁.f) ≫ f₁.f = (n.f ≫ h₂.f) ≫ f₂.f
    rw [Category.assoc, Category.assoc, w]

end GlobalTheory.DomThird
