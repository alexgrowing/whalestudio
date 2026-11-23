import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def IsImg {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (z : (Σ k, ι' k) → ℂ) (w : (Σ k, ι k) → ℂ) : Prop :=
  ∀ z₁, SameOrbit z₁ z → ∀ F' F, M'.IsFrame F' → M.IsFrame F →
    M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z₁ ∘ Cv.v)) →
    ∀ h, M'.IsFlagOf F' z₁ h → ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) ∧
      M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z₁) τ * h τ

theorem IsImg.orbit {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {Cv : FlagCover M' M}
    {z z₁ : (Σ k, ι' k) → ℂ} {w w₁ : (Σ k, ι k) → ℂ} (h : IsImg Cv z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : IsImg Cv z₁ w₁ := by
  intro z₂ h2 F' F hF' hF hg' hg hh hfl
  obtain ⟨z₀, a, b, c⟩ := h z₂ (Cj.sameOrbit_trans h2 hz) F' F hF' hF hg' hg hh hfl
  exact ⟨z₀, Cj.sameOrbit_trans a (Cj.sameOrbit_symm hw), b, c⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
