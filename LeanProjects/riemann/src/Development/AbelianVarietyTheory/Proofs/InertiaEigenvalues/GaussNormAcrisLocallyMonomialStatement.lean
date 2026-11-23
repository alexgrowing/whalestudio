import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_locally_monomial : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧ ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧ ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧ ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_monomial_near | exact GlobalTheory.PMon.Gauss.gC_monomial_near | (intros; apply GlobalTheory.PMon.Gauss.gC_monomial_near <;> assumption)
