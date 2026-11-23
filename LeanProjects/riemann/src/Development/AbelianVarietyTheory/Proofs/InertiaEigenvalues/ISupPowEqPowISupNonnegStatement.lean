import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonneg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (c ρ₁ ρ₂ : ℝ) (k : ℤ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ < 1 → 0 < c → (∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ x = c * ρ ^ k) → ∃ (y : Formalism.Per.Fl l) (j : ℕ), 0 ≤ k + j ∧ ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ j * x - (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y) < ρ ^ j * gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.lead_target | exact GlobalTheory.PMon.Gauss.lead_target | (intros; apply GlobalTheory.PMon.Gauss.lead_target <;> assumption)
