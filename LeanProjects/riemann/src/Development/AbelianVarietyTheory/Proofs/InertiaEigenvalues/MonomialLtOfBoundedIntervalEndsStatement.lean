import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonomialLtOfBoundedIntervalEnds
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_logConvex_in_radius : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_logConvex | exact GlobalTheory.PMon.Gauss.gC_logConvex | (intros; apply GlobalTheory.PMon.Gauss.gC_logConvex <;> assumption)
