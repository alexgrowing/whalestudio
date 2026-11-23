import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisUnique
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_unique : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ) (N N' : Formalism.Per.Acris l → ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ N → IsGauss l ρ N' → N = N' := by
  first | exact @GlobalTheory.PMon.Gauss.isGauss_unique | exact GlobalTheory.PMon.Gauss.isGauss_unique | (intros; apply GlobalTheory.PMon.Gauss.isGauss_unique <;> assumption)
