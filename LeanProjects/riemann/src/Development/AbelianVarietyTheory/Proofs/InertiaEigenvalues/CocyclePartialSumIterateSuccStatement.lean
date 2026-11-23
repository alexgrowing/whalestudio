import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocyclePartialSumIterateSucc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_frobenius_eq_pow_root_radius : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ x : Formalism.Per.Acris l, gC l ρ (φc l x) = gC l (ρ ^ ((1 : ℝ) / l)) x ^ l := by
  first | exact @GlobalTheory.PMon.Gauss.gC_phi | exact GlobalTheory.PMon.Gauss.gC_phi | (intros; apply GlobalTheory.PMon.Gauss.gC_phi <;> assumption)
