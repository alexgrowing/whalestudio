import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombination
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧ ∀ x : Fl l, ‖sh x‖ < 1 → HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  first | exact @GlobalTheory.PSer.exists_coef_hasSum_lam | exact GlobalTheory.PSer.exists_coef_hasSum_lam | (intros; apply GlobalTheory.PSer.exists_coef_hasSum_lam <;> assumption)
