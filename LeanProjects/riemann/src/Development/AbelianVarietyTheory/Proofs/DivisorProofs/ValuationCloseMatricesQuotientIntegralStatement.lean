import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationCloseMatricesQuotientIntegral
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_close_matrices_quotient_integral : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) →
    ∀ {N : ℕ} (Γa Γb Aa Ab : Matrix (Fin N) (Fin N) K), (∀ i k, w (Γa i k) ≤ 1) → (∀ i k, w (Γb i k) ≤ 1) →
    w Γa.det = 1 → (∀ i k, w (Aa i k - Γa i k) < 1) → (∀ i k, w (Ab i k - Γb i k) < 1) →
    w Aa.det = 1 ∧ ∀ i k, w ((Aa⁻¹ * Ab) i k - (Γa⁻¹ * Γb) i k) < 1 := by
  first | exact @GlobalTheory.inv_mul_congr_of_entries_congr_of_det_unit | exact GlobalTheory.inv_mul_congr_of_entries_congr_of_det_unit | (intros; apply GlobalTheory.inv_mul_congr_of_entries_congr_of_det_unit <;> assumption)
