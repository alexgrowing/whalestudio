import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRpowOfFibreCardLe
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_rpow_of_fibre_card_le' : ∀ (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ) (h : ι → ℝ), 1 < b → (n : ℝ) < t → (∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹) → (∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) → (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) → Summable fun q => h q ^ t := by
  first | exact @GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | exact GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | (intros; apply GlobalTheory.SummCount.summable_rpow_of_fibre_card_le <;> assumption)
