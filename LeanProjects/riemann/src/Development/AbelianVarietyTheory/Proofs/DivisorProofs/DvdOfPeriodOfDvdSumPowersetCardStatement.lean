import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfPeriodOfDvdSumPowersetCard

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_period_of_dvd_sum_powersetCard' : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → (∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i)) → ∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l := by
  first | exact @GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | exact GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard | (intros; apply GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard <;> assumption)
