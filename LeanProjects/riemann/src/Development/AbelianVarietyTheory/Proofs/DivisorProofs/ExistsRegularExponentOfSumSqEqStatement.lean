import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularExponentOfSumSqEq

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_exponent_of_sum_sq_eq' : ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d → (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) → ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d → (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) → ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by
  first | exact @GlobalTheory.exists_regular_exponent_of_sum_sq_eq | exact GlobalTheory.exists_regular_exponent_of_sum_sq_eq | (intros; apply GlobalTheory.exists_regular_exponent_of_sum_sq_eq <;> assumption)
