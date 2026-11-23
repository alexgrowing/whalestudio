import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfSumMulPowMemOfValuationZpow
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_sum_mul_pow_mem_of_valuation_zpow : ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω) (N : ℕ) (π ℓ : Ω) (c : ℕ → Ω), 0 < N → ℓ ≠ 0 → A.valuation ℓ < 1 → A.valuation π ^ N = A.valuation ℓ → (∀ i < N, c i ≠ 0 → ∃ k : ℤ, A.valuation (c i) = A.valuation ℓ ^ k) → (∑ i ∈ Finset.range N, c i * π ^ i) ∈ A → ∀ i < N, c i ∈ A := by
  first | exact @GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | exact GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow | (intros; apply GlobalTheory.mem_of_sum_mul_pow_mem_of_valuation_zpow <;> assumption)
