import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogConcaveMultiplicativeGrowthBound
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_concave_multiplicative_growth_bound : ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  first | exact @GlobalTheory.first_term_le_of_logConcave_blocks | exact GlobalTheory.first_term_le_of_logConcave_blocks | (intros; apply GlobalTheory.first_term_le_of_logConcave_blocks <;> assumption)
