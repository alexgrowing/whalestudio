import Mathlib

namespace GlobalTheory.LatticeFactsFlagMeasures

theorem main : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ), (∀ (i j : Fin n), ‖A i j‖ ≤ a) → (∀ (i j : Fin n), ‖B i j‖ ≤ b) → ∀ (i j : Fin n), ‖(A * B) i j‖ ≤ (↑n : ℝ) * (a * b) := by
  intro n A B a b hA hB i j
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        have ha : 0 ≤ a := le_trans (norm_nonneg _) (hA i k)
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
    _ = (n : ℝ) * (a * b) := by simp

end GlobalTheory.LatticeFactsFlagMeasures
