import Mathlib

namespace GlobalTheory

open Matrix

theorem ultra_matrix_mul_entry_le {E : Type} [NormedField E] [IsUltrametricDist E] {n : Type} [Fintype n]
    [DecidableEq n] (A B : Matrix n n E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

theorem matrix_one_add_pow_sub_entry_le :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) →
      ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  intro E _ _ n _ _ Y t ht0 ht1 hY m
  induction m with
  | zero => intro i j; simp; positivity
  | succ m ih =>
    have key : (1 + Y) ^ (m + 1) - 1 - ((m + 1 : ℕ) : E) • Y
        = ((1 + Y) ^ m - 1 - (m : E) • Y) + ((1 + Y) ^ m - 1 - (m : E) • Y) * Y
          + (m : E) • (Y * Y) := by
      rw [pow_succ]
      push_cast
      simp only [mul_add, add_mul, mul_one, one_mul, sub_mul, smul_mul_assoc, add_smul, one_smul]
      abel
    intro i j
    rw [key]
    have h1 := ih i j
    have h2 : ‖(((1 + Y) ^ m - 1 - (m : E) • Y) * Y) i j‖ ≤ t ^ 2 := by
      have := ultra_matrix_mul_entry_le _ Y (t ^ 2) t (by positivity) ht0 ih hY i j
      calc _ ≤ t ^ 2 * t := this
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
        _ = t ^ 2 := mul_one _
    have h3 : ‖((m : E) • (Y * Y)) i j‖ ≤ t ^ 2 := by
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
      have := ultra_matrix_mul_entry_le Y Y t t ht0 ht0 hY hY i j
      calc ‖(m : E)‖ * ‖(Y * Y) i j‖ ≤ 1 * (t * t) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one E m) this (norm_nonneg _) zero_le_one
        _ = t ^ 2 := by ring
    rw [Matrix.add_apply, Matrix.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)

end GlobalTheory
