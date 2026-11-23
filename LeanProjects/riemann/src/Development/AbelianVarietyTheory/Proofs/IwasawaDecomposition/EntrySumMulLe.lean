import Mathlib

namespace GlobalTheory.EntrySumMulBound

theorem entrySum_mul_le :
    (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → ℝ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) ↦ ∑ i : n, ∑ j : n, ‖M i j‖); ∀ {n : Type} [inst : Fintype n] (A B : Matrix n n ℂ), d1 (A * B) ≤ d1 A * d1 B) := by
  intro d1 n inst A B
  show ∑ i : n, ∑ j : n, ‖(A * B) i j‖ ≤ (∑ i : n, ∑ k : n, ‖A i k‖) * (∑ l : n, ∑ j : n, ‖B l j‖)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : n, ‖(A * B) i j‖ ≤ ∑ j : n, ∑ k : n, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : n, ‖A i k‖ * ∑ j : n, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : n, ‖A i k‖ * ∑ l : n, ∑ j : n, ‖B l j‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : n, ‖B l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : n, ‖A i k‖) * ∑ l : n, ∑ j : n, ‖B l j‖ := (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntrySumMulBound
