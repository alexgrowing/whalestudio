import Mathlib

namespace GlobalTheory.CompanionTheory.ExpSums

open Matrix in

theorem vandermonde_separation (r : ℕ) (α : Fin r → ℂ) (hα : Function.Injective α) :
    ∃ C : ℝ, ∀ (c : Fin r → ℂ) (i : Fin r),
      ‖c i‖ ≤ C * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ, V = Matrix.vandermonde α := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hα
  refine ⟨∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖, ?_⟩
  intro c i
  have hsum : ∀ s : Fin r, Matrix.vecMul c V s = ∑ k, c k * α k ^ (s : ℕ) := by
    intro s
    simp [Matrix.vecMul, dotProduct, hV, Matrix.vandermonde_apply]
  have hc : c = Matrix.vecMul (Matrix.vecMul c V) V⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  have hC : ∀ s : Fin r, ‖V⁻¹ s i‖ ≤ ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ := fun s =>
    (Finset.single_le_sum (f := fun j => ‖V⁻¹ s j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun s => ∑ j, ‖V⁻¹ s j‖)
      (fun s _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ s))
  calc ‖c i‖ = ‖Matrix.vecMul (Matrix.vecMul c V) V⁻¹ i‖ := by rw [← hc]
    _ = ‖∑ s, Matrix.vecMul c V s * V⁻¹ s i‖ := rfl
    _ ≤ ∑ s, ‖Matrix.vecMul c V s * V⁻¹ s i‖ := norm_sum_le _ _
    _ = ∑ s, ‖Matrix.vecMul c V s‖ * ‖V⁻¹ s i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ s, ‖Matrix.vecMul c V s‖ * ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)
    _ = (∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖) * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by rw [hsum]

end GlobalTheory.CompanionTheory.ExpSums
