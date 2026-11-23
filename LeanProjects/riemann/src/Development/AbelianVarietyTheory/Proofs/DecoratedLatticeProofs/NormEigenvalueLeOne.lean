import Mathlib

namespace GlobalTheory.EigenvalueNormBound

theorem pow_mulVec_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (μ : ℂ)
    (h : Matrix.mulVec M v = μ • v) (k : ℕ) : Matrix.mulVec (M ^ k) v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem norm_eigenvalue_le_one : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (C : ℝ),
    (∀ (k : ℕ) (i j : Fin n), ‖(M ^ k) i j‖ ≤ C) → ∀ (v : Fin n → ℂ), v ≠ (0 : Fin n → ℂ) →
    ∀ (μ : ℂ), Matrix.mulVec M v = μ • v → ‖μ‖ ≤ (1 : ℝ) := by
  intro n M C hC v hv μ hμ
  by_contra hlt
  rw [not_le] at hlt

  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi

  have bound : ∀ k : ℕ, ‖μ‖ ^ k * ‖v i‖ ≤ C * ∑ j, ‖v j‖ := by
    intro k
    have e := congrFun (pow_mulVec_eq M v μ hμ k) i
    have hk : ‖μ‖ ^ k * ‖v i‖ = ‖∑ j, (M ^ k) i j * v j‖ := by
      have : (M ^ k).mulVec v i = ∑ j, (M ^ k) i j * v j := by simp [Matrix.mulVec, dotProduct]
      rw [← this, e, Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    rw [hk]
    calc ‖∑ j, (M ^ k) i j * v j‖ ≤ ∑ j, ‖(M ^ k) i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖(M ^ k) i j‖ * ‖v j‖ := by simp only [norm_mul]
      _ ≤ ∑ j, C * ‖v j‖ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC k i j) (norm_nonneg _)
      _ = C * ∑ j, ‖v j‖ := by rw [Finset.mul_sum]

  have htend : Filter.Tendsto (fun k : ℕ => ‖μ‖ ^ k * ‖v i‖) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_mul_const hvi (tendsto_pow_atTop_atTop_of_one_lt hlt)
  obtain ⟨k, hk⟩ := (htend.eventually_gt_atTop (C * ∑ j, ‖v j‖)).exists
  exact absurd (bound k) (not_le.mpr hk)

end GlobalTheory.EigenvalueNormBound
