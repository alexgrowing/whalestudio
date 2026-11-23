import Mathlib

open scoped Matrix Matrix.Norms.Frobenius

namespace GlobalTheory

theorem frobCmp_normSq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

theorem frobCmp_le {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : ‖A‖ ≤ ‖B‖ := by
  have hsq : ‖A‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    rw [frobCmp_normSq, frobCmp_normSq]
    gcongr with i _ j _
    exact h i j
  nlinarith [norm_nonneg A, norm_nonneg B]

theorem frobCmp_le_const {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i j, ‖A i j‖ ≤ ε) : ‖A‖ ≤ r * ε := by
  have hsq : ‖A‖ ^ 2 ≤ ((r : ℝ) * ε) ^ 2 := by
    rw [frobCmp_normSq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin r, ∑ _j : Fin r, ε ^ 2 := by
          gcongr with i _ j _
          exact h i j
      _ = ((r : ℝ) * ε) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have : 0 ≤ (r : ℝ) * ε := by positivity
  nlinarith [norm_nonneg A]

theorem frobenius_lower_comparison : ∀ (r : ℕ) (g n b B W H : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, a < c → n a c = 0) → (∀ a : Fin r, n a a = 1) → (∀ a c : Fin r, c < a → ‖n a c‖ ≤ δ) → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) → (∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ) → (∀ a c : Fin r, c < a → B a c = 0) → (∀ a c : Fin r, a ≤ c → W a c = 0) → (∀ a c : Fin r, a ≤ c → H a c = 0) → g * n = b → g * W = H * b + B → ∑ a, ∑ c, ‖W a c‖ ^ 2 ≤ 2 * ∑ a, ∑ c, ‖H a c‖ ^ 2 := by
  intro r g n b B W H δ hδ hrδ hn_up hn_diag hn_low hb_low hb_diag hb_up hB hW hH hgn hgW
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hδ1 : δ ≤ 1 / 100 := by nlinarith

  have hnT : n.BlockTriangular OrderDual.toDual := fun i j hij => hn_up i j (by simpa using hij)
  have hdet : n.det = 1 := by
    rw [Matrix.det_of_lowerTriangular n hnT]; simp [hn_diag]
  have hu : IsUnit n.det := by rw [hdet]; exact isUnit_one
  letI := n.invertibleOfIsUnitDet hu
  have hinvT : n⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hnT
  obtain ⟨Y, hY⟩ : ∃ Y, Y = n⁻¹ * W := ⟨_, rfl⟩
  have hYlow : ∀ a c, a ≤ c → Y a c = 0 := by
    intro a c hac
    rw [hY, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : a < k
    · rw [hinvT (by simpa using hk), zero_mul]
    · rw [hW k c (le_trans (not_lt.mp hk) hac), mul_zero]
  have hWnY : W = n * Y := by
    rw [hY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  have hg : g = b * n⁻¹ := by
    rw [← hgn, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hbY : b * Y = H * b + B := by rw [← hgW, hg, hY, Matrix.mul_assoc]

  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin r) (Fin r) ℂ, D = Matrix.diagonal (fun a => b a a) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu'⟩ : ∃ u, u = b - D := ⟨_, rfl⟩
  have hbDu : b = D + u := by rw [hu']; abel
  have hdlow : ∀ a, (0.969 : ℝ) ≤ ‖b a a‖ := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).1
    nlinarith [norm_nonneg (b a a)]
  have hdup : ∀ a, ‖b a a‖ ≤ (1.03 : ℝ) := by
    intro a
    have h1 := (abs_le.mp (hb_diag a)).2
    nlinarith [norm_nonneg (b a a)]
  have hunorm : ‖u‖ ≤ 6 / 100 := by
    have h := frobCmp_le_const u (6 * δ) (by positivity) (by
      intro a c
      rw [hu', Matrix.sub_apply, hD]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), sub_zero]; exact hb_up a c hac
      · simp; positivity
      · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), sub_zero, hb_low a c hac, norm_zero]
        positivity)
    nlinarith
  have hn1 : ‖n - 1‖ ≤ 1 / 100 := by
    have h := frobCmp_le_const (n - 1) δ hδ (by
      intro a c
      rw [Matrix.sub_apply]
      rcases lt_trichotomy a c with hac | rfl | hac
      · rw [hn_up a c hac, Matrix.one_apply_ne (ne_of_lt hac), sub_zero, norm_zero]; exact hδ
      · rw [hn_diag, Matrix.one_apply_eq, sub_self, norm_zero]; exact hδ
      · rw [Matrix.one_apply_ne (ne_of_gt hac), sub_zero]; exact hn_low a c hac)
    linarith

  have hM : D * Y = H * D + H * u - u * Y + B := by
    have e1 : D * Y = b * Y - u * Y := by rw [hbDu, Matrix.add_mul]; abel
    rw [e1, hbY, hbDu, Matrix.mul_add]; abel
  have hkey : ‖D * Y‖ ≤ ‖H * D + H * u - u * Y‖ := by
    apply frobCmp_le
    intro a c
    by_cases hca : c < a
    · rw [hM, Matrix.add_apply, hB a c hca, add_zero]
    · rw [hD, Matrix.diagonal_mul, hYlow a c (not_lt.mp hca), mul_zero, norm_zero]
      exact norm_nonneg _
  have hDY : (0.969 : ℝ) * ‖Y‖ ≤ ‖D * Y‖ := by
    have h : ‖(0.969 : ℝ) • Y‖ ≤ ‖D * Y‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.diagonal_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hdlow a) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHD : ‖H * D‖ ≤ (1.03 : ℝ) * ‖H‖ := by
    have h : ‖H * D‖ ≤ ‖(1.03 : ℝ) • H‖ := by
      apply frobCmp_le
      intro a c
      rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
        hD, Matrix.mul_diagonal, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hdup c) (norm_nonneg _)
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at h
  have hHu : ‖H * u‖ ≤ ‖H‖ * ‖u‖ := Matrix.frobenius_norm_mul H u
  have huY : ‖u * Y‖ ≤ ‖u‖ * ‖Y‖ := Matrix.frobenius_norm_mul u Y
  have htri : ‖H * D + H * u - u * Y‖ ≤ ‖H * D‖ + ‖H * u‖ + ‖u * Y‖ :=
    (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have hHn := norm_nonneg H
  have hYn := norm_nonneg Y
  have hun := norm_nonneg u
  have hY12 : ‖Y‖ ≤ 1.2 * ‖H‖ := by nlinarith
  have hWY : ‖W‖ ≤ (1.01 : ℝ) * ‖Y‖ := by
    have e : W = Y + (n - 1) * Y := by rw [hWnY, Matrix.sub_mul, Matrix.one_mul]; abel
    have h1 : ‖W‖ ≤ ‖Y‖ + ‖n - 1‖ * ‖Y‖ := by
      rw [e]; exact (norm_add_le _ _).trans (by gcongr; exact Matrix.frobenius_norm_mul _ _)
    nlinarith [norm_nonneg (n - 1)]
  have hWn := norm_nonneg W
  rw [← frobCmp_normSq, ← frobCmp_normSq]
  nlinarith

end GlobalTheory
