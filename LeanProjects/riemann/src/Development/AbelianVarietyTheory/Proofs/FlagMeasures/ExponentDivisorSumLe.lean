import Mathlib

open scoped BigOperators

namespace GlobalTheory

private lemma exponent_product_le_G_div_N_mul_rpow (f r : ℕ) (G N H Q l d : ℝ) (hG : 1 ≤ G) (hN : 1 ≤ N)
    (hGH : G ≤ H) (hNH : N ≤ H) (hQ : 0 ≤ Q) (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d)
    (hdG : d ≤ G) :
    (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
        (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) ≤
      G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) := by
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0
  have hGdG : G / d ≤ G := div_le_self (by linarith) hd

  have h1 : (G / d) ^ (l + 3) ≤ G * H ^ (l + 2) := by
    rw [show l + 3 = 1 + (l + 2) by ring, Real.rpow_add hGd0, Real.rpow_one]
    exact mul_le_mul hGdG (Real.rpow_le_rpow hGd0.le (hGdG.trans hGH) (by linarith))
      (Real.rpow_nonneg hGd0.le _) (by linarith)

  have h2 : N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r + 2) := by
    have hN2 : N ^ (2 * r) ≤ H ^ (2 * r) := pow_le_pow_left₀ hN0.le hNH _
    calc N ^ (2 * r) * N * (Q * 9 ^ f) ≤ H ^ (2 * r) * H * H :=
          mul_le_mul (mul_le_mul hN2 hNH hN0.le (pow_nonneg hH0.le _)) hQH
            (mul_nonneg hQ (by positivity)) (mul_nonneg (pow_nonneg hH0.le _) hH0.le)
      _ = H ^ (2 * r + 2) := by ring
  have h3 : G ^ r ≤ H ^ r := pow_le_pow_left₀ (by linarith) hGH r

  have hE : H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) =
      H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r * H ^ (9 + 9 * r + 16 * r ^ 2) := by
    rw [← Real.rpow_natCast H (2 * r + 2), ← Real.rpow_natCast H r,
      ← Real.rpow_natCast H (9 + 9 * r + 16 * r ^ 2), ← Real.rpow_add hH0, ← Real.rpow_add hH0,
      ← Real.rpow_add hH0, ← Real.rpow_add hH0]
    congr 1
    push_cast
    ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hN0, hE]
  have hP : 0 ≤ H ^ (11 + 3 * l) := Real.rpow_nonneg hH0.le _
  have hM : 0 ≤ N ^ (2 * r) * N * (Q * 9 ^ f) :=
    mul_nonneg (mul_nonneg (pow_nonneg hN0.le _) hN0.le) (mul_nonneg hQ (by positivity))
  have hA : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hH0.le _)) hP
  have hR : 0 ≤ G ^ r := pow_nonneg (by linarith) _
  have hS : 0 ≤ H ^ (9 + 9 * r + 16 * r ^ 2) := pow_nonneg hH0.le _
  have hAM : 0 ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) :=
    mul_nonneg hA (pow_nonneg hH0.le _)
  calc (G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)) * N
        = (G / d) ^ (l + 3) * H ^ (11 + 3 * l) * (N ^ (2 * r) * N * (Q * 9 ^ f)) * G ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) := by ring
    _ ≤ G * H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h1 hP) h2 hM hA) h3 hR hAM) hS
    _ = G * (H ^ (l + 2) * H ^ (11 + 3 * l) * H ^ (2 * r + 2) * H ^ r *
            H ^ (9 + 9 * r + 16 * r ^ 2)) := by ring

theorem exponent_term (k f r : ℕ) (G N H a Q l d : ℝ) (hk : 1 ≤ k)
    (hG : 1 ≤ G) (hN : 1 ≤ N) (hGH : G ≤ H) (hNH : N ≤ H) (ha : 0 ≤ a) (hQ : 0 ≤ Q)
    (hQH : Q * 9 ^ f ≤ H) (hl : 0 ≤ l) (hd : 1 ≤ d) (hdG : d ≤ G) :
    (d / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * l)) *
        ((G / d) ^ ((k : ℝ) + (1 + l) + 1) *
          (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤
      H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hN0 : 0 < N := by linarith
  have hd0 : 0 < d := by linarith
  have hGd0 : 0 < G / d := div_pos (by linarith) hd0

  have hexp : ((m + 1 : ℕ) : ℝ) + (1 + l) + 1 = (m : ℝ) + (l + 3) := by push_cast; ring
  rw [hexp, Real.rpow_add hGd0, Real.rpow_natCast, Nat.add_sub_cancel, pow_succ]
  have hdm : (d / N) ^ m * (G / d) ^ m = (G / N) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hB := exponent_product_le_G_div_N_mul_rpow f r G N H Q l d hG hN hGH hNH hQ hQH hl hd hdG
  have hX : 0 ≤ a * (G / N) ^ m := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)
  calc (d / N) ^ m * a * (Q * H ^ (11 + 3 * l)) *
          ((G / d) ^ m * (G / d) ^ (l + 3) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2)))
        = a * ((d / N) ^ m * (G / d) ^ m) * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by ring
    _ = a * (G / N) ^ m * ((G / d) ^ (l + 3) * (Q * H ^ (11 + 3 * l)) *
            (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) := by rw [hdm]
    _ ≤ a * (G / N) ^ m * (G / N * H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB hX
    _ = H ^ (24 + 4 * l + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * ((G / N) ^ m * (G / N))) := by
          ring

theorem exponent_sum_le :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  intro k f r G N H a Q C hk hr hf hlog hG hN hGH hNH ha hQ hQH hC
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl0 : 0 ≤ Real.logb 2 (f : ℝ) := Real.logb_nonneg one_lt_two hf1
  have h2f : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.logb 2 f := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  have hX : 0 ≤ a * (G / N) ^ k := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)

  refine le_trans (Finset.sum_le_sum (g := fun _ =>
    H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k)) ?_) ?_
  · intro de hde
    rw [Finset.mem_Icc] at hde
    have hd1 : (1 : ℝ) ≤ de := by exact_mod_cast hde.1
    have hdG : (de : ℝ) ≤ G := le_trans (Nat.cast_le.mpr hde.2) (Nat.floor_le (by linarith))
    simp only [h2f]
    exact exponent_term k f r G N H a Q (Real.logb 2 f) de hk hG hN hGH hNH ha hQ hQH
      hl0 hd1 hdG
  ·
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfl : (⌊G⌋₊ : ℝ) ≤ H := (Nat.floor_le (by linarith)).trans hGH
    have hsq : Real.sqrt r ≤ r := by
      have h0 := Real.sqrt_nonneg (r : ℝ)
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith)
      nlinarith
    have hlog2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 (f : ℝ) ≤ 7 / 4 * r := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by linarith)
        (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith)]
    have hexp : 1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) ≤
        C * (r : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (r : ℝ))]
    have hE0 : 0 ≤ H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) :=
      Real.rpow_nonneg hH0.le _
    calc (⌊G⌋₊ : ℝ) * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k))
        ≤ H * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k)) := mul_le_mul_of_nonneg_right hfl (mul_nonneg hE0 hX)
      _ = H ^ (1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) *
            (a * (G / N) ^ k) := by rw [Real.rpow_add hH0 1, Real.rpow_one]; ring
      _ ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hX

end GlobalTheory
