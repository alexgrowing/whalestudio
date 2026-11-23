import Mathlib

open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem exm_alg (S Ifull R Lf Bt Tp K D Sg : ℂ) (y : ℝ) (hy : 0 < y)
    (hS : S = (1 / (2 * Real.pi) : ℂ) * Ifull)
    (hrect : Bt - Tp + I * R - I * Lf = 2 * Real.pi * I * (K * y + D - Sg)) :
    S / y - K - D / y + Sg / y =
      (1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp)) := by
  subst hS
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : (Ifull - R) + Lf + I * (Bt - Tp) =
      Ifull - 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg) := by
    linear_combination I * hrect + (-R + Lf + 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg)) * I_sq
  rw [key]
  field_simp
  ring

theorem exm_norm (Ifull R Lf Bt Tp : ℂ) (y a b c d : ℝ) (hy : 0 < y)
    (ha : ‖Ifull - R‖ ≤ a) (hb : ‖Lf‖ ≤ b) (hc : ‖Bt‖ ≤ c) (hd : ‖Tp‖ ≤ d) :
    ‖(1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp))‖ ≤
      1 / (2 * Real.pi * y) * (a + b + (c + d)) := by
  have hpos : 0 < 2 * Real.pi * y := mul_pos (mul_pos two_pos Real.pi_pos) hy
  have hk : (1 / (2 * Real.pi * y) : ℂ) = ((1 / (2 * Real.pi * y) : ℝ) : ℂ) := by
    norm_cast
  rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 hpos).le]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.2 hpos).le
  have h1 := norm_add_le (Ifull - R) Lf
  have h2 : ‖I * (Bt - Tp)‖ = ‖Bt - Tp‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h3 := norm_sub_le Bt Tp
  have h4 := norm_add_le (Ifull - R + Lf) (I * (Bt - Tp))
  linarith

theorem exm_log_le (M T u : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (hu0 : 0 ≤ u) (hu : u ≤ T + 1) :
    Real.log (M * (u + 2)) ≤ 2 * Real.log (M * T) := by
  have hM0 : 0 ≤ M := by linarith
  have hpos : 0 < M * (u + 2) := mul_pos (by linarith) (by linarith)
  have h3 : T + 3 ≤ M * T ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg T),
      mul_nonneg (sub_nonneg.2 hT) (by linarith : (0:ℝ) ≤ T)]
  have h4 : M * (u + 2) ≤ M * (T + 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have h5 : M * (T + 3) ≤ M * (M * T ^ 2) := mul_le_mul_of_nonneg_left h3 hM0
  have h2 : M * (u + 2) ≤ (M * T) ^ 2 := by nlinarith
  calc Real.log (M * (u + 2)) ≤ Real.log ((M * T) ^ 2) := Real.log_le_log hpos h2
    _ = 2 * Real.log (M * T) := by rw [Real.log_pow]; push_cast; ring

theorem exm_log_ge_one (M T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log (M * T) := by
  have h6 : 6 ≤ M * T := by nlinarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (M * T) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

theorem exm_N_le (κ C₁ C₂ M T δ : ℝ) (hκ : 0 < κ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hM : 3 ≤ M) (hT : 2 ≤ T)
    (_hδ0 : 0 < δ) (hδ : κ / (C₁ * (T + 1) * Real.log (M * (T + 2))) ≤ δ) :
    C₂ * (2 * Real.log (M * T)) / δ ≤ 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by
  have hL : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hL' : Real.log (M * (T + 2)) ≤ 2 * Real.log (M * T) :=
    exm_log_le M T T hM hT (by linarith) (by linarith)
  have hL'1 : 1 ≤ Real.log (M * (T + 2)) := exm_log_ge_one M (T + 2) hM (by linarith)
  have hA : 0 < C₁ * (T + 1) * Real.log (M * (T + 2)) :=
    mul_pos (mul_pos hC₁ (by linarith)) (by linarith)
  have hinv : 1 / δ ≤ C₁ * (T + 1) * Real.log (M * (T + 2)) / κ := by
    have := one_div_le_one_div_of_le (div_pos hκ hA) hδ
    rwa [one_div_div] at this
  have hP : 0 ≤ C₁ * C₂ * Real.log (M * T) := mul_nonneg (mul_nonneg hC₁.le hC₂.le) (by linarith)
  have e1 : (T + 1) * Real.log (M * (T + 2)) ≤ (T + 1) * (2 * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left hL' (by linarith)
  have e2 : (T + 1) * (2 * Real.log (M * T)) ≤ 3 * T * Real.log (M * T) := by
    nlinarith [mul_le_mul_of_nonneg_right hT (by linarith : (0:ℝ) ≤ Real.log (M * T))]
  have hnum : 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) ≤
      2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left (e1.trans e2) (by linarith)
  calc C₂ * (2 * Real.log (M * T)) / δ = C₂ * (2 * Real.log (M * T)) * (1 / δ) := by ring
    _ ≤ C₂ * (2 * Real.log (M * T)) * (C₁ * (T + 1) * Real.log (M * (T + 2)) / κ) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hC₂.le (by linarith))
    _ = 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) * κ⁻¹ := by ring
    _ ≤ 2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) * κ⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 hκ.le)
    _ = 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by ring

theorem exm_log_y (y : ℝ) (hy : 2 ≤ y) : 1 / 2 ≤ Real.log y := by
  calc (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ ≤ Real.log y := Real.log_le_log (by norm_num) hy

theorem exm_tail_num (C₃ T T' y l : ℝ) (hC₃ : 0 ≤ C₃) (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') ≤
      (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have hepi : Real.exp 1 ≤ Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have key : 1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') =
      (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) := by
    field_simp
  have hprod : Real.exp 1 * T ≤ 1 * (Real.pi * T') := by
    rw [one_mul]; exact mul_le_mul hepi hT' hT0.le Real.pi_pos.le
  have h1 : Real.exp 1 / (Real.pi * T') ≤ 1 / T := by
    rw [div_le_div_iff₀ (mul_pos Real.pi_pos hT'0) hT0]; exact hprod
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hA : 0 ≤ (1 + 2 * C₃) * Real.log y := mul_nonneg (by linarith) (by linarith)
  have hnum : Real.log y + C₃ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2 hA, mul_le_mul_of_nonneg_left hLy hC₃]
  rw [key]
  calc (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) ≤ (Real.log y + C₃) * (1 / T) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 * (1 / T) :=
        mul_le_mul_of_nonneg_right hnum (one_div_pos.2 hT0).le
    _ = (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by ring

theorem exm_horiz_num (G N T T' y l : ℝ) (hG : 0 ≤ G) (hN0 : 0 ≤ N) (hN : N ≤ G * (T * l ^ 2))
    (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) ≤
      3 * (G + 1) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have key : 1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) =
      3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) := by
    field_simp
  have hX : 0 ≤ Real.exp 1 / (2 * Real.pi * T' ^ 2) := by positivity
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hTl : 1 ≤ T * l ^ 2 := by nlinarith
  have hN1 : 3 * (N + 1) ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  have hA : Real.exp 1 ≤ 2 * Real.pi * Real.log y := by
    nlinarith [Real.exp_one_lt_d9, Real.pi_gt_three, mul_le_mul_of_nonneg_left hLy Real.pi_pos.le]
  have hTT : T ^ 2 ≤ T' ^ 2 := by nlinarith
  have hprod : Real.exp 1 * T ^ 2 ≤ Real.log y * (2 * Real.pi * T' ^ 2) := by
    nlinarith [mul_le_mul hA hTT (sq_nonneg T) (by nlinarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi * Real.log y)]
  have h1 : Real.exp 1 / (2 * Real.pi * T' ^ 2) ≤ Real.log y / T ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos two_pos Real.pi_pos) (pow_pos hT'0 2)) (pow_pos hT0 2)]; exact hprod
  have hB : 0 ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  rw [key]
  calc 3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2))
        ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) :=
        mul_le_mul_of_nonneg_right hN1 hX
    _ ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.log y / T ^ 2) := mul_le_mul_of_nonneg_left h1 hB
    _ = 3 * (G + 1) * (Real.log y * l ^ 2 / T) := by field_simp

theorem exm_left_num (κ G N M T T' σ₁ y : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 20) (hG : 0 ≤ G) (hN0 : 0 ≤ N)
    (hN : N ≤ G * (T * Real.log (M * T) ^ 2)) (hM : 3 ≤ M) (hT : 2 ≤ T) (hT0' : T ≤ T') (hT' : T' ≤ T + 1)
    (hσ : 1 - κ ≤ σ₁) (hσ' : σ₁ ≤ 1 - 3 * κ / 4) (hy : 2 ≤ y) :
    1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hMT : 0 < M * T := mul_pos hM0 hT0
  have hs1 : 19 / 20 ≤ σ₁ := by linarith
  have hs2 : 3 * κ / 4 ≤ 1 - σ₁ := by linarith
  have hs0 : 0 < σ₁ := by linarith
  have hs3 : 0 < 1 - σ₁ := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hsne : σ₁ ≠ 0 := hs0.ne'
  have hs3ne : 1 - σ₁ ≠ 0 := hs3.ne'
  have hs4 : σ₁ ≠ 1 := (by linarith : σ₁ < 1).ne
  have hs5 : (1 : ℝ) ≠ σ₁ := (by linarith : σ₁ < 1).ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hP : 57 * κ / 80 ≤ σ₁ * (1 - σ₁) := by
    nlinarith [mul_le_mul hs1 hs2 (by linarith) hs0.le]
  have hD : 2 * κ ≤ Real.pi * (σ₁ * (1 - σ₁)) := by
    nlinarith [mul_le_mul Real.pi_gt_three.le hP (by linarith) Real.pi_pos.le]
  have hDpos : 0 < Real.pi * (σ₁ * (1 - σ₁)) := by linarith
  have hc0 : 0 ≤ 4 / (3 * κ) := div_nonneg (by norm_num) (by linarith)
  have hL1 : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hLle : Real.log (M * T) ≤ M * T := by
    have := Real.log_le_sub_one_of_pos hMT
    linarith
  have hTL : 1 ≤ T * Real.log (M * T) ^ 2 := by nlinarith
  have hNc : N + 4 / (3 * κ) ≤ (G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hTL hc0]
  have hT'le : T' ≤ 3 * T / 2 := by linarith
  have hnum1 : T' * (N + 4 / (3 * κ)) ≤
      (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) :=
    mul_le_mul hT'le hNc (by linarith) (by linarith)
  have hGc : 0 ≤ G + 4 / (3 * κ) := by linarith
  have hTMT : T ≤ M * T := by nlinarith
  have hTL2 : T * Real.log (M * T) ≤ (M * T) * (M * T) :=
    mul_le_mul hTMT hLle (by linarith) hMT.le
  have hQ : (T * Real.log (M * T)) * (T * Real.log (M * T)) ≤
      ((M * T) * (M * T)) * ((M * T) * (M * T)) :=
    mul_le_mul hTL2 hTL2 (mul_nonneg hT0.le (by linarith)) (mul_self_nonneg _)
  have hnum2 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) ≤
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hGc
    have h2 := mul_nonneg hGc (pow_nonneg hMT.le 4)
    have e1 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) =
        3 / 2 * ((G + 4 / (3 * κ)) * ((T * Real.log (M * T)) * (T * Real.log (M * T)))) := by ring
    have e2 : (G + 4 / (3 * κ)) * (((M * T) * (M * T)) * ((M * T) * (M * T))) =
        (G + 4 / (3 * κ)) * (M * T) ^ 4 := by ring
    rw [e1]
    rw [e2] at h1
    linarith
  have hk0 : 0 ≤ 2 / κ := div_nonneg (by norm_num) hκ.le
  have hB0 : 0 ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGc) hk0) (pow_nonneg hMT.le 4)
  have hB2 : 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) =
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    field_simp
    ring
  have hchain : T' * (N + 4 / (3 * κ)) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
    calc T' * (N + 4 / (3 * κ)) ≤ 12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := hnum1.trans hnum2
      _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) := hB2.symm
      _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
          mul_le_mul_of_nonneg_left hD hB0
  have hA : T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 := by
    rw [div_le_iff₀ hDpos]; exact hchain
  have hA0 : 0 ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hDpos.le
  have hYle : y ^ σ₁ / y ≤ y ^ (-(κ / 2)) := by
    rw [← Real.rpow_sub_one hyne]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 ≤ y ^ (-(κ / 2)) := Real.rpow_nonneg hy0.le _
  calc 1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)))
        = T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * (y ^ σ₁ / y) := by
        field_simp
    _ ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_left hYle hA0
    _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_right hA hY0
    _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by ring

theorem sum_le_mul_rpow_add (AL AW C X Y W : ℝ) (hC4 : 4 ≤ C) (hCL : AL ≤ C) (hCW : AW ≤ C) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (hW : 0 ≤ W) : AL * (X ^ 4 * Y) + AW * W ≤ C * (X ^ C * Y + W) := by
  have hX0 : 0 ≤ X := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h4 : X ^ 4 ≤ X ^ C := by
    have h := Real.rpow_le_rpow_of_exponent_le hX hC4
    have e : X ^ (4 : ℝ) = X ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast X 4
    rwa [e] at h
  have h1 := mul_le_mul_of_nonneg_right hCL (mul_nonneg (pow_nonneg hX0 4) hY)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hY) hC0
  have h3 := mul_le_mul_of_nonneg_right hCW hW
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
