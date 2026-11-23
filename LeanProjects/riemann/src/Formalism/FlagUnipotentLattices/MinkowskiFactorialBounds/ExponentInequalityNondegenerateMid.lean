import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

lemma exponent_inequality_single (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (R lGam : ℝ) (hR : 1 ≤ R) (hMR : M = 2 * R + 2)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    F * lC + (C * M ^ 2 * F * L) * (C * M ^ 3) + lGam + C * M ^ 6 * F * L +
      (K * F) * (lC - (2 * R + 1) * lg - R * lk) / 2 ≤ -(K * F * lk) := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have f1 : F * lC ≤ F * (lk / 32) := mul_le_mul_of_nonneg_left hlClk hF0
  have f1b : 1 * (F * lk) ≤ K * (F * lk) :=
    mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ K) (mul_nonneg hF0 hlk0)
  have f4a : M * (C * (M ^ 5 * F * L)) ≤ M * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_left hC1Y hM0
  have f4b : M * (C ^ 32 * (M ^ 5 * F * L)) ≤ F * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_right hMF hZ0
  have f4c : F * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ F * K := mul_le_mul_of_nonneg_left hX hF0
  have hR1 : 0 ≤ (R - 1) * lg := mul_nonneg (by linarith) hlg0
  have hR2 : 0 ≤ (R - 1) * lk := mul_nonneg (by linarith) hlk0
  have hD : lC - (2 * R + 1) * lg - R * lk ≤ -23 * lk := by linarith
  have f5 : K * F * (lC - (2 * R + 1) * lg - R * lk) ≤ K * F * (-23 * lk) := mul_le_mul_of_nonneg_left hD hKF0
  linarith

lemma exponent_inequality_nondegenerate_mid (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 1) * K * F) * (l2 - lg) + (C * M ^ 2 * F * L * C + S * K * F * lC) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam ≤
      -(K * F * lg) / 2 - lk := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have hS0 : 0 ≤ S := by linarith
  have g2 : C ^ 2 * (M ^ 2 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 2 (by norm_num)) (pow_nonneg hC0 2)
  have g5a : C ^ 2 * (M ^ 4 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 4 (by norm_num)) (pow_nonneg hC0 2)
  have g5b : S * (C ^ 2 * (M ^ 4 * F * L)) ≤ S * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (g5a.trans hC2Y) hS0
  have g5c : S * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ S * K := mul_le_mul_of_nonneg_left hX hS0
  have g5d : S * (32 * K) ≤ S * (K * F * lg) := mul_le_mul_of_nonneg_left h32 hS0
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have g6a : 6 * S * F * (lC + 2 * lk) ≤ 6 * S * F * (3 * lk) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hS0) hF0)
  have g6b : S * F * lk ≤ S * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hSF0
  have g6c : 36 * (S * F * lg) ≤ K * (S * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hSF0 hlg0)
  have g4 : K * F * lC ≤ K * F * (lg / 256) := mul_le_mul_of_nonneg_left hlClg hKF0
  have hS1K : 0 ≤ (S - 1) * K * F := mul_nonneg (mul_nonneg (by linarith) hK0) hF0
  have g1 : ((S - 1) * K * F) * (l2 - lg) ≤ ((S - 1) * K * F) * (-(7 / 8) * lg) :=
    mul_le_mul_of_nonneg_left (by linarith) hS1K
  have g3 : S * K * F * lC ≤ S * K * F * (lg / 256) :=
    mul_le_mul_of_nonneg_left hlClg (mul_nonneg (mul_nonneg hS0 hK0) hF0)
  have g8a : 1 * (K * F * lg) ≤ (S - 1) * (K * F * lg) := mul_le_mul_of_nonneg_right (by linarith) hW0
  have g8b : 0 ≤ (S - 2) * (K * F * lg) := mul_nonneg (by linarith) hW0
  linarith

lemma exponent_inequality_nondegenerate_top (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K) (hKS : K - 1 ≤ S)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 1) * K * F) * (l2 - lg) + (K * F * (lk + L) + (K * F * (lC + lk) +
        ((C * M ^ 2 * F * L) * (C * M) + C * M * F * L) * (C * K))) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam ≤
      -(K * F * lg) / 2 - lk := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have hS0 : 0 ≤ S := by linarith
  have g2 : C ^ 2 * (M ^ 2 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 2 (by norm_num)) (pow_nonneg hC0 2)
  have g5a : C ^ 2 * (M ^ 4 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 4 (by norm_num)) (pow_nonneg hC0 2)
  have g5b : S * (C ^ 2 * (M ^ 4 * F * L)) ≤ S * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (g5a.trans hC2Y) hS0
  have g5c : S * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ S * K := mul_le_mul_of_nonneg_left hX hS0
  have g5d : S * (32 * K) ≤ S * (K * F * lg) := mul_le_mul_of_nonneg_left h32 hS0
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have g6a : 6 * S * F * (lC + 2 * lk) ≤ 6 * S * F * (3 * lk) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hS0) hF0)
  have g6b : S * F * lk ≤ S * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hSF0
  have g6c : 36 * (S * F * lg) ≤ K * (S * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hSF0 hlg0)
  have g4 : K * F * lC ≤ K * F * (lg / 256) := mul_le_mul_of_nonneg_left hlClg hKF0
  have t1 : K * F * lk ≤ K * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hKF0
  have t1b : K * F * L ≤ K * F * (lg / 8) := mul_le_mul_of_nonneg_left hLlg hKF0
  have t2a : C ^ 3 * (M ^ 3 * F * L) ≤ C ^ 3 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 3 (by norm_num)) (pow_nonneg hC0 3)
  have t2b : K * (C ^ 3 * (M ^ 3 * F * L)) ≤ K * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (t2a.trans hC3Y) hK0
  have t2c : C ^ 2 * (M * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_left hM1Y (pow_nonneg hC0 2)
  have t2d : K * (C ^ 2 * (M * F * L)) ≤ K * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (t2c.trans hC2Y) hK0
  have t2e : K * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ K * K := mul_le_mul_of_nonneg_left hX hK0
  have hS1K : 0 ≤ (S - 1) * K * F := mul_nonneg (mul_nonneg (by linarith) hK0) hF0
  have g1 : ((S - 1) * K * F) * (l2 - lg) ≤ ((S - 1) * K * F) * (-(7 / 8) * lg) :=
    mul_le_mul_of_nonneg_left (by linarith) hS1K
  have g8b : 0 ≤ (S - 2) * (K * F * lg) := mul_nonneg (by linarith) hW0
  have t3 : (K / 2) * (32 * K) ≤ (S - 1) * (K * F * lg) := mul_le_mul (by linarith) h32 (by linarith) (by linarith)
  have t4 : 100 * (K * F * lg) ≤ (S - 1) * (K * F * lg) := mul_le_mul_of_nonneg_right (by linarith) hW0
  linarith

lemma exponent_inequality_degenerate_mid (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K) (hG0 : 0 ≤ lGam)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 2) * K * F) * (l2 - lg) + (C * M ^ 2 * F * L * C + S * K * F * lC) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam +
      C * M ^ 6 * F * L + K * F * (lC - lk) ≤ -(K * F * lk) / 2 - 2 * lGam - lk := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have hS0 : 0 ≤ S := by linarith
  have g2 : C ^ 2 * (M ^ 2 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 2 (by norm_num)) (pow_nonneg hC0 2)
  have g5a : C ^ 2 * (M ^ 4 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 4 (by norm_num)) (pow_nonneg hC0 2)
  have g5b : S * (C ^ 2 * (M ^ 4 * F * L)) ≤ S * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (g5a.trans hC2Y) hS0
  have g5c : S * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ S * K := mul_le_mul_of_nonneg_left hX hS0
  have g5d : S * (32 * K) ≤ S * (K * F * lg) := mul_le_mul_of_nonneg_left h32 hS0
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have g6a : 6 * S * F * (lC + 2 * lk) ≤ 6 * S * F * (3 * lk) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hS0) hF0)
  have g6b : S * F * lk ≤ S * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hSF0
  have g6c : 36 * (S * F * lg) ≤ K * (S * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hSF0 hlg0)
  have g4 : K * F * lC ≤ K * F * (lg / 256) := mul_le_mul_of_nonneg_left hlClg hKF0
  have hS2K : 0 ≤ (S - 2) * K * F := mul_nonneg (mul_nonneg (by linarith) hK0) hF0
  have d1 : ((S - 2) * K * F) * (l2 - lg) ≤ ((S - 2) * K * F) * (-(7 / 8) * lg) :=
    mul_le_mul_of_nonneg_left (by linarith) hS2K
  have d4 : K * F * lC ≤ K * F * (lk / 32) := mul_le_mul_of_nonneg_left hlClk hKF0
  have d5d : (S - 2) * (32 * K) ≤ (S - 2) * (K * F * lg) := mul_le_mul_of_nonneg_left h32 (by linarith)
  have hS2F : 0 ≤ (S - 2) * F := mul_nonneg (by linarith) hF0
  have d6b : (S - 2) * F * lk ≤ (S - 2) * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hS2F
  have d6c : 36 * ((S - 2) * F * lg) ≤ K * ((S - 2) * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hS2F hlg0)
  have d6d : 36000 * (F * lk) ≤ K * (F * lk) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hF0 hlk0)
  have f4a : M * (C * (M ^ 5 * F * L)) ≤ M * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_left hC1Y hM0
  have f4b : M * (C ^ 32 * (M ^ 5 * F * L)) ≤ F * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_right hMF hZ0
  have f4c : F * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ F * K := mul_le_mul_of_nonneg_left hX hF0
  have d9 : K * F * (lC - lk) ≤ K * F * (lk / 32 - lk) := mul_le_mul_of_nonneg_left (by linarith) hKF0
  have d3a : S * K * F * lC ≤ S * K * F * (lk / 32) :=
    mul_le_mul_of_nonneg_left hlClk (mul_nonneg (mul_nonneg hS0 hK0) hF0)
  have d3b : (S - 2) * K * F * lk ≤ (S - 2) * K * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hS2K
  have B3 : S * K * F * lC ≤ (S - 2) * K * F * lg / 256 + K * F * lk / 16 := by linarith
  have hU : 0 ≤ (S - 2) * K * F * lg := mul_nonneg hS2K hlg0
  have B2 : C * M ^ 2 * F * L * C ≤ K * F * lk / 64 := by linarith
  have B4 : K * F * lC ≤ K * F * lk / 32 := by linarith
  have B5 : C * M ^ 2 * F * L * (C * (S + M) * M ^ 2) ≤
      (S - 2) * K * F * lg / 512 + K * F * lk / 32 + K * F * lk / 64 := by linarith
  have B6 : 6 * S * F * (lC + 2 * lk) ≤ (S - 2) * K * F * lg / 16 + K * F * lk / 1000 := by linarith
  have B7 : 3 * lGam ≤ 3 * (K * F * lk) / 64 := by linarith
  have BetaSesquilinearity : C * M ^ 6 * F * L ≤ K * F * lk / 16 := by linarith
  have B9 : lk ≤ K * F * lk / 1000 := by linarith
  have lowerOffDiagonalCoeff : K * F * (lC - lk) ≤ K * F * lk / 32 - K * F * lk := by linarith
  linarith

lemma exponent_inequality_degenerate_top (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K) (hKS : K - 1 ≤ S)
    (hG0 : 0 ≤ lGam) (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 2) * K * F) * (l2 - lg) + (K * F * (lk + L) + (K * F * (lC + lk) +
        ((C * M ^ 2 * F * L) * (C * M) + C * M * F * L) * (C * K))) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam +
      C * M ^ 6 * F * L + K * F * (lC - lk) ≤ -(K * F * lk) / 2 - 2 * lGam - lk := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have hS0 : 0 ≤ S := by linarith
  have g2 : C ^ 2 * (M ^ 2 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 2 (by norm_num)) (pow_nonneg hC0 2)
  have g5a : C ^ 2 * (M ^ 4 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 4 (by norm_num)) (pow_nonneg hC0 2)
  have g5b : S * (C ^ 2 * (M ^ 4 * F * L)) ≤ S * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (g5a.trans hC2Y) hS0
  have g5c : S * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ S * K := mul_le_mul_of_nonneg_left hX hS0
  have g5d : S * (32 * K) ≤ S * (K * F * lg) := mul_le_mul_of_nonneg_left h32 hS0
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have g6a : 6 * S * F * (lC + 2 * lk) ≤ 6 * S * F * (3 * lk) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hS0) hF0)
  have g6b : S * F * lk ≤ S * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hSF0
  have g6c : 36 * (S * F * lg) ≤ K * (S * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hSF0 hlg0)
  have g4 : K * F * lC ≤ K * F * (lg / 256) := mul_le_mul_of_nonneg_left hlClg hKF0
  have t1 : K * F * lk ≤ K * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hKF0
  have t1b : K * F * L ≤ K * F * (lg / 8) := mul_le_mul_of_nonneg_left hLlg hKF0
  have t2a : C ^ 3 * (M ^ 3 * F * L) ≤ C ^ 3 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 3 (by norm_num)) (pow_nonneg hC0 3)
  have t2b : K * (C ^ 3 * (M ^ 3 * F * L)) ≤ K * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (t2a.trans hC3Y) hK0
  have t2c : C ^ 2 * (M * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_left hM1Y (pow_nonneg hC0 2)
  have t2d : K * (C ^ 2 * (M * F * L)) ≤ K * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (t2c.trans hC2Y) hK0
  have t2e : K * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ K * K := mul_le_mul_of_nonneg_left hX hK0
  have hS2K : 0 ≤ (S - 2) * K * F := mul_nonneg (mul_nonneg (by linarith) hK0) hF0
  have d1 : ((S - 2) * K * F) * (l2 - lg) ≤ ((S - 2) * K * F) * (-(7 / 8) * lg) :=
    mul_le_mul_of_nonneg_left (by linarith) hS2K
  have d4 : K * F * lC ≤ K * F * (lk / 32) := mul_le_mul_of_nonneg_left hlClk hKF0
  have d5d : (S - 2) * (32 * K) ≤ (S - 2) * (K * F * lg) := mul_le_mul_of_nonneg_left h32 (by linarith)
  have hS2F : 0 ≤ (S - 2) * F := mul_nonneg (by linarith) hF0
  have d6b : (S - 2) * F * lk ≤ (S - 2) * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hS2F
  have d6c : 36 * ((S - 2) * F * lg) ≤ K * ((S - 2) * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hS2F hlg0)
  have d6d : 36000 * (F * lk) ≤ K * (F * lk) := mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hF0 hlk0)
  have f4a : M * (C * (M ^ 5 * F * L)) ≤ M * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_left hC1Y hM0
  have f4b : M * (C ^ 32 * (M ^ 5 * F * L)) ≤ F * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_right hMF hZ0
  have f4c : F * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ F * K := mul_le_mul_of_nonneg_left hX hF0
  have d9 : K * F * (lC - lk) ≤ K * F * (lk / 32 - lk) := mul_le_mul_of_nonneg_left (by linarith) hKF0
  have u3 : (K / 2) * (32 * K) ≤ (S - 2) * (K * F * lg) := mul_le_mul (by linarith) h32 (by linarith) (by linarith)
  have u4 : 100 * (K * F * lg) ≤ (S - 2) * (K * F * lg) := mul_le_mul_of_nonneg_right (by linarith) hW0
  have B1 : K * F * (lk + L) + (K * F * (lC + lk) + ((C * M ^ 2 * F * L) * (C * M) + C * M * F * L) * (C * K)) ≤
      (S - 2) * K * F * lg / 100 + (S - 2) * K * F * lg / 64 := by linarith
  have hU : 0 ≤ (S - 2) * K * F * lg := mul_nonneg hS2K hlg0
  have B2 : C * M ^ 2 * F * L * C ≤ K * F * lk / 64 := by linarith
  have B4 : K * F * lC ≤ K * F * lk / 32 := by linarith
  have B5 : C * M ^ 2 * F * L * (C * (S + M) * M ^ 2) ≤
      (S - 2) * K * F * lg / 512 + K * F * lk / 32 + K * F * lk / 64 := by linarith
  have B6 : 6 * S * F * (lC + 2 * lk) ≤ (S - 2) * K * F * lg / 16 + K * F * lk / 1000 := by linarith
  have B7 : 3 * lGam ≤ 3 * (K * F * lk) / 64 := by linarith
  have BetaSesquilinearity : C * M ^ 6 * F * L ≤ K * F * lk / 16 := by linarith
  have B9 : lk ≤ K * F * lk / 1000 := by linarith
  have lowerOffDiagonalCoeff : K * F * (lC - lk) ≤ K * F * lk / 32 - K * F * lk := by linarith
  linarith

lemma pow_eq_exp_mul_log (x : ℝ) (hx : 0 < x) (n : ℕ) : x ^ n = Real.exp ((n:ℝ) * Real.log x) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hx, mul_comm]

lemma heightParameter_rpow (C : ℝ) (m f : ℕ) (b y : ℝ) (hb : 0 < b) :
    bigH C m f b ^ y = Real.exp ((C * (m:ℝ) ^ 2 * f * Real.log b) * y) := by
  unfold bigH
  rw [← Real.rpow_mul hb.le, Real.rpow_def_of_pos hb]
  congr 1
  ring

lemma parameterRange_bounds (C : ℝ) (hC : 1 ≤ C) (k m f : ℕ) (b g v NT Gam : ℝ)
    (h : Params C (16 * C ^ 32) k m f b g v NT Gam) :
    (4:ℝ) ≤ m ∧ (m:ℝ) ≤ f ∧ (f:ℝ) ≤ k ∧ 0.69 ≤ Real.log b ∧ 1 ≤ Real.log k ∧ 0 ≤ Real.log C ∧
    32 * Real.log C ≤ Real.log k ∧ 8 * (Real.log k + Real.log b) ≤ Real.log g ∧ 0 ≤ Real.log 2 ∧
    Real.log 2 ≤ Real.log b ∧ 16 * C ^ 32 * ((m:ℝ) ^ 5 * f * Real.log b) ≤ k ∧ 0 < g ∧ 0 < b ∧
    0 < v ∧ Real.log v ≤ Real.log b ∧ 0 < NT ∧ Real.log NT ≤ C * m * f * Real.log b ∧ 0 < Gam ∧
    0 ≤ Real.log Gam ∧ Real.log Gam ≤ C * (m:ℝ) ^ 5 * f * Real.log b := by
  unfold Params at h
  obtain ⟨hm, hmf, hfk, hb, hkbg, hK, hv1, hvb, hNT1, hNTb, hG1, hGe⟩ := h
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmf' : (m : ℝ) ≤ f := by exact_mod_cast hmf
  have hfk' : (f : ℝ) ≤ k := by exact_mod_cast hfk
  have hb0 : 0 < b := by linarith
  have hl2b : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
  have hlb : 0.69 ≤ Real.log b := by
    have := Real.log_two_gt_d9
    linarith
  have hC0 : 0 < C := by linarith
  have a1 : (1 : ℝ) ≤ C ^ 32 := one_le_pow₀ hC
  have a2 : (1 : ℝ) ≤ (m : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have a3 : (1 : ℝ) ≤ (m : ℝ) ^ 5 * f := one_le_mul_of_one_le_of_one_le a2 (by linarith)
  have a4 : 1 * 0.69 ≤ (m : ℝ) ^ 5 * f * Real.log b := mul_le_mul a3 hlb (by norm_num) (by linarith)
  have a5 : (m : ℝ) ^ 5 * f * Real.log b ≤ C ^ 32 * ((m : ℝ) ^ 5 * f * Real.log b) :=
    le_mul_of_one_le_left (by linarith) a1
  have hKk : 16 * C ^ 32 * ((m : ℝ) ^ 5 * f * Real.log b) ≤ k := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hlk : 1 ≤ Real.log k := by
    have he := Real.exp_one_lt_d9
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log k := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have a6 : C ^ 32 * 1 ≤ C ^ 32 * (16 * ((m : ℝ) ^ 5 * f * Real.log b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hC32k : C ^ 32 ≤ (k : ℝ) := by linarith
  have hlCk : 32 * Real.log C ≤ Real.log k := by
    have h1 := Real.log_le_log (by positivity) hC32k
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hkb0 : (0 : ℝ) < ((k : ℝ) * b) ^ 8 := by positivity
  have hg0 : 0 < g := lt_of_lt_of_le hkb0 hkbg
  have hlg : 8 * (Real.log k + Real.log b) ≤ Real.log g := by
    have h1 := Real.log_le_log hkb0 hkbg
    rw [Real.log_pow, Real.log_mul hk0.ne' hb0.ne'] at h1
    push_cast at h1
    linarith
  have hv0 : 0 < v := by linarith
  have hNT0 : 0 < NT := by linarith
  have hGam0 : 0 < Gam := by linarith
  have hlNT : Real.log NT ≤ C * m * f * Real.log b := by
    have h1 := Real.log_le_log hNT0 hNTb
    rwa [Real.log_rpow hb0] at h1
  have hlG : Real.log Gam ≤ C * (m : ℝ) ^ 5 * f * Real.log b := by
    have h1 := Real.log_le_log hGam0 hGe
    rwa [Real.log_exp] at h1
  exact ⟨hm', hmf', hfk', hlb, hlk, Real.log_nonneg hC, hlCk, hlg, Real.log_nonneg (by norm_num), hl2b,
    hKk, hg0, hb0, hv0, Real.log_le_log hv0 hvb, hNT0, hlNT, hGam0, Real.log_nonneg hG1, hlG⟩

noncomputable def commonLatticeBound (C : ℝ) (k m f s : ℕ) (b v Gam : ℝ) (Xi : ℕ → ℝ) : ℝ :=
  ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
    bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam

lemma commonFactor_nonneg_and_le (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v Gam : ℝ) (Xi : ℕ → ℝ) (A : ℝ)
    (hb : 0 < b) (hv : 0 < v) (hGam : 0 < Gam) (hs1 : 1 ≤ s) (hsk : s ≤ k) (hf1 : 1 ≤ f)
    (hfk : f ≤ k) (hXi0 : 0 ≤ Xi s) (hA : ((k : ℝ) * v) ^ (k * f) * Xi s ≤ Real.exp A) :
    0 ≤ commonLatticeBound C k m f s b v Gam Xi ∧ commonLatticeBound C k m f s b v Gam Xi ≤
      Real.exp (A + (k:ℝ) * f * Real.log C +
        (C * (m:ℝ) ^ 2 * f * Real.log b) * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) +
        6 * (s:ℝ) * f * (Real.log C + 2 * Real.log k) + Real.log Gam) := by
  have hC0 : 0 < C := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hs1.trans hsk))
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs1)
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hf1)
  have hCsf : 0 < C * s * f := mul_pos (mul_pos hC0 hs0) hf0
  have hX0 : 0 ≤ ((k : ℝ) * v) ^ (k * f) * Xi s := mul_nonneg (pow_nonneg (mul_pos hk0 hv).le _) hXi0
  have e1 : C ^ (k * f) = Real.exp ((k : ℝ) * f * Real.log C) := by
    rw [pow_eq_exp_mul_log C hC0, Nat.cast_mul]
  have e2 : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) =
      Real.exp ((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :=
    heightParameter_rpow C m f b _ hb
  have e3 : (C * s * f) ^ (6 * s * f) ≤ Real.exp (6 * (s : ℝ) * f * (Real.log C + 2 * Real.log k)) := by
    rw [pow_eq_exp_mul_log _ hCsf]
    apply Real.exp_le_exp.2
    have hl : Real.log (C * s * f) ≤ Real.log C + 2 * Real.log k := by
      rw [Real.log_mul (mul_pos hC0 hs0).ne' hf0.ne', Real.log_mul hC0.ne' hs0.ne']
      have h1 := Real.log_le_log hs0 (show (s : ℝ) ≤ k by exact_mod_cast hsk)
      have h2 := Real.log_le_log hf0 (show (f : ℝ) ≤ k by exact_mod_cast hfk)
      linarith
    have h6 : (0 : ℝ) ≤ ((6 * s * f : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((6 * s * f : ℕ) : ℝ) * Real.log (C * s * f)
        ≤ ((6 * s * f : ℕ) : ℝ) * (Real.log C + 2 * Real.log k) := mul_le_mul_of_nonneg_left hl h6
      _ = 6 * (s : ℝ) * f * (Real.log C + 2 * Real.log k) := by push_cast; ring
  unfold commonLatticeBound
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hX0 (Real.exp_pos _).le) (Real.exp_pos _).le)
      (pow_nonneg hCsf.le _)) hGam.le
  · rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hGam]
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA
      (Real.exp_pos _).le) (Real.exp_pos _).le) e3 (pow_nonneg hCsf.le _) (by positivity)) le_rfl hGam.le
      (by positivity)

lemma massRatio_bound_of_mid (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) (hb : 0 < b)
    (hXi : XiHyp C k m f b v NT Xi) (hs2 : 2 ≤ s) (hsk : s + 2 ≤ k) :
    0 ≤ Xi s ∧ ((k : ℝ) * v) ^ (k * f) * Xi s ≤
      Real.exp (C * (m:ℝ) ^ 2 * f * Real.log b * C + (s:ℝ) * k * f * Real.log C) := by
  unfold XiHyp at hXi
  obtain ⟨h0, h1⟩ := hXi.1 s hs2 hsk
  refine ⟨h0, h1.trans (le_of_eq ?_)⟩
  rw [heightParameter_rpow C m f b C hb, pow_eq_exp_mul_log C (by linarith) (s * k * f), ← Real.exp_add,
    Nat.cast_mul, Nat.cast_mul]

lemma massRatio_bound_of_top (C : ℝ) (hC : 1 ≤ C) (k m f s : ℕ) (b v NT : ℝ) (Xi : ℕ → ℝ) (hb : 0 < b)
    (hv : 0 < v) (hNT : 0 < NT) (hk : 1 ≤ k) (hlv : Real.log v ≤ Real.log b)
    (hlNT : Real.log NT ≤ C * m * f * Real.log b)
    (hXi : XiHyp C k m f b v NT Xi) (hs : s + 1 = k ∨ s = k) :
    0 ≤ Xi s ∧ ((k : ℝ) * v) ^ (k * f) * Xi s ≤
      Real.exp ((k:ℝ) * f * (Real.log k + Real.log b) + ((k:ℝ) * f * (Real.log C + Real.log k) +
        ((C * (m:ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k))) := by
  unfold XiHyp at hXi
  obtain ⟨h0, h1⟩ := hXi.2 s hs
  refine ⟨h0, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hC0 : 0 < C := by linarith
  have hH : 0 < bigH C m f b ^ (C * m) := by
    rw [heightParameter_rpow C m f b _ hb]
    exact Real.exp_pos _
  have hkv : ((k : ℝ) * v) ^ (k * f) ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) := by
    rw [pow_eq_exp_mul_log _ (mul_pos hk0 hv), Real.log_mul hk0.ne' hv.ne', Nat.cast_mul]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hCk : (C * k) ^ (k * f) = Real.exp ((k : ℝ) * f * (Real.log C + Real.log k)) := by
    rw [pow_eq_exp_mul_log _ (mul_pos hC0 hk0), Real.log_mul hC0.ne' hk0.ne', Nat.cast_mul]
  have hB : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤
      Real.exp (((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k)) := by
    rw [Real.rpow_def_of_pos (mul_pos hH hNT), Real.log_mul hH.ne' hNT.ne', heightParameter_rpow C m f b _ hb,
      Real.log_exp]
    apply Real.exp_le_exp.2
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_pos hC0 hk0).le
  calc ((k : ℝ) * v) ^ (k * f) * Xi s ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) *
        ((C * k) ^ (k * f) * (bigH C m f b ^ (C * m) * NT) ^ (C * k)) :=
        mul_le_mul hkv h1 h0 (Real.exp_pos _).le
    _ ≤ Real.exp ((k : ℝ) * f * (Real.log k + Real.log b)) *
        (Real.exp ((k : ℝ) * f * (Real.log C + Real.log k)) *
          Real.exp (((C * (m : ℝ) ^ 2 * f * Real.log b) * (C * m) + C * m * f * Real.log b) * (C * k))) := by
        rw [hCk]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]

lemma two_div_pow_eq_exp (g : ℝ) (hg : 0 < g) (n : ℕ) :
    (2 / g) ^ n = Real.exp ((n:ℝ) * (Real.log 2 - Real.log g)) := by
  rw [pow_eq_exp_mul_log _ (div_pos two_pos hg) n, Real.log_div (by norm_num) hg.ne']

theorem sumNondegenerateRowsLe : NonDegSum := by
  unfold NonDegSum
  intro C hC
  refine ⟨16 * C ^ 32, ?_⟩
  intro k m f b g v NT Gam Xi hPar hXi
  obtain ⟨hm4, hmf, hfk, hlb, hlk, hlC0, hlC, hlg, hl20, hl2, hX, hg0, hb0, hv0, hlv, hNT0, hlNT,
    hGam0, hlG0, hlG⟩ := parameterRange_bounds C hC k m f b g v NT Gam hPar
  have hk0 : (0 : ℝ) < k := by linarith
  have hk0' : (k : ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hf1 : 1 ≤ f := by exact_mod_cast (show (1 : ℝ) ≤ f by linarith)
  have hfkN : f ≤ k := by exact_mod_cast hfk
  have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hkexp : ∀ X : ℝ, (k : ℝ) * Real.exp (X - Real.log k) = Real.exp X := fun X => by
    rw [Real.exp_sub, Real.exp_log hk0]
    field_simp
  have hrow : ∀ s ∈ Finset.Icc 2 k, ndRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log g) / 2 - Real.log k) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs2, hsk⟩ := hs
    have hrowEq : ndRow C k m f s b g v Gam Xi =
        (2 / g) ^ ((s - 1) * k * f) * commonLatticeBound C k m f s b v Gam Xi := by
      unfold ndRow commonLatticeBound
      ring
    have hcast : (((s - 1) * k * f : ℕ) : ℝ) = ((s : ℝ) - 1) * k * f := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    have hs2R : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    have hskR : (s : ℝ) ≤ k := by exact_mod_cast hsk
    rw [hrowEq, two_div_pow_eq_exp g hg0, hcast]
    rcases (show s + 2 ≤ k ∨ (s + 1 = k ∨ s = k) by omega) with hmid | htop
    · obtain ⟨hXi0, hA⟩ := massRatio_bound_of_mid C hC k m f s b v NT Xi hb0 hXi hs2 hmid
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_nondegenerate_mid C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hlG
      refine le_trans (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    · have hKS : (k : ℝ) - 1 ≤ s := by
        have h1 : k ≤ s + 1 := by omega
        have h2 : (k : ℝ) ≤ s + 1 := by exact_mod_cast h1
        linarith
      obtain ⟨hXi0, hA⟩ := massRatio_bound_of_top C hC k m f s b v NT Xi hb0 hv0 hNT0 hk1 hlv hlNT hXi htop
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_nondegenerate_top C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hKS hlG
      refine le_trans (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
  calc _ ≤ ∑ s ∈ Finset.Icc 2 k, Real.exp (-((k : ℝ) * f * Real.log g) / 2 - Real.log k) := Finset.sum_le_sum hrow
    _ = ((Finset.Icc 2 k).card : ℝ) * Real.exp (-((k : ℝ) * f * Real.log g) / 2 - Real.log k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * Real.exp (-((k : ℝ) * f * Real.log g) / 2 - Real.log k) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [Nat.card_Icc]
        exact_mod_cast (by omega : k + 1 - 2 ≤ k)
    _ = Real.exp (-((k : ℝ) * f * Real.log g) / 2) := hkexp _
    _ = (Real.sqrt g)⁻¹ ^ (k * f) := by
        rw [pow_eq_exp_mul_log _ (inv_pos.2 (Real.sqrt_pos.2 hg0)) (k * f), Real.log_inv, Real.log_sqrt hg0.le,
          Nat.cast_mul]
        congr 1
        ring

theorem sumDegenerateRowsLe : DegSum := by
  unfold DegSum
  intro C hC
  refine ⟨16 * C ^ 32, ?_⟩
  intro k m f b g v NT Gam Xi hPar hXi
  obtain ⟨hm4, hmf, hfk, hlb, hlk, hlC0, hlC, hlg, hl20, hl2, hX, hg0, hb0, hv0, hlv, hNT0, hlNT,
    hGam0, hlG0, hlG⟩ := parameterRange_bounds C hC k m f b g v NT Gam hPar
  have hk0 : (0 : ℝ) < k := by linarith
  have hk0' : (k : ℝ) ≠ 0 := hk0.ne'
  have hC0 : 0 < C := by linarith
  have hf1 : 1 ≤ f := by exact_mod_cast (show (1 : ℝ) ≤ f by linarith)
  have hfkN : f ≤ k := by exact_mod_cast hfk
  have hk1 : 1 ≤ k := by exact_mod_cast (show (1 : ℝ) ≤ k by linarith)
  have hkexp : ∀ X : ℝ, (k : ℝ) * Real.exp (X - Real.log k) = Real.exp X := fun X => by
    rw [Real.exp_sub, Real.exp_log hk0]
    field_simp
  have hrow : ∀ s ∈ Finset.Icc 2 k, degRow C k m f s b g v Gam Xi ≤ Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs2, hsk⟩ := hs
    have hrowEq : degRow C k m f s b g v Gam Xi =
        (2 / g) ^ ((s - 2) * k * f) * commonLatticeBound C k m f s b v Gam Xi *
          Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by
      unfold degRow commonLatticeBound
      ring
    have hcast : (((s - 2) * k * f : ℕ) : ℝ) = ((s : ℝ) - 2) * k * f := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ s), Nat.cast_ofNat]
    have hCk : (C / k) ^ (k * f) = Real.exp ((k : ℝ) * f * (Real.log C - Real.log k)) := by
      rw [pow_eq_exp_mul_log _ (div_pos hC0 hk0), Real.log_div hC0.ne' hk0', Nat.cast_mul]
    have hs2R : (2 : ℝ) ≤ s := by exact_mod_cast hs2
    have hskR : (s : ℝ) ≤ k := by exact_mod_cast hsk
    rw [hrowEq, two_div_pow_eq_exp g hg0, hcast, hCk]
    rcases (show s + 2 ≤ k ∨ (s + 1 = k ∨ s = k) by omega) with hmid | htop
    · obtain ⟨hXi0, hA⟩ := massRatio_bound_of_mid C hC k m f s b v NT Xi hb0 hXi hs2 hmid
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_degenerate_mid C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hlG0 hlG
      refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    · have hKS : (k : ℝ) - 1 ≤ s := by
        have h1 : k ≤ s + 1 := by omega
        have h2 : (k : ℝ) ≤ s + 1 := by exact_mod_cast h1
        linarith
      obtain ⟨hXi0, hA⟩ := massRatio_bound_of_top C hC k m f s b v NT Xi hb0 hv0 hNT0 hk1 hlv hlNT hXi htop
      obtain ⟨-, hc⟩ := commonFactor_nonneg_and_le C hC k m f s b v Gam Xi _ hb0 hv0 hGam0 (by omega) hsk hf1 hfkN hXi0 hA
      have hcore := exponent_inequality_degenerate_top C k f m (Real.log b) (Real.log k) (Real.log g) (Real.log C) (Real.log 2) hC hm4 hmf
        hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX s (Real.log Gam) hs2R hskR hKS hlG0 hlG
      refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (Real.exp_pos _).le) (Real.exp_pos _).le) ?_
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
  calc _ ≤ ∑ s ∈ Finset.Icc 2 k, Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := Finset.sum_le_sum hrow
    _ = ((Finset.Icc 2 k).card : ℝ) * Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam - Real.log k) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        rw [Nat.card_Icc]
        exact_mod_cast (by omega : k + 1 - 2 ≤ k)
    _ = Real.exp (-((k : ℝ) * f * Real.log k) / 2 - 2 * Real.log Gam) := hkexp _
    _ = Real.exp (-((k : ℝ) * f * Real.log k) / 2) * (Gam ^ 2)⁻¹ := by
        rw [Real.exp_sub, pow_eq_exp_mul_log Gam hGam0 2, div_eq_mul_inv, Nat.cast_ofNat]

theorem singleRowBound : SingleRowBound := by
  unfold SingleRowBound
  intro C hC
  refine ⟨16 * C ^ 32, ?_⟩
  intro k r f b g v NT Gam hPar
  obtain ⟨hm4, hmf, hfk, hlb, hlk, hlC0, hlC, hlg, hl20, hl2, hX, hg0, hb0, hv0, hlv, hNT0, hlNT,
    hGam0, hlG0, hlG⟩ := parameterRange_bounds C hC k (2 * r + 2) f b g v NT Gam hPar
  have hC0 : 0 < C := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hR : (1 : ℝ) ≤ r := by
    have h := hm4
    push_cast at h
    linarith
  have hMR : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have hcore := exponent_inequality_single C k f ((2 * r + 2 : ℕ) : ℝ) (Real.log b) (Real.log k) (Real.log g) (Real.log C)
    (Real.log 2) hC hm4 hmf hfk hlb hlk hlC0 hlC hlg hl20 hl2 hX r (Real.log Gam) hR hMR hlG
  have hg1 : 0 < g⁻¹ ^ (2 * r + 1) := pow_pos (inv_pos.2 hg0) _
  have hk1 : 0 < ((k : ℝ) ^ r)⁻¹ := inv_pos.2 (pow_pos hk0 _)
  have hin : 0 < C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹ := mul_pos (mul_pos hC0 hg1) hk1
  have e4 : Real.sqrt ((C * g⁻¹ ^ (2 * r + 1) * ((k : ℝ) ^ r)⁻¹) ^ (k * f)) =
      Real.exp (((k : ℝ) * f) * (Real.log C - (2 * r + 1) * Real.log g - r * Real.log k) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (pow_pos hin _), Real.log_pow,
      Real.log_mul (mul_pos hC0 hg1).ne' hk1.ne', Real.log_mul hC0.ne' hg1.ne', Real.log_pow, Real.log_inv,
      Real.log_inv, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [pow_eq_exp_mul_log C hC0 f, heightParameter_rpow C (2 * r + 2) f b _ hb0, ← Real.exp_log hGam0, e4]
  simp only [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith)

end Formalism.HermitianLatticeCounting.P
