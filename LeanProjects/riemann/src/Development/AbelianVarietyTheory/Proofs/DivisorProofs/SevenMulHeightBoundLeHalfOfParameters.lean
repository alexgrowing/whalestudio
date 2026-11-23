import Mathlib

namespace GlobalTheory

theorem seven_mul_height_bound_le_half :
    ∀ (D T ρ PP κ b f r m k H TO Nb nW t : ℝ), 1 ≤ D → 0 < b → 1 ≤ f → 2 ≤ m → m ≤ k →
      r = k + m - 1 → 0 ≤ t → 0 ≤ κ → κ ≤ 4 * f * r * b → PP ^ 2 * D ^ 2 * k / m ≤ T →
      T ≤ TO → 4 * D + 4 ≤ T →
      ρ ≤ 3 * r * (f * (r * r * (2 * (T + D + 1)) / H + 2 * r * r * T * (2 / Real.sqrt b))) →
      TO * Nb * f ^ 2 * m ^ 2 * k * D * PP ≤ H → 2500 * r * (D + 1) ≤ TO →
      f * r * (r + 1) ≤ nW → (2 * f * m) ^ 4 * nW ≤ PP → PP ^ 3 * TO ^ 2 ≤ Real.sqrt b →
      TO * nW ≤ r + t → m * (t + 1) ≤ Nb → 7 * (D ^ 2 / T + D * ρ) * (PP * κ) ≤ b / 2 := by
  intro D T ρ PP κ b f r m k H TO Nb nW t hD hb hf hm hmk hr ht hκ0 hκ hT1 hTTO hT2 hρ hH hTO
    hnW hPP hPPb htn hNb
  have hk0 : 0 < k := by linarith
  have hr3 : 3 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  have hf0 : 0 < f := by linarith
  have hm0 : 0 < m := by linarith
  have hT0 : 0 < T := by linarith
  have hTO0 : 0 < TO := by linarith
  have hD0 : 0 < D := by linarith

  have hnW2 : f * r ^ 2 ≤ nW := by linarith [mul_pos hf0 hr0]
  have h4f : 4 * f ≤ 2 * f * m := by linarith [mul_le_mul_of_nonneg_left hm hf0.le]
  have hfm4 : (4 * f) ^ 4 ≤ (2 * f * m) ^ 4 := pow_le_pow_left₀ (by linarith) h4f 4
  have hf3 : 1 ≤ f ^ 3 := one_le_pow₀ hf
  have h256 : 256 * f ≤ (2 * f * m) ^ 4 := by
    have e : (4 * f) ^ 4 = 256 * f * f ^ 3 := by ring
    linarith [mul_le_mul_of_nonneg_left hf3 hf0.le]
  have hPPlow : 256 * f * (f * r ^ 2) ≤ PP := by
    have := mul_le_mul h256 hnW2 (mul_nonneg hf0.le (sq_nonneg r)) (by positivity)
    linarith
  have hPP0 : 0 < PP := lt_of_lt_of_le (by positivity) hPPlow

  have hX0 : 0 ≤ D ^ 2 / T := div_nonneg (sq_nonneg D) hT0.le
  have hXT : D ^ 2 / T * T = D ^ 2 := div_mul_cancel₀ _ hT0.ne'
  have h1 : PP ^ 2 * D ^ 2 * k ≤ T * m := by
    rw [div_le_iff₀ hm0] at hT1; linarith
  have hXPP2 : D ^ 2 / T * PP ^ 2 ≤ 1 := by
    have e : D ^ 2 / T * PP ^ 2 * (T * k) = PP ^ 2 * D ^ 2 * k := by
      rw [show D ^ 2 / T * PP ^ 2 * (T * k) = (D ^ 2 / T * T) * PP ^ 2 * k by ring, hXT]; ring
    have hTk : 0 < T * k := mul_pos hT0 hk0
    have : D ^ 2 / T * PP ^ 2 * (T * k) ≤ 1 * (T * k) := by
      rw [e]; linarith [mul_le_mul_of_nonneg_left hmk hT0.le]
    exact le_of_mul_le_mul_right this hTk
  have hfr : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf (by linarith)
  have h224 : 224 * (f * r) ≤ PP := by
    linarith [mul_le_mul_of_nonneg_left hfr (by linarith : (0:ℝ) ≤ f * r)]
  have hXPP : 0 ≤ D ^ 2 / T * PP := mul_nonneg hX0 hPP0.le
  have ha1 : D ^ 2 / T * PP * (224 * (f * r)) ≤ 1 := by
    calc D ^ 2 / T * PP * (224 * (f * r)) ≤ D ^ 2 / T * PP * PP :=
          mul_le_mul_of_nonneg_left h224 hXPP
      _ = D ^ 2 / T * PP ^ 2 := by ring
      _ ≤ 1 := hXPP2
  have ha : 7 * (D ^ 2 / T) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have e2 := mul_le_mul_of_nonneg_left e1 (by linarith [hX0] : (0:ℝ) ≤ 7 * (D ^ 2 / T))
    have e3 := mul_le_mul_of_nonneg_right ha1 hb.le
    linarith

  have hNb0 : 0 < Nb := by linarith [mul_pos hm0 (by linarith : (0:ℝ) < t + 1)]
  have hH0 : 0 < H := by
    have : 0 < TO * Nb * f ^ 2 * m ^ 2 * k * D * PP :=
      mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hTO0 hNb0) (pow_pos hf0 2))
        (pow_pos hm0 2)) hk0) hD0) hPP0
    linarith
  generalize hs : Real.sqrt b = s at hρ hPPb
  have hs0 : 0 < s := by rw [← hs]; exact Real.sqrt_pos.mpr hb
  have hss : s * s = b := by rw [← hs]; exact Real.mul_self_sqrt hb.le
  generalize hS1 : r * r * (2 * (T + D + 1)) / H = S1 at hρ
  generalize hS2 : 2 * r * r * T * (2 / s) = S2 at hρ
  have hS1H : S1 * H = r * r * (2 * (T + D + 1)) := by
    rw [← hS1]; exact div_mul_cancel₀ _ hH0.ne'
  have hS1_0 : 0 ≤ S1 := by
    rw [← hS1]; exact div_nonneg (mul_nonneg (mul_self_nonneg r) (by linarith)) hH0.le
  have h2s : (2:ℝ) / s * s = 2 := div_mul_cancel₀ 2 hs0.ne'
  have hS2s : S2 * s = 4 * r ^ 2 * T := by
    rw [← hS2]
    calc 2 * r * r * T * (2 / s) * s = 2 * r * r * T * (2 / s * s) := by ring
      _ = 4 * r ^ 2 * T := by rw [h2s]; ring
  have hS2_0 : 0 ≤ S2 := by
    rw [← hS2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0.le) hr0.le) hT0.le)
      (div_nonneg (by norm_num) hs0.le)

  have hS1b : S1 * H ≤ 4 * r ^ 2 * TO := by
    rw [hS1H]
    linarith [mul_le_mul_of_nonneg_left (show 2 * (T + D + 1) ≤ 4 * TO by linarith)
      (mul_self_nonneg r)]
  have hYQ : S1 * D * f ^ 2 * PP * (Nb * m ^ 2 * k) ≤ 4 * r ^ 2 := by
    have e1 : S1 * (TO * Nb * f ^ 2 * m ^ 2 * k * D * PP) ≤ S1 * H :=
      mul_le_mul_of_nonneg_left hH hS1_0
    have e2 : S1 * D * f ^ 2 * PP * (Nb * m ^ 2 * k) * TO ≤ 4 * r ^ 2 * TO := by
      calc _ = S1 * (TO * Nb * f ^ 2 * m ^ 2 * k * D * PP) := by ring
        _ ≤ S1 * H := e1
        _ ≤ _ := hS1b
    exact le_of_mul_le_mul_right e2 hTO0
  have hTO5 : 5000 * r ≤ TO := by
    linarith [mul_le_mul_of_nonneg_left (show (2:ℝ) ≤ D + 1 by linarith) hr0.le]
  have hrr1 : 0 ≤ r * (r + 1) := mul_nonneg hr0.le (by linarith)
  have hnW3 : r * (r + 1) ≤ nW := by
    linarith [mul_le_mul_of_nonneg_right hf hrr1]
  have hTOnW : 5000 * r * (r * (r + 1)) ≤ TO * nW := mul_le_mul hTO5 hnW3 hrr1 hTO0.le
  have ht1 : 5000 * r ^ 3 ≤ t + 1 := by
    linarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ r by linarith) hr0.le]
  have hm3 : 8 ≤ m ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm 3
    linarith [show (2:ℝ) ^ 3 = 8 by norm_num]
  have hm3k : 4 * r ≤ m ^ 3 * k := by linarith [mul_le_mul_of_nonneg_right hm3 hk0.le]
  have hQlow : 20000 * r ^ 4 ≤ Nb * m ^ 2 * k := by
    have e1 : m * (t + 1) * (m ^ 2 * k) ≤ Nb * (m ^ 2 * k) :=
      mul_le_mul_of_nonneg_right hNb (mul_nonneg (sq_nonneg m) hk0.le)
    have e2 : (4 * r) * (5000 * r ^ 3) ≤ (m ^ 3 * k) * (t + 1) :=
      mul_le_mul hm3k ht1 (mul_nonneg (by norm_num) (pow_nonneg hr0.le 3))
        (mul_nonneg (pow_nonneg hm0.le 3) hk0.le)
    linarith [e1, e2]
  have hY0 : 0 ≤ S1 * D * f ^ 2 * PP :=
    mul_nonneg (mul_nonneg (mul_nonneg hS1_0 hD0.le) (sq_nonneg f)) hPP0.le
  have hY : S1 * D * f ^ 2 * PP * (5000 * r ^ 2) ≤ 1 := by
    have e1 := mul_le_mul_of_nonneg_left hQlow hY0
    have hr2 : 0 < 4 * r ^ 2 := by have := pow_pos hr0 2; linarith
    have e2 : (4 * r ^ 2) * (S1 * D * f ^ 2 * PP * (5000 * r ^ 2)) ≤ (4 * r ^ 2) * 1 := by
      linarith [hYQ, e1]
    exact le_of_mul_le_mul_left e2 hr2
  have hterm1 : 7 * (D * (3 * r * (f * S1))) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have hc : 0 ≤ 7 * (D * (3 * r * (f * S1))) :=
      mul_nonneg (by norm_num) (mul_nonneg hD0.le
        (mul_nonneg (mul_nonneg (by norm_num) hr0.le) (mul_nonneg hf0.le hS1_0)))
    have e2 := mul_le_mul_of_nonneg_left e1 hc
    have e3 := mul_le_mul_of_nonneg_right hY hb.le
    linarith

  have hPP2 : 2688 * D * r ^ 4 * f ^ 2 ≤ PP ^ 2 * TO := by
    have hTOD : D ≤ TO := by
      linarith [mul_le_mul_of_nonneg_right hr3 (by linarith : (0:ℝ) ≤ D + 1)]
    have e1 : (256 * f * (f * r ^ 2)) ^ 2 ≤ PP ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) hf0.le)
        (mul_nonneg hf0.le (sq_nonneg r))) hPPlow 2
    have hf2 : 1 ≤ f ^ 2 := one_le_pow₀ hf
    have e2 : 2688 * r ^ 4 * f ^ 2 ≤ (256 * f * (f * r ^ 2)) ^ 2 := by
      linarith [mul_le_mul_of_nonneg_right hf2 (by positivity : (0:ℝ) ≤ f ^ 2 * r ^ 4),
        (by positivity : (0:ℝ) ≤ f ^ 2 * r ^ 4)]
    have e3 := mul_le_mul (le_trans e2 e1) hTOD hD0.le (sq_nonneg PP)
    linarith [e3]
  have hterm2 : 7 * (D * (3 * r * (f * S2))) * (PP * κ) ≤ b / 8 := by
    have e1 : PP * κ ≤ PP * (4 * f * r * b) := mul_le_mul_of_nonneg_left hκ hPP0.le
    have hc : 0 ≤ 7 * (D * (3 * r * (f * S2))) :=
      mul_nonneg (by norm_num) (mul_nonneg hD0.le
        (mul_nonneg (mul_nonneg (by norm_num) hr0.le) (mul_nonneg hf0.le hS2_0)))
    have e2 := mul_le_mul_of_nonneg_left e1 hc
    have e3 : 7 * (D * (3 * r * (f * S2))) * (PP * (4 * f * r * b))
        = 336 * D * r ^ 4 * f ^ 2 * T * PP * s := by
      rw [← hss]
      calc _ = 84 * D * r ^ 2 * f ^ 2 * PP * (S2 * s) * s := by ring
        _ = _ := by rw [hS2s]; ring
    have e4 : 2688 * D * r ^ 4 * f ^ 2 * T * PP ≤ s := by
      have f1 := mul_le_mul hPP2 hTTO hT0.le (mul_nonneg (sq_nonneg PP) hTO0.le)
      have f2 := mul_le_mul_of_nonneg_right f1 hPP0.le
      calc 2688 * D * r ^ 4 * f ^ 2 * T * PP ≤ PP ^ 2 * TO * TO * PP := f2
        _ = PP ^ 3 * TO ^ 2 := by ring
        _ ≤ s := hPPb
    have e5 := mul_le_mul_of_nonneg_right e4 hs0.le
    linarith [e2, e3, e5, hss]
  have hDρ : D * ρ * (PP * κ) ≤ D * (3 * r * (f * (S1 + S2))) * (PP * κ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hD0.le) (mul_nonneg hPP0.le hκ0)
  have e : 7 * (D ^ 2 / T + D * ρ) * (PP * κ)
      = 7 * (D ^ 2 / T) * (PP * κ) + 7 * (D * ρ * (PP * κ)) := by ring
  have e' : D * (3 * r * (f * (S1 + S2))) * (PP * κ)
      = D * (3 * r * (f * S1)) * (PP * κ) + D * (3 * r * (f * S2)) * (PP * κ) := by ring
  rw [e]
  linarith [ha, hterm1, hterm2, hDρ, e', hb]

end GlobalTheory
