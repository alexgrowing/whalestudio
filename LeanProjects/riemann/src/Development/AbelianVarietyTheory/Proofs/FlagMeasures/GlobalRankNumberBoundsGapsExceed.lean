import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

open GlobalTheory.Diag.PG

namespace GlobalTheory.Diag.PG

theorem gaps_exceed :
    ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x →
      ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → ∀ r : ℝ, k ≤ r → r ≤ 2 * k →
      C * k * m ^ 4 + r * m ^ 10 < 4 * Del ∧ C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) ∧
      C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps ∧
      C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
  intro eps CD heps _heps' hCD C hC
  refine ⟨max (max 1 (C + 2)) (max (C ^ (100 / eps)) ((16 : ℝ) ^ (2 / eps))), ?_⟩
  intro x hx m f k lrd Del h r hkr hrk
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC : C + 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC' : C ^ (100 / eps) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx16 : (16 : ℝ) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx0 : 0 ≤ x := by linarith
  have hm1 : 1 ≤ m := le_trans (Real.one_le_rpow hx1 (by norm_num)) h.m_lo
  have hm4 : x ≤ m ^ 4 := by
    have h1 : (x ^ ((1 : ℝ) / 4)) ^ 4 ≤ m ^ 4 := by
      gcongr
      exact h.m_lo
    have h2 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
    linarith
  have hf : x ≤ f := le_trans hm4 h.mf
  have hk : x ≤ k := le_trans hf h.fk
  have hr : x ≤ r := le_trans hk hkr
  have hf1 : 1 ≤ f := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL : 1 ≤ x ^ eps := Real.one_le_rpow hx1 heps.le
  have hL' : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx1 (by positivity)
  have hm10 : m ^ 10 ≤ f ^ 3 := by
    have h1 : m ^ 10 ≤ m ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
    have h2 : m ^ 12 = (m ^ 4) ^ 3 := by ring
    have h3 : (m ^ 4) ^ 3 ≤ f ^ 3 := by gcongr; exact h.mf
    linarith
  have hf3 : f ≤ f ^ 3 := by
    have := pow_le_pow_right₀ hf1 (show 1 ≤ 3 by norm_num); simpa using this
  have hS : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * k * f ^ 3 := by
    have h1 : C * k * m ^ 4 ≤ C * k * f ^ 3 := by
      have : m ^ 4 ≤ f ^ 3 := le_trans h.mf hf3
      gcongr
    have h2 : r * m ^ 10 ≤ (2 * k) * f ^ 3 := by
      gcongr
    nlinarith
  have hSpos : 0 < C * k * m ^ 4 + r * m ^ 10 := by positivity

  have hy1 : 1 ≤ k * f * x ^ eps := by
    have : 1 ≤ k * f := one_le_mul_of_one_le_of_one_le hk1 hf1
    exact one_le_mul_of_one_le_of_one_le this hL
  have hDel3 : (k * f * x ^ eps) ^ (3 : ℕ) ≤ Del := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hCD
    rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    linarith [h.Del_lo]
  have hDelpos : 0 < Del := by
    have : 0 < (k * f * x ^ eps) ^ (3 : ℕ) := by positivity
    linarith
  have hc1 : C * k * m ^ 4 + r * m ^ 10 < 4 * Del := by
    have hkf3 : 0 < k * f ^ 3 := by positivity
    have hk2 : C + 2 < 4 * k ^ 2 := by nlinarith
    have e1 : (C + 2) * k * f ^ 3 < 4 * k ^ 2 * (k * f ^ 3) := by nlinarith
    have e2 : 4 * k ^ 2 * (k * f ^ 3) ≤ 4 * (k * f * x ^ eps) ^ (3 : ℕ) := by
      have hkf : k * f ≤ k * f * x ^ eps := le_mul_of_one_le_right (by positivity) hL
      have : (k * f) ^ 3 ≤ (k * f * x ^ eps) ^ 3 := by gcongr
      nlinarith
    linarith

  set t := x ^ (eps / 2) with ht
  have ht16 : 16 ≤ t := by
    have h1 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) ≤ x ^ (eps / 2) :=
      Real.rpow_le_rpow (by positivity) hx16 (by positivity)
    have h2 : ((16 : ℝ) ^ (2 / eps)) ^ (eps / 2) = 16 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 2 / eps * (eps / 2) = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith
  have hxe : x ^ eps = t ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
  have hDelE : Del ≤ Real.exp t := by
    have := h.Del_hi
    rw [Real.log_le_iff_le_exp hDelpos] at this
    exact this
  have hc2 : C * k * m ^ 4 + r * m ^ 10 < Real.sqrt (bx x eps) := by
    rw [Real.lt_sqrt hSpos.le]
    have e1 : (C * k * m ^ 4 + r * m ^ 10) ^ 2 < (4 * Real.exp t) ^ 2 := by
      have : C * k * m ^ 4 + r * m ^ 10 < 4 * Real.exp t := by linarith
      gcongr
    have e2 : (4 * Real.exp t) ^ 2 = Real.exp (Real.log 16 + 2 * t) := by
      rw [Real.exp_add, Real.exp_log (by norm_num)]
      rw [show 2 * t = t + t by ring, Real.exp_add]; ring
    have e3 : Real.log 16 + 2 * t ≤ x ^ eps := by
      have : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      rw [hxe]; nlinarith
    have e4 : Real.exp (Real.log 16 + 2 * t) ≤ bx x eps := by
      unfold bx; exact Real.exp_le_exp.mpr e3
    linarith

  have hc3 : C * k * m ^ 4 + r * m ^ 10 < x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hf35 : f ^ 3 ≤ f ^ 5 := pow_le_pow_right₀ hf1 (by norm_num)
    have e1 : C * k * m ^ 4 + r * m ^ 10 ≤ (C + 2) * r * f ^ 5 := by
      have : (C + 2) * k * f ^ 3 ≤ (C + 2) * r * f ^ 5 := by gcongr
      linarith
    have hx18 : x ≤ x ^ 18 := by
      have := pow_le_pow_right₀ hx1 (show 1 ≤ 18 by norm_num); simpa using this
    have hr18 : x ^ 18 ≤ r ^ 18 := by gcongr
    have e2 : (C + 2) * r * f ^ 5 < r ^ 18 * (r * f ^ 5) := by
      have hp : 0 < r * f ^ 5 := by positivity
      have hC18 : C + 2 < r ^ 18 := by
        have hx2 : x ^ 2 ≤ x ^ 18 := pow_le_pow_right₀ hx1 (by norm_num)
        have : x < x ^ 2 := by nlinarith
        linarith
      have := mul_lt_mul_of_pos_right hC18 hp
      calc (C + 2) * r * f ^ 5 = (C + 2) * (r * f ^ 5) := by ring
        _ < r ^ 18 * (r * f ^ 5) := this
    have e3 : r ^ 18 * (r * f ^ 5) = r ^ 19 * f ^ 5 := by ring
    have e4 : r ^ 19 * f ^ 5 ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
      have hp : 0 ≤ r ^ 19 * f ^ 5 := by positivity
      have h1 : 1 ≤ x ^ (eps / 100) * x ^ eps := one_le_mul_of_one_le_of_one_le hL' hL
      have := mul_le_mul_of_nonneg_right h1 hp
      calc r ^ 19 * f ^ 5 = 1 * (r ^ 19 * f ^ 5) := by ring
        _ ≤ (x ^ (eps / 100) * x ^ eps) * (r ^ 19 * f ^ 5) := this
        _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
    linarith

  have hc4 : C * r ^ 19 * f ^ 5 * x ^ eps ≤ x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by
    have hCx : C ≤ x ^ (eps / 100) := by
      have h1 : (C ^ (100 / eps)) ^ (eps / 100) ≤ x ^ (eps / 100) :=
        Real.rpow_le_rpow (by positivity) hxC' (by positivity)
      have h2 : (C ^ (100 / eps)) ^ (eps / 100) = C := by
        rw [← Real.rpow_mul hC.le]
        have : 100 / eps * (eps / 100) = 1 := by field_simp
        rw [this, Real.rpow_one]
      linarith
    have hp : 0 ≤ r ^ 19 * f ^ 5 * x ^ eps := by positivity
    have := mul_le_mul_of_nonneg_right hCx hp
    calc C * r ^ 19 * f ^ 5 * x ^ eps = C * (r ^ 19 * f ^ 5 * x ^ eps) := by ring
      _ ≤ x ^ (eps / 100) * (r ^ 19 * f ^ 5 * x ^ eps) := this
      _ = x ^ (eps / 100) * r ^ 19 * f ^ 5 * x ^ eps := by ring
  exact ⟨hc1, hc2, hc3, hc4⟩

end GlobalTheory.Diag.PG
