import Mathlib

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities

variable {x : ℝ}

lemma u_le (hx : 11 ≤ x) : x⁻¹ ≤ 1 / 11 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 11 - x⁻¹ = (x - 11) / (11 * x) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 11 - x⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h0.le)
  linarith

lemma p_le (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 1 / 10 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 10 - (x - 1)⁻¹ = (x - 11) / (10 * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 10 - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h1.le)
  linarith

lemma e_le (hx : 11 ≤ x) : (x - 2)⁻¹ ≤ 1 / 9 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 9 - (x - 2)⁻¹ = (x - 11) / (9 * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 9 - (x - 2)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h2.le)
  linarith

lemma u_le_p (hx : 11 ≤ x) : x⁻¹ ≤ (x - 1)⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : (x - 1)⁻¹ - x⁻¹ = 1 / (x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ (x - 1)⁻¹ - x⁻¹ := by
    rw [e]
    exact div_nonneg (zero_le_one) (mul_nonneg h0.le h1.le)
  linarith

lemma q_le (hx : 11 ≤ x) : x / (x - 1) ^ 2 ≤ 121 / 100 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by norm_num) h0.le) (sq_nonneg _))
  linarith

lemma e_le_u (hx : 11 ≤ x) : (x - 2)⁻¹ ≤ 11 / 9 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 9 * x⁻¹ - (x - 2)⁻¹ = (2 * x - 22) / (9 * x * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 9 * x⁻¹ - (x - 2)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h2.le)
  linarith

lemma p_le_u (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 11 / 10 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 10 * x⁻¹ - (x - 1)⁻¹ = (x - 11) / (10 * x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 10 * x⁻¹ - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h1.le)
  linarith

lemma inv_sub_one_sq_le_inv (hx : 11 ≤ x) : (x - 1)⁻¹ ^ 2 ≤ x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : x⁻¹ - (x - 1)⁻¹ ^ 2 = (x ^ 2 - 3 * x + 1) / (x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ x⁻¹ - (x - 1)⁻¹ ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg h0.le (sq_nonneg _))
  linarith

lemma k_cut (hx : 11 ≤ x) :
    (x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹ ≤ 5 / 4 * x⁻¹ ^ 2 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 5 / 4 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹) = (x ^ 3 - 12 * x ^ 2 + 17 * x - 10) / (4 * x ^ 2 * (x - 1) ^ 2 * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 5 / 4 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹) := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h, mul_nonneg (mul_nonneg h h) h]) (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) h2.le)
  linarith

lemma k_le (hx : 11 ≤ x) :
    (x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹ ≤ 22 / 9 * x⁻¹ ^ 2 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 22 / 9 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹) = (4 * x ^ 2 - 48 * x + 44) / (9 * x ^ 2 * (x - 1) * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 22 / 9 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹) := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by positivity) h1.le) h2.le)
  linarith

lemma r21 (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 21 / 100 - (2 * x - 1) / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 21 / 100 - (2 * x - 1) / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (by norm_num) (sq_nonneg _))
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities
