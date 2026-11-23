import Mathlib
open Real

namespace GlobalTheory

theorem log_theta_weight_size_le (f r Lb S sz : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ Lb)
    (hlog : Real.log (f * r) ≤ Lb) (hS : ∃ N : ℕ, S = N) (hlogS : Real.log S ≤ 10 * Lb)
    (hsz0 : 0 ≤ sz) (hsz : sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1)) :
    Real.log sz ≤ 20 * Lb := by
  obtain ⟨N, rfl⟩ := hS
  have hx : 0 < f * r := by positivity
  have hE : 2 ≤ Real.exp Lb := by have := Real.add_one_le_exp Lb; linarith
  have hxE : f * r ≤ Real.exp Lb := by
    rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hlog
  have hpow : ∀ n : ℕ, Real.exp Lb ^ n = Real.exp (n * Lb) := fun n => (Real.exp_nat_mul Lb n).symm
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hSE : (N:ℝ) ≤ Real.exp Lb ^ 10 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; positivity
    · have hNp : (0:ℝ) < N := by exact_mod_cast h
      rw [hpow, ← Real.exp_log hNp]
      exact Real.exp_le_exp.mpr (by push_cast; linarith)
  set E := Real.exp Lb with hEdef
  set x := f * r with hxdef
  have hE1 : 1 ≤ E := by linarith
  have hr1 : 1 + r ≤ 2 * x := by rw [hxdef]; nlinarith
  have h1 : (1 + r) * (N:ℝ) ≤ 2 * E ^ 11 := by
    calc (1 + r) * (N:ℝ) ≤ (2 * x) * N := mul_le_mul_of_nonneg_right hr1 hN0
      _ ≤ (2 * E) * E ^ 10 := by
          apply mul_le_mul (by linarith) hSE hN0 (by positivity)
      _ = 2 * E ^ 11 := by ring
  have h2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * E ^ 2 := by
    have : r * f * (4 * (f * r + 1) + 1) = x * (4 * x + 5) := by rw [hxdef]; ring
    rw [this]
    have hx1 : 1 ≤ x := by rw [hxdef]; nlinarith
    nlinarith
  have h3 : E ^ 2 ≤ E ^ 11 := pow_le_pow_right₀ hE1 (by norm_num)
  have h4 : (2:ℝ) ^ 9 ≤ E ^ 9 := pow_le_pow_left₀ (by norm_num) hE 9
  have h5 : 11 * E ^ 11 ≤ E ^ 20 := by
    have : E ^ 20 = E ^ 9 * E ^ 11 := by ring
    rw [this]
    have : (0:ℝ) ≤ E ^ 11 := by positivity
    nlinarith
  have key : sz ≤ Real.exp (20 * Lb) := by
    have : Real.exp (20 * Lb) = E ^ 20 := by rw [hEdef, hpow]; norm_num
    rw [this]; linarith
  rcases hsz0.eq_or_lt with h | h
  · subst h; simp; linarith
  · exact (Real.log_le_iff_le_exp h).mpr key

end GlobalTheory
