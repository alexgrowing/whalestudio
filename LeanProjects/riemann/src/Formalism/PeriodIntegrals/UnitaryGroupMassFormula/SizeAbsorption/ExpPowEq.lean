import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.Development

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

theorem key_ineq (c0 E w : ℝ) (hE : 0 ≤ E) (hw : 1 + |c0| + 18 + 4 * E ≤ w) :
    c0 + 4 * (E * w) + 2 * w ^ 2 + 12 * w ≤ w ^ 6 := by
  have hw1 : 1 ≤ w := by have := abs_nonneg c0; linarith
  have hw2 : w ≤ w ^ 2 := by nlinarith
  have hw21 : 1 ≤ w ^ 2 := one_le_pow₀ hw1
  have hw3 : w ^ 3 ≤ w ^ 6 := pow_le_pow_right₀ hw1 (by norm_num)
  have h1 : |c0| ≤ |c0| * w ^ 2 := le_mul_of_one_le_right (abs_nonneg _) hw21
  have h2 : E * w ≤ E * w ^ 2 := mul_le_mul_of_nonneg_left hw2 hE
  have h3 : (|c0| + 18 + 4 * E) * w ^ 2 ≤ w * w ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg w)
  have h4 : w * w ^ 2 = w ^ 3 := by ring
  have h5 := le_abs_self c0
  nlinarith

theorem exp_pow_eq (y : ℝ) (k : ℕ) : Real.exp y ^ k = Real.exp (k * y) := (Real.exp_nat_mul y k).symm

theorem core (x w E n N d1 d2 a b Y : ℝ) (hx : 1 < x) (hE : 0 ≤ E)
    (hW : 1 + |Real.log ((2 + |d1| + 2 * |d2|) * (10 + 4 * E) ^ 2)| + 18 + 4 * E ≤ w)
    (hl : Real.log x ≤ E * w) (hn1 : 1 ≤ n) (hn : n ≤ x ^ 3) (hN1 : 1 ≤ N)
    (hN : N ^ 2 ≤ Real.exp (w ^ 2))
    (hb : b = Real.exp (w ^ 6)) (ha : a = x * b) (hY : Y = x * n * Real.exp (w ^ 2)) :
    0 ≤ N ^ 2 * (Real.log (8 * n * N * a) + Real.log Y) + |d1| * N ^ 2 * Real.log (2 * a) +
        2 * |d2| * Real.log (2 * a) ^ 2 ∧
      Y * (N ^ 2 * (Real.log (8 * n * N * a) + Real.log Y) + |d1| * N ^ 2 * Real.log (2 * a) +
        2 * |d2| * Real.log (2 * a) ^ 2) ≤ b ∧
      1 < Y ∧ 1 ≤ Real.log Y := by
  subst hb ha hY
  have hw1 : 1 ≤ w := by have := abs_nonneg (Real.log ((2 + |d1| + 2 * |d2|) * (10 + 4 * E) ^ 2)); linarith
  have hx0 : 0 < x := by linarith
  have hn0 : 0 < n := by linarith
  have hN0 : 0 < N := by linarith
  have he2 : 0 < Real.exp (w ^ 2) := Real.exp_pos _
  have he6 : 0 < Real.exp (w ^ 6) := Real.exp_pos _
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hw6 : 0 ≤ w ^ 6 := by positivity
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw1
  have hEw : 0 ≤ E * w := mul_nonneg hE (by linarith)
  have hlogn : Real.log n ≤ 3 * Real.log x := by
    calc Real.log n ≤ Real.log (x ^ 3) := Real.log_le_log hn0 hn
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogN : Real.log N ≤ w ^ 2 := by
    have h1 : Real.log (N ^ 2) ≤ w ^ 2 := by
      calc Real.log (N ^ 2) ≤ Real.log (Real.exp (w ^ 2)) := Real.log_le_log (by positivity) hN
        _ = w ^ 2 := Real.log_exp _
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hxb : 0 < x * Real.exp (w ^ 6) := mul_pos hx0 he6
  have hloga : Real.log (x * Real.exp (w ^ 6)) = Real.log x + w ^ 6 := by
    rw [Real.log_mul hx0.ne' he6.ne', Real.log_exp]
  have h8n : (0 : ℝ) < 8 * n := by linarith
  have h8nN : 0 < 8 * n * N := mul_pos h8n hN0
  have hL1 : Real.log (8 * n * N * (x * Real.exp (w ^ 6))) =
      Real.log 8 + Real.log n + Real.log N + (Real.log x + w ^ 6) := by
    rw [Real.log_mul h8nN.ne' hxb.ne', Real.log_mul h8n.ne' hN0.ne',
      Real.log_mul (by norm_num) hn0.ne', hloga]
  have hL2 : Real.log (x * n * Real.exp (w ^ 2)) = Real.log x + Real.log n + w ^ 2 := by
    rw [Real.log_mul (mul_pos hx0 hn0).ne' he2.ne', Real.log_mul hx0.ne' hn0.ne', Real.log_exp]
  have hL3 : Real.log (2 * (x * Real.exp (w ^ 6))) = Real.log 2 + (Real.log x + w ^ 6) := by
    rw [Real.log_mul (by norm_num) hxb.ne', hloga]
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8); linarith
  have hlog80 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set P : ℝ := 8 + 4 * (E * w) + w ^ 2 + w ^ 6 with hPdef
  set L1 := Real.log (8 * n * N * (x * Real.exp (w ^ 6))) with hL1def
  set L2 := Real.log (x * n * Real.exp (w ^ 2)) with hL2def
  set L3 := Real.log (2 * (x * Real.exp (w ^ 6))) with hL3def
  have A1 : 0 ≤ L1 ∧ L1 ≤ P := by rw [hL1]; constructor <;> linarith
  have A2 : 0 ≤ L2 ∧ L2 ≤ P := by rw [hL2]; constructor <;> linarith
  have A3 : 0 ≤ L3 ∧ L3 ≤ P := by rw [hL3]; constructor <;> linarith
  have hlogY : 1 ≤ L2 := by rw [hL2]; linarith
  have hY1 : 1 < x * n * Real.exp (w ^ 2) := by
    calc (1 : ℝ) < x := hx
      _ ≤ x * n := le_mul_of_one_le_right hx0.le hn1
      _ ≤ x * n * Real.exp (w ^ 2) :=
        le_mul_of_one_le_right (mul_pos hx0 hn0).le (Real.one_le_exp (by positivity))
  set R := N ^ 2 * (L1 + L2) + |d1| * N ^ 2 * L3 + 2 * |d2| * L3 ^ 2 with hRdef
  have hR0 : 0 ≤ R :=
    add_nonneg (add_nonneg (mul_nonneg (sq_nonneg N) (add_nonneg A1.1 A2.1))
      (mul_nonneg (by positivity) A3.1)) (by positivity)
  refine ⟨hR0, ?_, hY1, hlogY⟩

  have hP1 : 1 ≤ P := by linarith
  have hPP : P ≤ P ^ 2 := by nlinarith
  have he21 : 1 ≤ Real.exp (w ^ 2) := Real.one_le_exp (by positivity)
  set Aa : ℝ := 2 + |d1| + 2 * |d2| with hAa
  have t1 : N ^ 2 * (L1 + L2) ≤ Real.exp (w ^ 2) * (2 * P ^ 2) :=
    mul_le_mul hN (by linarith) (add_nonneg A1.1 A2.1) he2.le
  have t2 : N ^ 2 * L3 ≤ Real.exp (w ^ 2) * P ^ 2 :=
    mul_le_mul hN (A3.2.trans hPP) A3.1 he2.le
  have t2' : |d1| * N ^ 2 * L3 ≤ |d1| * (Real.exp (w ^ 2) * P ^ 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left t2 (abs_nonneg _)
  have t3 : L3 ^ 2 ≤ Real.exp (w ^ 2) * P ^ 2 :=
    (pow_le_pow_left₀ A3.1 A3.2 2).trans (le_mul_of_one_le_left (sq_nonneg _) he21)
  have t3' : 2 * |d2| * L3 ^ 2 ≤ 2 * |d2| * (Real.exp (w ^ 2) * P ^ 2) :=
    mul_le_mul_of_nonneg_left t3 (by positivity)
  have hRle : R ≤ Real.exp (w ^ 2) * P ^ 2 * Aa := by
    rw [hRdef, hAa]; linarith only [t1, t2', t3']

  have hxle : x ≤ Real.exp (E * w) := by
    calc x = Real.exp (Real.log x) := (Real.exp_log hx0).symm
      _ ≤ Real.exp (E * w) := Real.exp_le_exp.2 hl
  have hYle : x * n * Real.exp (w ^ 2) ≤ Real.exp (4 * (E * w)) * Real.exp (w ^ 2) := by
    have h1 : x * n ≤ x ^ 4 := by
      calc x * n ≤ x * x ^ 3 := mul_le_mul_of_nonneg_left hn hx0.le
        _ = x ^ 4 := by ring
    have h2 : x ^ 4 ≤ Real.exp (4 * (E * w)) := by
      calc x ^ 4 ≤ Real.exp (E * w) ^ 4 := pow_le_pow_left₀ hx0.le hxle 4
        _ = Real.exp (4 * (E * w)) := by rw [exp_pow_eq]; norm_num
    exact mul_le_mul_of_nonneg_right (h1.trans h2) he2.le

  have hP6 : P ≤ (10 + 4 * E) * w ^ 6 := by
    have a1 : 1 ≤ w ^ 6 := one_le_pow₀ hw1
    have a2 : w ≤ w ^ 6 := by
      calc w = w ^ 1 := (pow_one w).symm
        _ ≤ w ^ 6 := pow_le_pow_right₀ hw1 (by norm_num)
    have a3 : w ^ 2 ≤ w ^ 6 := pow_le_pow_right₀ hw1 (by norm_num)
    have a4 : E * w ≤ E * w ^ 6 := mul_le_mul_of_nonneg_left a2 hE
    rw [hPdef]; linarith only [a1, a3, a4]
  have hwexp : w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  have hw12 : w ^ 12 ≤ Real.exp (12 * w) := by
    calc w ^ 12 ≤ Real.exp w ^ 12 := pow_le_pow_left₀ (by linarith) hwexp 12
      _ = Real.exp (12 * w) := by rw [exp_pow_eq]; norm_num
  have hPsq : P ^ 2 ≤ (10 + 4 * E) ^ 2 * Real.exp (12 * w) := by
    calc P ^ 2 ≤ ((10 + 4 * E) * w ^ 6) ^ 2 := pow_le_pow_left₀ (by linarith) hP6 2
      _ = (10 + 4 * E) ^ 2 * w ^ 12 := by ring
      _ ≤ (10 + 4 * E) ^ 2 * Real.exp (12 * w) := mul_le_mul_of_nonneg_left hw12 (by positivity)
  have hAa0 : 0 < Aa := by rw [hAa]; positivity
  set c0 := Real.log (Aa * (10 + 4 * E) ^ 2) with hc0
  have hc0e : Real.exp c0 = Aa * (10 + 4 * E) ^ 2 := Real.exp_log (by positivity)
  have hkey := key_ineq c0 E w hE hW
  calc x * n * Real.exp (w ^ 2) * R
      ≤ (Real.exp (4 * (E * w)) * Real.exp (w ^ 2)) * (Real.exp (w ^ 2) * P ^ 2 * Aa) :=
        mul_le_mul hYle hRle hR0 (by positivity)
    _ ≤ (Real.exp (4 * (E * w)) * Real.exp (w ^ 2)) *
          (Real.exp (w ^ 2) * ((10 + 4 * E) ^ 2 * Real.exp (12 * w)) * Aa) := by
        gcongr
    _ = Real.exp (c0 + 4 * (E * w) + 2 * w ^ 2 + 12 * w) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add, hc0e]
        have : Real.exp (2 * w ^ 2) = Real.exp (w ^ 2) * Real.exp (w ^ 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [this]; ring
    _ ≤ Real.exp (w ^ 6) := Real.exp_le_exp.2 hkey

end PI.SzEatI.W
