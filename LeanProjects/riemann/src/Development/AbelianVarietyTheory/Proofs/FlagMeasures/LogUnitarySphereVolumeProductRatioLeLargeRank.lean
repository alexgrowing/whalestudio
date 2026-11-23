import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.SphRatio

theorem sphV_succ (i : ℕ) :
    sphV (i + 1) = sphV i * (2 * Real.pi ^ (i + 1) / (i.factorial : ℝ)) := by
  unfold sphV
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem sphV_pos (i : ℕ) : 0 < sphV i := by
  unfold sphV
  exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity

theorem log_factor_le (n m : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ m) (hm : (n : ℝ) / 2 ≤ m) :
    Real.log (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)) ≤
      Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  have hpi := Real.pi_pos
  have he := Real.exp_pos 1
  have hn' : (18 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by linarith
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hc : 2 * Real.pi * Real.exp 1 ≤ n := by
    have h1 := Real.pi_lt_d2
    have h2 := Real.exp_one_lt_d9
    nlinarith
  have hL : 0 ≤ Real.log (n / (2 * Real.pi * Real.exp 1)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have h1 : (m : ℝ) ^ m / m.factorial ≤ Real.exp 1 ^ m := by
    rw [← Real.exp_nat_mul, mul_one]
    exact Real.pow_div_factorial_le_exp _ hm0.le m
  have h2 : 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) ≤
      (2 * Real.pi) * ((n / (2 * Real.pi * Real.exp 1))⁻¹) ^ m := by
    have h3 : Real.pi * Real.exp 1 / m ≤ (n / (2 * Real.pi * Real.exp 1))⁻¹ := by
      rw [inv_div, div_le_div_iff₀ hm0 (by linarith)]
      have : 0 < Real.pi * Real.exp 1 := by positivity
      nlinarith
    calc 2 * Real.pi ^ (m + 1) / (m.factorial : ℝ)
        = (2 * Real.pi) * ((Real.pi / m) ^ m * ((m : ℝ) ^ m / m.factorial)) := by
          rw [div_pow, pow_succ]; field_simp
      _ ≤ (2 * Real.pi) * ((Real.pi / m) ^ m * Real.exp 1 ^ m) := by gcongr
      _ = (2 * Real.pi) * (Real.pi * Real.exp 1 / m) ^ m := by
          rw [← mul_pow]; congr 2; ring
      _ ≤ _ := by gcongr
  refine (Real.log_le_log (by positivity) h2).trans ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv]
  nlinarith

theorem log_ratio_add_le (n q : ℕ) (a : ℝ) (hn : 18 ≤ n) (ha : a ≤ q) (hq : (n : ℝ) / 2 ≤ q)
    (j : ℕ) : Real.log (sphV (q + j) / sphV q) ≤
      j * (Real.log (2 * Real.pi) - a * Real.log (n / (2 * Real.pi * Real.exp 1))) := by
  induction j with
  | zero => simp [(sphV_pos q).ne']
  | succ j ih =>
    have hpi := Real.pi_pos
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h := log_factor_le n (q + j) a hn (by push_cast; linarith) (by push_cast; linarith)
    have h1 := sphV_pos (q + j)
    have h2 := sphV_pos q
    rw [← add_assoc, sphV_succ, mul_div_right_comm,
      Real.log_mul (by positivity) (by positivity)]
    push_cast
    linarith

theorem log_sphV_ratio_le : ∀ (n p j : ℕ), 18 ≤ n → j ≤ p → p ≤ n → (n : ℝ) - 2 * Real.sqrt n ≤ (p : ℝ) - j → (n : ℝ) / 2 ≤ (p : ℝ) - j → Real.log (sphV p / sphV (p - j)) ≤ j * Real.log (2 * Real.pi) - j * ((n : ℝ) - 2 * Real.sqrt n) * Real.log (n / (2 * Real.pi * Real.exp 1)) := by
  intro n p j hn hj _ ha hq
  have hc : ((p - j : ℕ) : ℝ) = (p : ℝ) - j := Nat.cast_sub hj
  have h := log_ratio_add_le n (p - j) _ hn (hc ▸ ha) (hc ▸ hq) j
  rw [Nat.sub_add_cancel hj] at h
  linarith

end GlobalTheory.SphRatio
