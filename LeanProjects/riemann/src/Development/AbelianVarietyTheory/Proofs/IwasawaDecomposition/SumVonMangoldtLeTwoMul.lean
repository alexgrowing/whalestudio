import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem lcmUpto_le_four_pow_small : ∀ n : ℕ, n ≤ 100 → Nat.lcmUpto n ≤ 4 ^ n := by
  decide +kernel

theorem psi_le_two_mul_small {y : ℝ} (h0 : 0 ≤ y) (h : y ≤ 100) : Chebyshev.psi y ≤ 2 * y := by
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have hn : ⌊y⌋₊ ≤ 100 := Nat.floor_le_of_le (by exact_mod_cast h)
  have h1 : ((Nat.lcmUpto ⌊y⌋₊ : ℕ) : ℝ) ≤ 4 ^ ⌊y⌋₊ := by
    exact_mod_cast lcmUpto_le_four_pow_small _ hn
  have h2 : (0 : ℝ) < (Nat.lcmUpto ⌊y⌋₊ : ℕ) := by exact_mod_cast Nat.lcmUpto_pos _
  have h3 := Real.log_le_log h2 h1
  rw [Real.log_pow] at h3
  have h4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have h5 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le h0
  have h6 : (0 : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem psi_le_of_le_sqrt {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (h : ∀ y : ℝ, 0 ≤ y → y ≤ √x → Chebyshev.psi y ≤ C * y) :
    Chebyshev.psi x ≤ 1.4 * x + 3 * C * √x := by
  have key : ∀ n : ℝ, 2 ≤ n → Chebyshev.psi (x ^ n⁻¹) ≤ C * √x := by
    intro n hn
    have hle : x ^ n⁻¹ ≤ √x := by
      rw [Real.sqrt_eq_rpow, one_div]
      exact Real.rpow_le_rpow_of_exponent_le hx (inv_anti₀ (by norm_num) hn)
    exact (h _ (by positivity) hle).trans (mul_le_mul_of_nonneg_left hle hC)
  have h1 := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := Chebyshev.theta_le_log4_mul_x (x := x) (by linarith)
  have h4 : Real.log 4 ≤ 1.4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have h5 : Real.log 4 * x ≤ 1.4 * x := mul_le_mul_of_nonneg_right h4 (by linarith)
  linarith [key 2 le_rfl, key 3 (by norm_num), key 5 (by norm_num)]

theorem psi_le_two_mul {y : ℝ} (h0 : 0 ≤ y) : Chebyshev.psi y ≤ 2 * y := by
  rcases le_total y 100 with h | h
  · exact psi_le_two_mul_small h0 h
  have hs : √y * √y = y := Real.mul_self_sqrt h0
  have h10 : 10 ≤ √y := Real.le_sqrt_of_sq_le (by linarith)
  rcases le_total (√y) 100 with h' | h'
  · have := psi_le_of_le_sqrt (C := 2) (by norm_num) (by linarith : 1 ≤ y)
      (fun z hz hz' => psi_le_two_mul_small hz (hz'.trans h'))
    nlinarith
  · have h4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have := psi_le_of_le_sqrt (C := 6) (by norm_num) (by linarith : 1 ≤ y)
      (fun z hz _ => (Chebyshev.psi_le_const_mul_self hz).trans
        (mul_le_mul_of_nonneg_right (by linarith) hz))
    nlinarith

theorem sum_vonMangoldt_le_two_mul : ∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, Λ n ≤ 2 * y := by
  intro y hy
  have h := psi_le_two_mul hy
  rw [Chebyshev.psi] at h
  rwa [show Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ from Finset.Icc_add_one_left_eq_Ioc 0 _]

end GlobalTheory.Mem.An
