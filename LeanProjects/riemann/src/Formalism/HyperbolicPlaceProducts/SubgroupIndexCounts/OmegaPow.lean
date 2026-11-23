import Formalism.HyperbolicPlaceProducts.Statement

namespace Formalism.SLP.P

theorem two_pow_length_primeFactorsList_le (j : ℕ) (hj : 1 ≤ j) :
    2 ^ (Nat.primeFactorsList j).length ≤ j := by
  have hprod := Nat.prod_primeFactorsList (show j ≠ 0 by omega)
  calc 2 ^ (Nat.primeFactorsList j).length ≤ (Nat.primeFactorsList j).prod :=
        List.pow_card_le_prod _ _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = j := hprod

theorem pow_primeFactors_length_le : Formalism.SLP.OmegaPow := by
  intro n j hn hj
  set k := (Nat.primeFactorsList j).length
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hk : (2 : ℝ) ^ k ≤ j := by exact_mod_cast two_pow_length_primeFactorsList_le j hj

  have hklog : (k : ℝ) ≤ Real.logb 2 j := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hj0]
    simpa [Real.rpow_natCast] using hk
  have hlogn : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

  have e1 : (n : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0,
      Real.rpow_natCast]
  have e2 : (j : ℝ) ^ Real.logb 2 n = (2 : ℝ) ^ (Real.logb 2 j * Real.logb 2 n) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hj0]
  rw [e1, e2]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hklog hlogn)

end Formalism.SLP.P
