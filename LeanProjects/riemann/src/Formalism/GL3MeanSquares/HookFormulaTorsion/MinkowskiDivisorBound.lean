import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset

private theorem mink_term (n p i : ℕ) (hp : 2 ≤ p) :
    n / (p ^ i * (p - 1)) ≤ 2 * n / p ^ (1 + i) := by
  have hpos : 0 < p ^ (1 + i) := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hpos]
  have h1 : n / (p ^ i * (p - 1)) * (p ^ i * (p - 1)) ≤ n := Nat.div_mul_le_self _ _
  have h2 : p ≤ 2 * (p - 1) := by omega
  calc n / (p ^ i * (p - 1)) * p ^ (1 + i)
      = n / (p ^ i * (p - 1)) * p ^ i * p := by rw [pow_add, pow_one]; ring
    _ ≤ n / (p ^ i * (p - 1)) * p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 * (n / (p ^ i * (p - 1)) * (p ^ i * (p - 1))) := by ring
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1

theorem minkowski_divisor_bound : Minkowski_div := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2 * n) < 2 * n + 2 :=
    lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  rw [padicValNat_factorial hlog]
  calc ∑ i ∈ range (n + 1), n / (p ^ i * (p - 1))
      ≤ ∑ i ∈ range (n + 1), 2 * n / p ^ (1 + i) :=
        Finset.sum_le_sum (fun i _ => mink_term n p i hp.two_le)
    _ = ∑ i ∈ Ico 1 (n + 2), 2 * n / p ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]; rfl
    _ ≤ ∑ i ∈ Ico 1 (2 * n + 2), 2 * n / p ^ i := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Ico_subset_Ico le_rfl
        omega

theorem minkowski_log_bound : Minkowski_log := by
  refine ⟨12, ?_⟩
  intro M hM
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hfac : (((4 * M).factorial : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) ^ (4 * M) := by
    exact_mod_cast Nat.factorial_le_pow (4 * M)
  have hfpos : (0 : ℝ) < ((4 * M).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h1 : Real.log ((4 * M).factorial : ℝ) ≤ Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) :=
    Real.log_le_log hfpos hfac
  have h2 : Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) = (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
    rw [Real.log_pow]
    push_cast
    rw [Real.log_mul (by norm_num) hM0.ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMr
  have h6 : Real.log 4 + Real.log M ≤ 3 * Real.log M := by linarith
  calc Real.log ((4 * M).factorial : ℝ) ≤ (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
        rw [← h2]; exact h1
    _ ≤ (4 * (M : ℝ)) * (3 * Real.log M) := mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = 12 * M * Real.log M := by ring

theorem moduli_arithmetic_bound : Ms_arith := by
  intro C₀ hC₀
  refine ⟨8 * Real.log C₀ + 31 + C₀, ?_⟩
  intro f N v T L logg R2 logh hf hN hv hT hL hg hlf hlN hlv hR2 hh
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hC0' : C₀ ≠ 0 := by positivity
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hv' : v ≠ 0 := by positivity
  have hT' : T ≠ 0 := by positivity
  have hlogR : Real.log R2 = Real.log C₀ + Real.log f + 2 * Real.log N + 2 * Real.log v
      + 2 * Real.log T := by
    rw [hR2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hC0' hf', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hR2' : R2 ≠ 0 := by rw [hR2]; positivity
  have hlogCR : Real.log (C₀ * R2) = Real.log C₀ + Real.log R2 := Real.log_mul hC0' hR2'
  set c := Real.log C₀ with hcdef
  set lT := Real.log T with hlTdef
  set X := L + lT + logg with hX
  clear_value X c lT
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ c * X := by nlinarith
  have hA : Real.log R2 ≤ (c + 5) * X := by
    have : Real.log R2 ≤ c + 5 * X := by rw [hlogR]; linarith
    linarith
  have hB : Real.log (C₀ * R2) ≤ (2 * c + 5) * X := by
    rw [hlogCR]; linarith
  have hfN2 : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hP : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 * X := by positivity

  have t1 : (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) := by
    have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith

  have t2 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5)) := by
    have h1 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2)
        ≤ 4 * f * N * ((N : ℝ) + 1) * ((c + 5) * X / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ 2 * (f : ℝ) * ((c + 5) * X) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith

  have t3 : (f : ℝ) * N * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * lT := by
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (f : ℝ) * lT)
    linarith
  have t3' : (f : ℝ) * (N : ℝ) ^ 2 * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * X :=
    mul_le_mul_of_nonneg_left (by linarith) hfN2
  have t4 : C₀ * f * (N : ℝ) ^ 2 * logg ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * C₀ := by
    have := mul_le_mul_of_nonneg_left (by linarith : logg ≤ X)
      (by positivity : 0 ≤ C₀ * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith
  have hsum : logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := by linarith
  calc logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := hsum
    _ = (8 * c + 31 + C₀) * f * (N : ℝ) ^ 2 * X := by ring

end Formalism.HermitianLattices.TraceIntegrality
