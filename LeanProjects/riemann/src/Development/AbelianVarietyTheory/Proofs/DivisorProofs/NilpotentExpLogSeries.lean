import Mathlib

open Polynomial Finset

namespace GlobalTheory.NilpExpLog

noncomputable def logPoly (D : ℕ) : ℚ[X] :=
  ∑ j ∈ range D, C ((-1 : ℚ) ^ j / ((j : ℚ) + 1)) * X ^ (j + 1)

noncomputable def expPoly (D : ℕ) : ℚ[X] :=
  ∑ i ∈ range D, C ((i.factorial : ℚ)⁻¹) * X ^ i

theorem X_dvd_logPoly (D : ℕ) : (X : ℚ[X]) ∣ logPoly D :=
  dvd_sum fun j _ => dvd_mul_of_dvd_right (dvd_pow_self X (Nat.succ_ne_zero j)) _

theorem derivative_expPoly (N : ℕ) :
    derivative (expPoly (N + 1)) = expPoly (N + 1) - C ((N.factorial : ℚ)⁻¹) * X ^ N := by
  have h1 : expPoly (N + 1) = expPoly N + C ((N.factorial : ℚ)⁻¹) * X ^ N := by
    rw [expPoly, sum_range_succ]; rfl
  rw [h1, add_sub_cancel_right, ← h1, expPoly, sum_range_succ', derivative_add, derivative_sum]
  simp only [derivative_C_mul_X_pow, pow_zero, mul_one, derivative_C, add_zero]
  rw [expPoly]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_cancel]
  congr 2
  rw [Nat.factorial_succ]; push_cast
  field_simp

theorem derivative_logPoly (D : ℕ) :
    derivative (logPoly D) = ∑ j ∈ range D, (-X : ℚ[X]) ^ j := by
  rw [logPoly, derivative_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, neg_pow (X : ℚ[X]) j,
    show ((-1 : ℚ[X])) ^ j = C ((-1 : ℚ) ^ j) by simp]
  · congr 2
    push_cast
    field_simp

theorem one_add_X_mul_derivative_logPoly (D : ℕ) :
    (1 + X) * derivative (logPoly D) = 1 - (-X : ℚ[X]) ^ D := by
  rw [derivative_logPoly]
  have := geom_sum_mul (-X : ℚ[X]) D
  linear_combination (-1 : ℚ[X]) * this

theorem X_pow_dvd_expPoly_comp_logPoly_sub (N : ℕ) :
    (X : ℚ[X]) ^ (N + 1) ∣ (expPoly (N + 1)).comp (logPoly (N + 1)) - (1 + X) := by
  set p := logPoly (N + 1) with hp
  set q := (expPoly (N + 1)).comp p with hqdef
  set c : ℚ[X] := C ((N.factorial : ℚ)⁻¹) with hc
  have hq' : derivative q = derivative p * (q - c * p ^ N) := by
    rw [hqdef, derivative_comp, derivative_expPoly, sub_comp, mul_comp, C_comp, X_pow_comp]
  have hX : (X : ℚ[X]) ∣ p := X_dvd_logPoly _
  have h2 := one_add_X_mul_derivative_logPoly (N + 1)
  rw [← hp] at h2
  have hQ : (X : ℚ[X]) ^ N ∣ (1 + X) * derivative (q - (1 + X)) - (q - (1 + X)) := by
    have e : (1 + X) * derivative (q - (1 + X)) - (q - (1 + X)) =
        -((-X) ^ (N + 1) * (q - c * p ^ N)) - c * p ^ N := by
      rw [derivative_sub, hq', derivative_add, derivative_one, derivative_X]
      linear_combination (q - c * p ^ N) * h2
    rw [e]
    refine dvd_sub (dvd_neg.mpr (dvd_mul_of_dvd_left ?_ _)) (dvd_mul_of_dvd_right ?_ _)
    · rw [neg_pow]; exact dvd_mul_of_dvd_right (pow_dvd_pow X (Nat.le_succ N)) _
    · exact pow_dvd_pow_of_dvd hX N
  set r := q - (1 + X) with hr
  have hr0 : r.coeff 0 = 0 := by
    obtain ⟨p0, hp0⟩ := hX
    have he : (expPoly (N + 1)).eval 0 = 1 := by
      rw [expPoly, eval_finset_sum, sum_range_succ']
      simp
    rw [coeff_zero_eq_eval_zero, hr, hqdef, eval_sub, eval_comp, hp0, eval_mul, eval_X, zero_mul, he]
    simp
  have hind : ∀ k, k ≤ N → r.coeff k = 0 := by
    intro k
    induction k with
    | zero => intro _; exact hr0
    | succ k ih =>
      intro hk
      have hk' := ih (by omega)
      have h0 := (X_pow_dvd_iff.mp hQ) k (by omega)
      rw [coeff_sub, add_mul, one_mul, coeff_add, coeff_derivative, hk', sub_zero] at h0
      have hXr : ((X : ℚ[X]) * derivative r).coeff k = 0 := by
        rcases k with _ | k
        · exact coeff_X_mul_zero _
        · rw [coeff_X_mul, coeff_derivative, hk', zero_mul]
      rw [hXr, add_zero] at h0
      have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h0).resolve_right (by exact_mod_cast hne)
  exact X_pow_dvd_iff.mpr fun d hd => hind d (by omega)

theorem exp_truncLog_one_add : ∀ (A : Type) [Ring A] [Algebra ℚ A] (D : ℕ) (n : A), n ^ D = 0 →
    IsNilpotent.exp (∑ j ∈ Finset.range D, ((-1 : ℚ) ^ j / ((j : ℚ) + 1)) • n ^ (j + 1)) = 1 + n := by
  intro A _ _ D n h
  rcases D with _ | N
  · have : Subsingleton A := subsingleton_of_zero_eq_one (by simpa using h.symm)
    exact Subsingleton.elim _ _
  have hvan : ∀ f : ℚ[X], X ^ (N + 1) ∣ f → aeval n f = 0 := by
    rintro f ⟨g, rfl⟩
    rw [map_mul, map_pow, aeval_X, h, zero_mul]
  have hS : aeval n (logPoly (N + 1)) =
      ∑ j ∈ Finset.range (N + 1), ((-1 : ℚ) ^ j / ((j : ℚ) + 1)) • n ^ (j + 1) := by
    rw [logPoly, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]
  have hpow : (aeval n (logPoly (N + 1))) ^ (N + 1) = 0 := by
    rw [← map_pow]; exact hvan _ (pow_dvd_pow_of_dvd (X_dvd_logPoly _) _)
  rw [← hS, IsNilpotent.exp_eq_sum hpow]
  have hE : aeval n ((expPoly (N + 1)).comp (logPoly (N + 1))) =
      ∑ i ∈ range (N + 1), ((i.factorial : ℚ))⁻¹ • (aeval n (logPoly (N + 1))) ^ i := by
    rw [aeval_comp, expPoly, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]
  rw [← hE]
  have h3 := hvan _ (X_pow_dvd_expPoly_comp_logPoly_sub N)
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, map_add, map_one, aeval_X]

end GlobalTheory.NilpExpLog
