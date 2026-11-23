import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem linFunctional_translate_pow_firstOrder_eq_zero (σ : Type) (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
    (L P : MvPolynomial σ ℝ) (m : ℕ)
    (h : ∀ t : ℤ, Φ ((L + C (t : ℝ) * P) ^ (m + 1)) = Φ (L ^ (m + 1))) :
    Φ (P * L ^ m) = 0 := by
  classical
  set a : ℕ → ℝ := fun k => ((m + 1).choose k : ℝ) * Φ (P ^ k * L ^ (m + 1 - k)) with ha
  set q : Polynomial ℝ := ∑ k ∈ Finset.range (m + 2), Polynomial.C (a k) * Polynomial.X ^ k with hq
  have heval : ∀ t : ℝ, q.eval t = Φ ((L + C t * P) ^ (m + 1)) := by
    intro t
    rw [add_comm, add_pow, map_sum, hq, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (C t * P) ^ k * L ^ (m + 1 - k) * ((m + 1).choose k : MvPolynomial σ ℝ)
        = (t ^ k * ((m + 1).choose k : ℝ)) • (P ^ k * L ^ (m + 1 - k)) := by
      rw [← MvPolynomial.C_mul', mul_pow, ← map_pow, map_mul]
      simp only [map_natCast]
      ring
    rw [this, map_smul, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, ha]
    ring
  have hzero : q - Polynomial.C (Φ (L ^ (m + 1))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Int.cast_injective (α := ℝ)))
    rintro _ ⟨t, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, heval, h t,
      sub_self]
  have hc := congrArg (fun p => Polynomial.coeff p 1) hzero
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_zero, hq,
    Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq (Finset.range (m + 2)) 1] at hc
  simp only [Finset.mem_range, show 1 < m + 2 by omega, if_true, one_ne_zero, if_false, sub_zero, ha,
    Nat.choose_one_right, pow_one, Nat.add_sub_cancel] at hc
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  push_cast at hc
  exact (mul_eq_zero.mp hc).resolve_left hm

end GlobalTheory
