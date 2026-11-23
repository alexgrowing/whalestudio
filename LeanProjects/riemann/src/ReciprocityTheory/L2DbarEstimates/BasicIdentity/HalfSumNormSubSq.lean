import Mathlib

namespace ReciprocityTheory.L2DbarEstimates.E

open scoped ComplexConjugate

theorem norm_sq_le_split (A B : ℂ) (ep : ℝ) (hep : 0 < ep) :
    ‖A‖ ^ 2 ≤ (1 + ep) * ‖A + B‖ ^ 2 + (1 + 1 / ep) * ‖B‖ ^ 2 := by
  have h1 : ‖A‖ ≤ ‖A + B‖ + ‖B‖ := by
    have := norm_sub_le (A + B) B
    simpa using this
  set x := ‖A + B‖ with hx
  set y := ‖B‖ with hy
  set t := 1 / ep with htdef
  have ht : ep * t = 1 := by rw [htdef]; field_simp
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have key : 2 * x * y ≤ ep * x ^ 2 + t * y ^ 2 := by
    have h := mul_nonneg hep.le (sq_nonneg (x - t * y))
    have e1 : ep * t * x * y = x * y := by rw [ht]; ring
    have e2 : ep * t * t * y ^ 2 = t * y ^ 2 := by rw [ht]; ring
    nlinarith [h, e1, e2]
  have h2 : ‖A‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [h2, key]

theorem norm_sum_mul_sq_le {n : ℕ} (a c : Fin n → ℂ) :
    ‖∑ j, a j * c j‖ ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * c j‖ ≤ ∑ j, ‖c j‖ * ‖a j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, mul_comm]
  have h2 : (∑ j, ‖c j‖ * ‖a j‖) ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem norm_sum_sq_eq {n : ℕ} (a : Fin n → ℂ) :
    ‖∑ j, a j‖ ^ 2 = (∑ j, ∑ k, a j * conj (a k)).re := by
  have h : (∑ j, ∑ k, a j * conj (a k)) = (∑ j, a j) * conj (∑ j, a j) := by
    rw [map_sum, Finset.sum_mul_sum]
  rw [h, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem half_sum_norm_sub_sq {n : ℕ} (a : Fin n → Fin n → ℂ) :
    (∑ j, ∑ k, ‖a j k - a k j‖ ^ 2) / 2 =
      ∑ j, ∑ k, ‖a k j‖ ^ 2 - (∑ j, ∑ k, a k j * conj (a j k)).re := by
  have h : ∀ j k, ‖a j k - a k j‖ ^ 2 =
      ‖a j k‖ ^ 2 + ‖a k j‖ ^ 2 - 2 * (a j k * conj (a k j)).re := by
    intro j k
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_sub]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum]
  have hs : ∑ j, ∑ k, ‖a j k‖ ^ 2 = ∑ j, ∑ k, ‖a k j‖ ^ 2 := Finset.sum_comm
  have hr : ∑ j, ∑ k, (a j k * conj (a k j)).re = ∑ j, ∑ k, (a k j * conj (a j k)).re :=
    Finset.sum_comm
  rw [hs, hr]
  ring

end ReciprocityTheory.L2DbarEstimates.E
