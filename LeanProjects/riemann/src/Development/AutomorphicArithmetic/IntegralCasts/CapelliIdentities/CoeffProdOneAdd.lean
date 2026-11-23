import Mathlib

namespace UpperTheory.Reformulated.B.Qk43

private lemma esymm_zero_deg (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

private lemma esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

open Polynomial in
private lemma coeff_prod_one_add (s : Multiset ℂ) (k : ℕ) :
    (s.map fun r => (1 + C r * X : ℂ[X])).prod.coeff k = s.esymm k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => cases k <;> simp [Multiset.esymm, coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add,
      coeff_C_mul]
    cases k with
    | zero => rw [coeff_X_mul_zero, ih, esymm_zero_deg, esymm_zero_deg, mul_zero, add_zero]
    | succ k => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (j : ℕ) :
    (s + t).esymm j = ∑ a ∈ Finset.range (j + 1), s.esymm a * t.esymm (j - a) := by
  rw [← coeff_prod_one_add, Multiset.map_add, Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

end UpperTheory.Reformulated.B.Qk43
