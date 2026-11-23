import Formalism.GrowthSums.StatementA

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem factorial_add_prod (m k : ℕ) :
    (((m + k).factorial : ℕ) : ℚ) =
      (m.factorial : ℚ) * (k.factorial : ℚ) * ∏ y ∈ Ico 1 (k + 1), (1 + (m : ℚ) / y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, Nat.factorial_succ (m + k), Nat.factorial_succ k,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    rw [ih]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem coarseUnit_succ (P n : ℕ) (hP : 1 ≤ P) :
    coarseUnit P (n + 1) = coarseUnit P n * ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * n / y) := by
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  have key := factorial_add_prod (P * n) P
  push_cast at key
  rw [Finset.prod_Ico_succ_top hP, mul_div_cancel_left₀ _ hPq] at key
  have hfP : (P.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero P
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  unfold coarseUnit
  rw [show P * (n + 1) = P * n + P by ring, key, Nat.factorial_succ n]
  push_cast
  field_simp
  ring

theorem blockFactorialQuotientProd : CoarseUnitProd := by
  intro P n hP
  induction n with
  | zero => simp [coarseUnit]
  | succ n ih => rw [coarseUnit_succ P n hP, ih, Finset.prod_range_succ]

end Formalism.GrowthSums
