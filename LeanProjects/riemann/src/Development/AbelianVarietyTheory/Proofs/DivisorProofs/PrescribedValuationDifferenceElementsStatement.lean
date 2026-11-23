import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrescribedValuationDifferenceElements
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prescribed_valuation_difference_elements : ∀ (A : Type) [CommRing A] [IsDedekindDomain A] [Finite (ClassGroup A)] (S : Finset (Ideal A))
    (q : Ideal A → ℚ), ∃ (m : ℕ) (a b : A), 0 < m ∧ a ≠ 0 ∧ b ≠ 0 ∧ ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ →
      ∃ na nb : ℕ, a ∈ P ^ na ∧ a ∉ P ^ (na + 1) ∧ b ∈ P ^ nb ∧ b ∉ P ^ (nb + 1) ∧
        ((na : ℚ) - nb = (m : ℚ) * (if P ∈ S then q P else 0)) := by
  first | exact @GlobalTheory.exists_num_den_of_rat_divisor | exact GlobalTheory.exists_num_den_of_rat_divisor | (intros; apply GlobalTheory.exists_num_den_of_rat_divisor <;> assumption)
