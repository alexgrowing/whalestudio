import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderUnipotentAutDivisiblePrimaryEqId
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteOrder_unipotent_aut_divisible_primary_eq_id : ∀ (A : Type) [AddCommGroup A] (β : A →+ A) (n g r m : ℕ), 0 < n → (∀ x : A, β^[n] x = x) → g.Prime → r + 2 ≤ g → (∀ x : A, ∃ y : A, g • y = x) → (∀ x : A, ∃ j : ℕ, g ^ j • x = 0) → (∃ T : Finset A, T.card ≤ g ^ r ∧ ∀ x : A, g • x = 0 → x ∈ T) → (∀ x : A, g • x = 0 → (fun z => β z - z)^[m] x = 0) → ∀ x : A, β x = x := by
  first | exact @GlobalTheory.finite_order_unipotent_eq_id | exact GlobalTheory.finite_order_unipotent_eq_id | (intros; apply GlobalTheory.finite_order_unipotent_eq_id <;> assumption)
