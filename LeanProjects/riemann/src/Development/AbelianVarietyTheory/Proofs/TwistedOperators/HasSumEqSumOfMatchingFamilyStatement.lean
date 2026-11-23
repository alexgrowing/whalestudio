import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily
open Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  first | exact @GlobalTheory.hasSum_eq_sum_of_matching_family | exact GlobalTheory.hasSum_eq_sum_of_matching_family | (intros; apply GlobalTheory.hasSum_eq_sum_of_matching_family <;> assumption)
