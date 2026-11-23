import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparabilityElementOfTraceNondegenerate
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separability_element_of_trace_nondegenerate' : ∀ (A : Type) [Ring A] [Module.Free ℤ A] [Module.Finite ℤ A], (∀ x : A, (∀ y : A, LinearMap.trace ℤ A (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0) → ∃ (N : ℤ) (k : ℕ) (x y : Fin k → A), N ≠ 0 ∧ ∑ j, x j * y j = (N : A) ∧ ∀ c : A, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c) := by
  first | exact @GlobalTheory.exists_separability_element_of_trace_nondegenerate | exact GlobalTheory.exists_separability_element_of_trace_nondegenerate | (intros; apply GlobalTheory.exists_separability_element_of_trace_nondegenerate <;> assumption)
