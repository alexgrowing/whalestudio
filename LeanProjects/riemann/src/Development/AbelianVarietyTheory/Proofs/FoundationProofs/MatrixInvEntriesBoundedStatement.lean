import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixInvEntriesBounded
import Mathlib
open scoped Matrix
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_inv_entries_of_bounded_entries : ∀ (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ), Continuous G → (∀ c, G c ≠ 0 → IsUnit c) → ∀ B ε : ℝ, 0 < ε → ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  first | exact @GlobalTheory.matrix_inv_entries_bounded | exact GlobalTheory.matrix_inv_entries_bounded | (intros; apply GlobalTheory.matrix_inv_entries_bounded <;> assumption)
