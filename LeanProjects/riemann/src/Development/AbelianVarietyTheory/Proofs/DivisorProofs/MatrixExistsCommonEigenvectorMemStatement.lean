import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExistsCommonEigenvectorMem
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_eigenvector_mem_of_commute : ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Set (Matrix (Fin n) (Fin n) K)), (∀ A ∈ S, ∀ B ∈ S, Commute A B) → ∀ (E : Submodule K (Fin n → K)), E ≠ ⊥ → (∀ A ∈ S, ∀ v ∈ E, A *ᵥ v ∈ E) → ∃ v ∈ E, v ≠ 0 ∧ ∀ A ∈ S, ∃ μ : K, A *ᵥ v = μ • v := by
  first | exact @GlobalTheory.matrix_exists_common_eigenvector_mem | exact GlobalTheory.matrix_exists_common_eigenvector_mem | (intros; apply GlobalTheory.matrix_exists_common_eigenvector_mem <;> assumption)
