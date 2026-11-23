import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystems
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_joint_eigenvalues_of_commute : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  first | exact @GlobalTheory.finite_joint_eigensystems | exact GlobalTheory.finite_joint_eigensystems | (intros; apply GlobalTheory.finite_joint_eigensystems <;> assumption)
