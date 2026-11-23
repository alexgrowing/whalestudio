import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EchelonProjectorKernelFrobenius
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.echelon_projector_kernel_frobenius : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
