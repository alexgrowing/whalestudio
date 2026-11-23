import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SingularValuesSubmatrix
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_values_submatrix : ∀ (p q : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (α : ι ≃ Fin p) (β : κ ≃ Fin q) (B : Matrix (Fin p) (Fin q) ℂ), (Matrix.toEuclideanLin (B.submatrix α β) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι).singularValues = (Matrix.toEuclideanLin B : EuclideanSpace ℂ (Fin q) →ₗ[ℂ] EuclideanSpace ℂ (Fin p)).singularValues := by
  first | exact @GlobalTheory.singularValues_submatrix | exact GlobalTheory.singularValues_submatrix | (intros; apply GlobalTheory.singularValues_submatrix <;> assumption)
