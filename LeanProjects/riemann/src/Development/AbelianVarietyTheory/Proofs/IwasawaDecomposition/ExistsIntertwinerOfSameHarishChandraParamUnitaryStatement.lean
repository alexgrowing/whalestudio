import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_same_harishChandraParam_unitary : ∀ (k : ℕ) (u : Fin k → ℝ) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁)) (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), Formalism.MainNotions.S.IsHCTypeU k u π₁ → Formalism.MainNotions.S.IsHCTypeU k u π₂ → ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  first | exact @GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | exact GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU | (intros; apply GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU <;> assumption)
