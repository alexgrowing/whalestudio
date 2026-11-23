import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace : ∀ (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ), m + 1 = n → qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧ ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  first | exact @GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | exact GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | (intros; apply GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal <;> assumption)
