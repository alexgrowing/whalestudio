import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open Formalism.MainNotions.S Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsSqIntOn ε σ → ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d := by
  first | exact @GlobalTheory.schur_orthogonality_unitary | exact GlobalTheory.schur_orthogonality_unitary | (intros; apply GlobalTheory.schur_orthogonality_unitary <;> assumption)
