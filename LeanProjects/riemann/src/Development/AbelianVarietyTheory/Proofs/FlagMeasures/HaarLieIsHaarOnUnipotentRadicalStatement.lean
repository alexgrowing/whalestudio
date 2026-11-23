import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarLie_isHaarOn_unipotentRadical : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ → IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := by
  first | exact @GlobalTheory.haarLie_isHaarOn_Nset | exact GlobalTheory.haarLie_isHaarOn_Nset | (intros; apply GlobalTheory.haarLie_isHaarOn_Nset <;> assumption)
