import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn : ∀ k r : ℕ, IsHaarOn (Nset k r) (lebN k r) := by
  first | exact @GlobalTheory.Amp.NHaar.isHaarOn_lebN | exact GlobalTheory.Amp.NHaar.isHaarOn_lebN | (intros; apply GlobalTheory.Amp.NHaar.isHaarOn_lebN <;> assumption)
