import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentHaarMeasure_ratio : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  first | exact @GlobalTheory.ThA.exists_isRatioN | exact GlobalTheory.ThA.exists_isRatioN | (intros; apply GlobalTheory.ThA.exists_isRatioN <;> assumption)
