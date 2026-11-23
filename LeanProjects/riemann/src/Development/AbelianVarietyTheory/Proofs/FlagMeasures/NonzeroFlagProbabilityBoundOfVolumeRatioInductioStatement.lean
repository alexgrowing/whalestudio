import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonzeroFlagProbabilityBoundOfVolumeRatioInductio
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroFlagProbabilityBound_of_volumeRatioInduction : VolumeStep → NonzeroFlagBound := by
  first | exact @GlobalTheory.NonzeroFlag.nonzeroFlagBound | exact GlobalTheory.NonzeroFlag.nonzeroFlagBound | (intros; apply GlobalTheory.NonzeroFlag.nonzeroFlagBound <;> assumption)
