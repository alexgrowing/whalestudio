import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatio
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio : VolumeStep → FlagMeasureBound := by
  first | exact @GlobalTheory.FlagMeas.Bound.flagMeasureBound | exact GlobalTheory.FlagMeas.Bound.flagMeasureBound | (intros; apply GlobalTheory.FlagMeas.Bound.flagMeasureBound <;> assumption)
