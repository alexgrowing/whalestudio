import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianSumStabiliserUnfolding
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianSum_stabiliserUnfolding : GaugeUnfold := by
  first | exact @GlobalTheory.StabUnfold.gaugeUnfold | exact GlobalTheory.StabUnfold.gaugeUnfold | (intros; apply GlobalTheory.StabUnfold.gaugeUnfold <;> assumption)
