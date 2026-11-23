import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplifierOfHypotheses
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplifier_of_hypotheses : BranchingSupport.Hyps → GlobalTheory.CellAmp.AmpKF := by
  first | exact @GlobalTheory.AmpOrb.ampKF | exact GlobalTheory.AmpOrb.ampKF | (intros; apply GlobalTheory.AmpOrb.ampKF <;> assumption)
