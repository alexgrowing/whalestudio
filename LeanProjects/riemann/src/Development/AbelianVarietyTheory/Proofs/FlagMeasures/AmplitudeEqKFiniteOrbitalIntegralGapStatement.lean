import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 := by
  first | exact @GlobalTheory.AmpOrbGap.ampKF | exact GlobalTheory.AmpOrbGap.ampKF | (intros; apply GlobalTheory.AmpOrbGap.ampKF <;> assumption)
