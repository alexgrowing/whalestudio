import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMultOneDecayOfLargeGapHypotheses
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 := by
  first | exact @GlobalTheory.Amp.LocalInputsGap.locIn_of_hypGap | exact GlobalTheory.Amp.LocalInputsGap.locIn_of_hypGap | (intros; apply GlobalTheory.Amp.LocalInputsGap.locIn_of_hypGap <;> assumption)
