import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanCovolumeFunction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineLatticeClassMean_covolume_function : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  first | exact @GlobalTheory.FlagBase.MeanCov.latMean_covAt | exact GlobalTheory.FlagBase.MeanCov.latMean_covAt | (intros; apply GlobalTheory.FlagBase.MeanCov.latMean_covAt <;> assumption)
