import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableAbsLogNormSection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_abs_log_norm_section : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (L : LocPot X) (s : X → X → ℂ),
    IsPotential A L → IsSection A L s → ∀ (Y : Type) [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (μ : Y → X), Continuous μ → Measurable fun y => absLogNorm L s (μ y) := by
  first | exact @GlobalTheory.AbsLogNormMeas.measurable_absLogNorm_comp | exact GlobalTheory.AbsLogNormMeas.measurable_absLogNorm_comp | (intros; apply GlobalTheory.AbsLogNormMeas.measurable_absLogNorm_comp <;> assumption)
