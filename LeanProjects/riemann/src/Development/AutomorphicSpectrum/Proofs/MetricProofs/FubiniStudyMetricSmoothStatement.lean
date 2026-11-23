import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_study_metric_smooth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℤ), IsSmoothHerm (fsHerm ι a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm <;> assumption)
