import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_section_boundary : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsSection A L s → IsClosed (bdry s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | exact GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection <;> assumption)
