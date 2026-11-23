import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NullSetImageUnderHoloMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_set_image_under_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y), HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | exact GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.NullImage.isNull_image_of_holoMap <;> assumption)
