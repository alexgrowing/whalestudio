import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density : ∀ {n : ℕ} {Y : Type} [TopologicalSpace Y] (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ}, IsOpen S → (∀ y ∈ S, y ∈ e.source → ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) → AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  first | exact @GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | exact GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | (intros; apply GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous <;> assumption)
