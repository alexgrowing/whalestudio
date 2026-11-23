import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSet
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_psi_chart_of_not_mem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  first | exact @GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | exact GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet | (intros; apply GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet <;> assumption)
