import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinset
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (T : Finset Y) (G : La), ∃ k0 : ℕ, ∀ k ≥ k0, ∃ (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (a : ι → Y → ℂ), A.IsSec (A.kap + k • H) t0 ∧ (∀ j, A.IsSec (A.kap + k • H) (t j)) ∧ A.IsSec (A.kap + (G + k • H)) a ∧ ∀ P ∈ T, t0 (A.pick P) P ≠ 0 ∧ A.IsCoordAt t0 t P ∧ a (A.pick P) P ≠ 0 := by
  first | exact @GlobalTheory.sections_coords_and_nonvanishing_at_finset | exact GlobalTheory.sections_coords_and_nonvanishing_at_finset | (intros; apply GlobalTheory.sections_coords_and_nonvanishing_at_finset <;> assumption)
