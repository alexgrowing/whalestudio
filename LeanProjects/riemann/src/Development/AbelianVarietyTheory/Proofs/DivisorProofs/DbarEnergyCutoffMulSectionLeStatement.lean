import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyCutoffMulSectionLe
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.n1_cutoff_mul_section_le_lintegral : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (χ : Y → ℝ), A.SmoothFn χ → ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (W Z : Set Y) (h : ι → Y → ℂ), IsOpen W → tsupport χ ⊆ W → A.IsSecOn (A.kap + la) W h → MeasurableSet Z → (∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y) → n1 C la (fun i y => (χ y : ℂ) * h i y) ≤ ENNReal.ofReal K * ∫⁻ y in Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + la) h y) ∂A.mu := by
  first | exact @GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | exact GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le | (intros; apply GlobalTheory.CutEnergy.dbarEnergy_cutoff_mul_section_le <;> assumption)
