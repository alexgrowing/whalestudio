import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBoundedLocallyIntegrable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_bounded_locally_integrable : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ (u : X → ℝ) (C : ℝ), A.SmoothOn Zᶜ u → (∀ x, x ∉ Z → |u x| ≤ C * Real.log (r x)) → ∀ j, MeasureTheory.LocallyIntegrableOn (u ∘ (A.chart j).symm) (A.chart j).target MeasureTheory.volume := by
  first | exact @GlobalTheory.Mean4O.locallyIntegrableOn_of_log_bound | exact GlobalTheory.Mean4O.locallyIntegrableOn_of_log_bound | (intros; apply GlobalTheory.Mean4O.locallyIntegrableOn_of_log_bound <;> assumption)
