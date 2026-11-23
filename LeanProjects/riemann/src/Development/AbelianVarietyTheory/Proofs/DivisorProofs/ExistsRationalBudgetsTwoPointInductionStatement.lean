import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalBudgetsTwoPointInduction
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_budgets_twoPointInduction : ∀ (n r : ℕ) (c : ℕ → ℝ), 0 < r → (∀ e ∈ Finset.Icc 1 n, 0 < c e) → ∑ e ∈ Finset.Icc 1 n, (2 : ℝ) ^ (1 / (e : ℝ)) * e / c e ≤ 1 → ∃ (h : ℕ → ℚ), (∀ e, 0 < h e) ∧ ∑ e ∈ Finset.Icc 1 n, h e < 1 / (r : ℚ) ∧ ∀ e ∈ Finset.Icc 1 n, ∀ t : ℤ, c e ^ e < (t : ℝ) / (r : ℝ) ^ e → 2 * (e : ℚ) ^ e < h e ^ e * t := by
  first | exact @GlobalTheory.PairStep.exists_rat_budgets | exact GlobalTheory.PairStep.exists_rat_budgets | (intros; apply GlobalTheory.PairStep.exists_rat_budgets <;> assumption)
