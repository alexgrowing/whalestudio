import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibility
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_power_series_evaluation_divisibility : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first | exact @GlobalTheory.MBLow.BddPS.main | exact GlobalTheory.MBLow.BddPS.main | (intros; apply GlobalTheory.MBLow.BddPS.main <;> assumption)
