import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtSubOfNotLcAt
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x → ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  first | exact @GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | exact GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | (intros; apply GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt <;> assumption)
