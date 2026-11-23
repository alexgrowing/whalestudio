import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTestDivisorsKltLcPencilBoundaries
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_test_divisors_klt_lc_pencil_boundaries : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G D₀ : CartierDiv X), η ≠ 0 → 0 < m → ∃ S : Set (DivOver p), S.Finite ∧ ∀ (x : X) (g f : X.functionFieldˣ) (c : ℚ), G.IsEqn x g → D₀.IsEqn x f → ((∀ E ∈ S, E.Through x → -1 < discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 < discrep E η m g - c * E.ord f) ∧ ((∀ E ∈ S, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) → ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g - c * E.ord f) := by
  first | exact @GlobalTheory.PairStep.finite_test_divisors | exact GlobalTheory.PairStep.finite_test_divisors | (intros; apply GlobalTheory.PairStep.finite_test_divisors <;> assumption)
