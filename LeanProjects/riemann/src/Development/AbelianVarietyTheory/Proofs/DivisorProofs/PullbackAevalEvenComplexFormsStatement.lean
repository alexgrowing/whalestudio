import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackAevalEvenComplexForms
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_aeval_evenComplexForms : ∀ (n n' : ℕ) (L : V n →L[ℂ] V n') (κ : Type) (w : κ → Ev n) (w' : κ → Ev n') (P : MvPolynomial κ ℂ), (∀ x, (w x : Alt n) = pull L (w' x : Alt n')) → ((aeval w P : Ev n) : Alt n) = pull L ((aeval w' P : Ev n') : Alt n') := by
  first | exact @GlobalTheory.FlagCell2.pull_aeval_even | exact GlobalTheory.FlagCell2.pull_aeval_even | (intros; apply GlobalTheory.FlagCell2.pull_aeval_even <;> assumption)
