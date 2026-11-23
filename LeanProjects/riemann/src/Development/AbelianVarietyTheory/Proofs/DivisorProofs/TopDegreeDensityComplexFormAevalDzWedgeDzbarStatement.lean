import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityComplexFormAevalDzWedgeDzbar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar : ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ), dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  first | exact @GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | exact GlobalTheory.ChernCalc.DensTop.dens_aeval_sym | (intros; apply GlobalTheory.ChernCalc.DensTop.dens_aeval_sym <;> assumption)
