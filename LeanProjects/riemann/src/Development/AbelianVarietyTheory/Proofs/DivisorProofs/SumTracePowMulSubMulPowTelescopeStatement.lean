import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTracePowMulSubMulPowTelescope
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_trace_pow_mul_sub_mul_pow_telescope : ∀ (R : Type) [CommRing R] (r : Type) [Fintype r] [DecidableEq r] (P Q : Matrix r r R) (k : ℕ), ∑ i ∈ Finset.range k, (P ^ i * (P - Q) * Q ^ (k - 1 - i)).trace = (P ^ k).trace - (Q ^ k).trace := by
  first | exact @GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow | exact GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow | (intros; apply GlobalTheory.ChernCalc.sum_trace_pow_mul_sub_mul_pow <;> assumption)
