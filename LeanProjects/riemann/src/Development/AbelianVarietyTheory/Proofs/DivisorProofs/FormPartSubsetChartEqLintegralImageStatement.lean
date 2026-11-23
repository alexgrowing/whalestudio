import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormPartSubsetChartEqLintegralImage
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formPart_subset_chart_eq_lintegral_image : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (β : A.Fld), A.IsForm β → ∀ (s : ℤˣ) (i : A.ι) (T : Set M), MeasurableSet T → T ⊆ (A.e i).source → A.part β s T = ∫⁻ v in A.e i '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens (A.loc β i v)).re) := by
  first | exact @GlobalTheory.FlagCell2.part_subset_chart | exact GlobalTheory.FlagCell2.part_subset_chart | (intros; apply GlobalTheory.FlagCell2.part_subset_chart <;> assumption)
