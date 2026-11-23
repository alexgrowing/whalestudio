import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_posDef_properties : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  first | exact @GlobalTheory.ChernCalc.ldPart_posDef_spec | exact GlobalTheory.ChernCalc.ldPart_posDef_spec | (intros; apply GlobalTheory.ChernCalc.ldPart_posDef_spec <;> assumption)
