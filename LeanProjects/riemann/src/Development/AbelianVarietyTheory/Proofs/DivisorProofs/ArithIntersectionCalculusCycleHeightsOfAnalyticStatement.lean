import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic : ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := by
  first | exact @GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | exact GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic | (intros; apply GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic <;> assumption)
