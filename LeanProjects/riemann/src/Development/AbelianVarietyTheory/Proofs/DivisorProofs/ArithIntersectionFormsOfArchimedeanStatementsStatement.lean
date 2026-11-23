import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatements
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  first | exact @GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | exact GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection | (intros; apply GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection <;> assumption)
