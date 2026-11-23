import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormsOfArchimedeanStatementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
