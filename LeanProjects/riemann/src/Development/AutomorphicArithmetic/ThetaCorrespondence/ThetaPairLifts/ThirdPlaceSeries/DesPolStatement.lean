import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimateStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DesPol

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_descent_estimate' : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.desPol_alt | exact _root_.GlobalTheory.BigTop.Fun.desPol_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.desPol_alt <;> assumption)
end
