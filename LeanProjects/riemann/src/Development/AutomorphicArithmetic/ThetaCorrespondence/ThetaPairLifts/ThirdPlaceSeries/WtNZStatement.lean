import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ

set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_weight_numerator : _root_.GlobalTheory.CovTop.LiftWeightNumerator := by
  first | exact @_root_.GlobalTheory.CovTop.WtShape.wtN_z | exact _root_.GlobalTheory.CovTop.WtShape.wtN_z | (intros; apply _root_.GlobalTheory.CovTop.WtShape.wtN_z <;> assumption)
end
