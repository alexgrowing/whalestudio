import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latSmallGen' : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | exact _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt <;> assumption)
end
