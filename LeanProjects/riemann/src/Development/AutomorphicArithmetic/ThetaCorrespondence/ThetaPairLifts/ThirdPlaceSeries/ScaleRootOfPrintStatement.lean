import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrintStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScaleRootOfPrint

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_root_of_reciprocity_inputs : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ScaleRootAltBis := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt | exact _root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.scaleRoot_of_hypothesis_alt <;> assumption)
end
