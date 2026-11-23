import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocityStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjBaseOfSteps

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjBase_of_ray_class_field_and_seriesRat : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.ConjugateBase := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | exact _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity | (intros; apply _root_.GlobalTheory.BigOn.Exp.conjBase_of_cusp_decay_and_reciprocity <;> assumption)
end
