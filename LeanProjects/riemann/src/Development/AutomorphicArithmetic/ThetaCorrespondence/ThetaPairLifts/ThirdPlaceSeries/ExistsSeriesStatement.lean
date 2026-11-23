import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseUpperBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSeries

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLe_of_cuspRapidDecay_artin_rayClassField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → _root_.GlobalTheory.BigOn.Exp.BaseUpperBound₂ := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | exact _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field | (intros; apply _root_.GlobalTheory.BigOn.Exp.baseLe_of_cusp_decay_and_ray_class_field <;> assumption)
end
