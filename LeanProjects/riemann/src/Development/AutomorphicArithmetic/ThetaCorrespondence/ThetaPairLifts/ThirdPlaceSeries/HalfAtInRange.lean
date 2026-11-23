import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallnessCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HalfLabels
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]
end GlobalTheory.HalfLabels
namespace GlobalTheory.HalfLabels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem halfAt_inRange_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)
end GlobalTheory.HalfLabels
end
end
