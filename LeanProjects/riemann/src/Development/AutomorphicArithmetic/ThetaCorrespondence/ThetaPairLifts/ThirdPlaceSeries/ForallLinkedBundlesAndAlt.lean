import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConstructedAfterLargeBaseCorePropertyOfForall
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.AllAtMember
section large₂
variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
theorem forall_linked_bundles_and_alt {Lk : LkT _root_.GlobalTheory.Fc.BundleCondition} {H H' : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'
end large₂
end GlobalTheory.Fc.AllAtMember
end
