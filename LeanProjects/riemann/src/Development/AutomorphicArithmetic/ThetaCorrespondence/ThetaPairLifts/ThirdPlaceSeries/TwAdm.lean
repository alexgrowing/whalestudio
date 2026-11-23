import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
namespace GlobalTheory.BigOn.Exp.TwAdmProof
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
namespace GlobalTheory.BigOn.Exp.TwAdmProof
variable {D : D7}
end GlobalTheory.BigOn.Exp.TwAdmProof
open GlobalTheory.BigOn.Exp.TwAdmProof in
theorem GlobalTheory.BigOn.Exp.twAdm_alt : _root_.GlobalTheory.BigOn.Exp.TwAdmAlt := by
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    _root_.GlobalTheory.BigTop.EventuallyAtPoints.of_forall fun x hx i p hR _ w hw _ => ?_⟩⟩
  have hmu := (p.tw_iff w).1 hw
  obtain ⟨-, N0, S, hG⟩ := hR.ties.twist
  obtain ⟨-, hall⟩ := hG w hmu
  have h1 := hall 1 (by simp)
  rw [zpow_one] at h1
  have hpsi := h1.1
  refine ⟨?_, ?_, GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ _ (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois w hmu⟩
  · have h2 := Formalism.MainNotions.IntegralHeckeForms.TwOK_psiAt ((Fm.ex x hx i).nch.sd w) (Formalism.MainNotions.IntegralHeckeForms.TwOK_of_PsiOk hpsi)
    rw [psiAt_comp, Formalism.MainNotions.psiAt_psiAt] at h2
    exact h2
  · intro P hP
    obtain ⟨-, hin, he⟩ := hpsi.1 P hP
    exact exists_splitK_of P hin he
end
