import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OverNEOfNEb
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lg1EntryOfMembership
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.Mem.AtPtTransport
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem overNE_of_NEb_alt {N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) :
    _root_.GlobalTheory.NRows.AtPt.OverNEAlt N :=
  fun K B f T w Z Wt p0 t nch n xd c h => (hN K B f T w Z Wt p0 t nch n xd c h).elim fun x => ⟨x.1⟩
theorem atMem_at_wit_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), WitMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s →
    (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) →
    (∀ p : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun κ D O _ _ => ∃ K : Ctx, κ.Of K ∧ O.L.sc = K.s ∧
      Val K.C K.cD K.ch O.L ∧ ∃ q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K, q.Is D O ∧
        p K q.B q.f q.T q.w q.Z q.x.Wt _ q.x.what₂ _ q.x.n (_root_.GlobalTheory.Mem.Top.Bl.WPt.core_data_of_point (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q)) ∧
    ∀ P : ∀ D : D7, NChoice D → Prop, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL (fun _ _ _ _ w Z _ _ _ nch _ _ => P (w.D Z) nch) →
      _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => RowE Q L fun _ D O _ _ => P D O.ex.nch := by
  intro hL N S Γ H hN
  have hN' := _root_.GlobalTheory.Mem.AtPtTransport.overNE_of_NEb_alt hN
  refine ⟨fun p hp => ?_, fun P hP => ?_⟩
  · refine GlobalTheory.NRows.AtPt.linkedBundleProperty_after_largeBaseCoreProperty (_root_.GlobalTheory.NRows.AtPt.lgSlotG_memSlot' hp _) ?_
    refine RowE.of_all fun κ K β c b hk hβ _ => ?_
    obtain ⟨q, hq, _, hw⟩ := _root_.GlobalTheory.NRows.AtPt.exists_wPt_entC_atWit hN' H β hβ
    exact ⟨K, hk, β.sc, β.p.pt_val β.val, q, hq, hw⟩
  · exact _root_.GlobalTheory.NRows.AtPt.lg1_entry_of_atWit hP hN' H (r := fun D O => P D O.ex.nch) (fun K q _ t => t) _
end GlobalTheory.Mem.AtPtTransport
end
end
