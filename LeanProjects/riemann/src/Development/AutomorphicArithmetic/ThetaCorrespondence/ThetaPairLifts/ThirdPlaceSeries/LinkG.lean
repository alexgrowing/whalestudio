import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.closed_linkG_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkG Fm := by
  intro 𝒜 sel hduty
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hG2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.G.Adm2F Fm :=
    Closed.of_class fun Fm _ hc => admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)
  have hGt : Closed (D3 3 𝒜) fun Fm _ => Formalism.L2.G.GroupCompatibilityFamily Fm :=
    Closed.of_class fun Fm _ hc => _root_.Formalism.L2.group_compatibility_of_second_layer_family Fm (hRec Fm (d3_a hc))
  have lG := Formalism.L2.G.linkG_concrete5 (D3 3 𝒜) hGt hG2
  exact lG
end
end
