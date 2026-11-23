import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelectionClosedOfWuDecay
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefiniteRealisationChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinXRowOfGap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibilityClosed
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVRecBridgeSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Top.selection_closed_of_wu_decay_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH), Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  intro 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have jGap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm,
      _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
    (Formalism.L2.SG.GapClosed.gapEv_closed_of (D3 3 𝒜) fun _ hc => hc.2.2.1).imp fun Fm _ _ h hc => by
      obtain ⟨y, hy⟩ := h hc
      exact ⟨y, fun x _ _ hxy i => hy x hxy i⟩
  have hM : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection (fun Fm hc => sel Fm (d3_a hc)) Fm hc fun x hx h i =>
      _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx h i) :=
    rRows.imp fun Fm CH _ h hc => by
      obtain ⟨C, _, x0, H⟩ := h hc
      exact ⟨x0, fun x hx hs hx0 i => (H x hx hs hx0 i).1.miStar⟩
  have hFX := _root_.Formalism.L2.SG.JoinSISel.closed_finX_of_gapHyp (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
    (selS := fun Fm hc => selS Fm (d3_a hc)) (Formalism.L2.SG.Pf.finXC_of hWu hRF)
    jGap
  have hC5 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm :=
    _root_.Formalism.L2.SG.JoinSISel.complementFive_closed_of_image_v0 (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
      (selS := fun Fm hc => selS Fm (d3_a hc)) (selP := fun Fm hc => selP Fm (d3_a hc)) (selDH := fun Fm hc => selDH Fm (d3_a hc))
      (selC := fun Fm hc => selC Fm (d3_a hc)) (selK := fun Fm hc => (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) Fm (d3_a hc)) (selI := fun Fm hc => (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc))
      (fun Fm hc => selJ Fm (d3_a hc)) hM hFX jOn
  exact hC5
end
