import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesOfCasselmanWallach
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixRowsAtMemberStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtChoice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowJOnOfRowHPA
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAAtGAtBuilt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHRBUniv
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHTwOfTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfLinkStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LPrjSurjAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowCountsOfLabels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedAtPart
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.AllAtMemberStage0
section large₂
variable {KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop} {Q Q' : V4.Slot}
theorem forall_linked_bundles_and_alt {Lk : LkT _root_.GlobalTheory.Fc.BundleCondition} {H H' : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop}
    (h : Lg1 KP Q Q' fun S => Row S Lk H) (h' : Lg1 KP Q Q' fun S => Row S Lk H') :
    Lg1 KP Q Q' fun S => Row S Lk fun 𝒜 σ => H 𝒜 σ ∧ H' 𝒜 σ :=
  RowL.and (KP := KP) (Q := Q) (Q' := Q') h h'
end large₂
theorem linkR_of_isLinked' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c)
    (h : _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p K β c b) : _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  refine ⟨q, b'.R, w.recPin, ?_⟩
  exact congrArg (fun t : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => (⟨t.1, t.2.1, t.2.2.R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)) e
theorem allRows_of_open0_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesClassification → _root_.GlobalTheory.BigOn.SurjectiveOntoX → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (NN : FamClass → Prop), _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.CovolumeBoundThirdPlaceSeries → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.S0.FunctionalCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L NN) → _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) NN _root_.GlobalTheory.Fc.DefiniteSideCondition := by
  intro hA hSW p1 p2 p3 p4 p5 h3 h4 hL N S Γ NN o hl3 hfun hN
  have six := _root_.GlobalTheory.T.period_entries_tie_and_level_valuations_at_built (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
  have hU := GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hSW
  have loc := _root_.GlobalTheory.LocalRows.lg1_sLp_sO_hTF hSW KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
  exact
    { hn4 := eventually_coreProperty_of_forall fun Q => (R0.classCountBound_paramsLambda_constructedPoints _ Q _).1
      jOn := eventually_coreProperty_mono o.hPA fun Q h => _root_.GlobalTheory.Fc.JOnBundle.row_jOn_of_row_hPA_alt Q _ h
      hInstR := eventually_coreProperty_of_forall fun Q => GlobalTheory.row_hInstR_of_hU hU _ Q _
      aC2 := eventually_coreProperty_of_forall fun Q => ClassTwoEntries.divisionSecondComplement_constructedPoints _ Q _
      aP10 := six.2.2.2.2.2
      aAtG := _root_.GlobalTheory.Fc.row_aAtG_at_built_alt _ rfl _
      aPt0 := six.1
      aPtTw := six.2.1
      aPer0 := six.2.2.1
      aPerTw := six.2.2.2.1
      tie := six.2.2.2.2.1
      hRB := eventually_coreProperty_of_forall fun Q => _root_.GlobalTheory.Fc.R1.row_hRB_univ_alt p1 p2 p3 p4 Q _
      hTw := eventually_coreProperty_mono o.tie fun Q h => _root_.GlobalTheory.Fc.row_hTw_of_tie_alt Q _ h
      hPA := o.hPA
      hLamP := o.hLamP
      hDivG := o.hDivG
      hDcPtG := o.hDcPtG
      selJ := o.selJ
      sLp := loc.1
      sO := loc.2.1
      hServ := _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (_root_.GlobalTheory.T.hServ_of_linkR hA (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _ (_root_.GlobalTheory.Fc.AllAtMemberStage0.linkR_of_isLinked' _))
      zL := eventually_coreProperty_mono o.hPA fun Q h => _root_.GlobalTheory.Fc.R1.ZLAt.zL_of_hPA Q _ h
      hTF := loc.2.2
      c30 := _root_.GlobalTheory.CountRowByName.row_counts_of_labels_alt hSW KPx _ _ _ o.lab
      rRows := eventually_coreProperty_mono (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.hPA o.hDivG) (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.good o.geo))
          (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt hl3 hfun) (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt (_root_.GlobalTheory.Fc.AllAtMemberStage0.forall_linked_bundles_and_alt o.mi o.kap) o.df)))
        fun Q h => _root_.GlobalTheory.Fc.StageZeroRow.row_rRows_stage0_alt p1 p2 p3 p4 p5 h3 h4 Q _
          (h.imp fun _ _ _ t => t.1.1.1) (h.imp fun _ _ _ t => t.1.1.2) (h.imp fun _ _ _ t => t.1.2.1)
          (h.imp fun _ _ _ t => t.1.2.2) (h.imp fun _ _ _ t => t.2.1.1) (h.imp fun _ _ _ t => t.2.1.2)
          (h.imp fun _ _ _ t => t.2.2.1.1) (h.imp fun _ _ _ t => t.2.2.1.2) (h.imp fun _ _ _ t => t.2.2.2)
      nRest := hN }
end GlobalTheory.Fc.AllAtMemberStage0
end
