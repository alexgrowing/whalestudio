import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CanonicalAnalyticData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXColumns
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolKap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocVolPrim
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealObjClosed
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataKppVol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataVolumesS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTied

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.L2.SG.NGAnalytic.MassDataLemmas

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepChoiceDataC_of_leaves
    (hSW : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
      Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
        Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInf : OnTied fun _ X _ _ u u' _ _ => Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  exact stepChoiceDataC_of
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ => level_s_at_instance X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ => MassDataX.inMassesAt_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ => MassDataX.inColumnsAt_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ => MassDataX.inIndicesAt_holds X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ =>
      volumes_s_at_instance hSW X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    (fun _ _ _ _ _ _ _ _ _ _ X Y u u' _ hb X0 _ _ => kpp_volume_at_instance X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 _ _)
    hTy hPC
    (fun _ _ _ _ _ _ _ _ _ _ X _ u u' _ _ _ _ _ =>
      ⟨LocVolPrim.primX X u locFramePrim, LocVolPrim.primX X u' locFramePrim⟩)
    (fun _ _ _ _ _ _ _ _ _ _ X _ u u' _ hb _ _ _ => Formalism.L2.SG.LocVolKap.kapX (X := X) hb u u')
    (fun Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT =>
      ⟨Formalism.L2.SG.RealObj.InfCut.inNuX X u u' 1, hInf Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT⟩)
    hPos hFV

theorem stepChoiceDataC_of_leavesG
    (hSW : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
      Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ∧
        Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hTy : OnTied fun D X hb Y u u' X0 ψ =>
      InTypedC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u)
        (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) Y.M Y.δ (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0))
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1)
    (hPos : OnTied fun _ X hb Y u u' X0 ψ => (bk0 X hb Y u u' X0 ψ).Pos)
    (hFV : OnTied fun D X hb Y u u' X0 ψ =>
      FrameVolAt X hb Y u u' X0 ψ 0 0 1 (F0 := X.Fu u) (what₂ := Y.what₂ u) (fun _ => 0)
        (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D) (fun _ => idx0 D) (fun _ => 0)) :
    StepChoiceConstantsC := by
  intro Cg cb Cw cT CT C0
  obtain ⟨Cgs, CTs, -, -, s₀, t₀, hS⟩ := sizes_of_hypotheses Cg cb Cw cT CT C0
  refine ⟨max s₀ 29, max t₀ 16, fun C' Cl h1 h2 D large₂ X Y u u' hc hb X0 ψ hT => ?_⟩
  obtain ⟨-, -, hrd, -, hg, -⟩ := hS C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc
  have hGap : Formalism.L2.SG.ConcreteSettingExists.GapHyp D :=
    Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hc.1.1 (le_trans (le_max_right _ _) h2) (le_trans (le_max_right _ _) h1)
  have e := fun {P} (h : OnTied P) => h Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' hc hb X0 ψ hT
  exact ⟨0, 0, 1, X.Fu u, Y.what₂ u, fun _ => 0, pairSys0 u u' (X.Fu u) (Y.what₂ u), fun _ => idx0 D,
    fun _ => idx0 D, fun _ => 0,
    massDataValid_bk_of X hb Y u u' X0 ψ 0 0 1 (fun _ => 0) (pairSys0 u u' (X.Fu u) (Y.what₂ u)) (fun _ => idx0 D)
      (fun _ => idx0 D) (fun _ => 0) hc hrd (by linarith) hT (level_s_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inMassesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inColumnsAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (Formalism.L2.SG.Pf.MassDataX.inIndicesAt_holds X hb Y.hK _ _ u u' X0 _ _)
      (volumes_s_at_instance hSW X hb Y.hK _ _ u u' X0 _ _) (kpp_volume_at_instance X hb Y.hK _ _ u u' X0 _ _)
      (e hTy) (e hPC) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
      (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim) (Formalism.L2.SG.LocVolKap.kapX X hb u u')
      (Formalism.L2.SG.Pf.realObj_inNuX X u u' 1) (hInfG D X u u' hGap) (e hPos) (e hFV)⟩

theorem choice_massData (hSW : PI.VolStabS.MassDataS.SWXS)
    (hPC : OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ)
    (hInfG : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
      Formalism.L2.SG.RealObj.InInfinityX X u u' 1) :
    StepChoiceConstantsC := by
  exact stepChoiceDataC_of_leavesG hSW MassDataX.nTy_holds hPC hInfG (MassDataX.nPos_of hSW hPC) (MassDataX.frameVolAt_of_prodConv hPC)

end Formalism.L2.SG.Pf
