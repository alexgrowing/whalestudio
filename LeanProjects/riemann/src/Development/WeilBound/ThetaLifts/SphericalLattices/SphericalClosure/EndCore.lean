import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.VacIntZ
import Development.WeilBound.ThetaLifts.Reductions.WeightConstants.ConstOfGood
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitaryDensity.EqTopOfLines
import Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.TraceBlocks
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaBasic
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.PerpZeroOf
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
import Development.WeilBound.ThetaLifts.CartanFactorisation.Cartan
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.SigReOf
import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.LeviDeterminants.EvZero
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixXClosed
import Development.WeilBound.ThetaLifts.WeilDomination.DomWeilOf
import Development.WeilBound.ThetaLifts.SmallCones.ThetaExp
import Development.WeilBound.ThetaLifts.SmallCones.SoZeroAOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SmallAnyOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.EigenKillSet
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SubMemKer
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.KRealAsm
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.VacuumImageIntertwiner
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict
import Development.WeilBound.ThetaLifts.WeilDomination.MatchEx
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.AlphaZeroOf
import Development.WeilBound.ThetaLifts.LatticeBasics.PolDense
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.RealVanishOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchHeisOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SlicePol
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFacOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.TwoStepOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.LocalFieldT2Space
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.PlaContinuous
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ActsOfReads
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ColOpSingle
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.CuspOfLineOfKeys
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConstFin
import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpen
import Development.WeilBound.ThetaLifts.LatticeBasics.HeightGLLe
import Development.WeilBound.ThetaLifts.LatticeBasics.OrthAn
import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInert
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerHalf
import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm

theorem PositivityTheory.Sph.Tr.endAB_sph
    (hSiegelSet : GlobalTheory.Published.SiegelSetUnitary)
    (h_Weil6_ThKG_Tow_WeilEx : PositivityTheory.ThKG.Tow.WeilEx)
    (hKCo : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv)
    (hFinRam : PositivityTheory.ThK.FinRam)
    (hFinSplit : PositivityTheory.ThK.FinSplit)
    (hFinInert : PositivityTheory.ThK.FinInert)
    (h_LieSecond : GlobalTheory.RealLift.LieSecond)
    (h_Weil6_ThKF_ArchLie : PositivityTheory.ThKF.ArchLie)
    (h_SWStd : GlobalTheory.ThK.Dbl.SiegelWeilStd)
    (h_EisBL : GlobalTheory.ThK.Dbl.EisBL) :
    GlobalTheory.ThK.EndA ∧ GlobalTheory.ThK.EndB := by
  have h_Bump : GlobalTheory.ThK.Dbl.Bump := GlobalTheory.ThK.Dbl.bump
  have h_FrameConj : GlobalTheory.ThK.Dbl.FrameConj := (GlobalTheory.ThK.Dbl.frameConj)
  have h_Weil6_ThKEnd_Cusp_VacBar := PositivityTheory.ThKEnd.Cusp.vacBar
  have h_GlobalTheory_ThK_Dbl_LocUnrSplit := GlobalTheory.ThK.Dbl.locUnrSplit
  have h_GlobalTheory_ThK_Dbl_BadFactor : GlobalTheory.ThK.Dbl.BadFactor := GlobalTheory.ThK.Dbl.badFactor_of GlobalTheory.ThK.Dbl.dblX PositivityTheory.ThKG.Tow.stabEx GlobalTheory.ThK.Dbl.vacFix2 h_Bump
  have h_Weil6_ThKEnd_Iwa : PositivityTheory.ThKEnd.Iwa := (PositivityTheory.ThKG.Tow.iwa)
  have h_Weil6_ThKEnd_CTBasic : PositivityTheory.ThKEnd.CTBasic := (PositivityTheory.ThKEnd.Grp.ctBasic)
  have h_Weil6_ThKEnd_LineMove : PositivityTheory.ThKEnd.LineMove := (PositivityTheory.ThKEnd.Grp.lineMove)
  have h_GlobalTheory_ThK_ThetaBasic : GlobalTheory.ThK.ThetaBasic := (PositivityTheory.ThKF0.thetaBasic)
  have h_Weil6_ThKF_ICont : PositivityTheory.ThKF.ICont := (PositivityTheory.ThKEst.iCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKCT_SoStab : PositivityTheory.ThKCT.SoStab := (PositivityTheory.ThKCT.soStab_of)
  have h_Weil6_ThKEnd_IAut : PositivityTheory.ThKEnd.IAut := (PositivityTheory.ThKEnd.Grp.iAut_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_ICont h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKF_ArchOp : PositivityTheory.ThKF.ArchOp := (PositivityTheory.ThKF.A.archOp)
  have h_Weil6_ThKF_PureAct : PositivityTheory.ThKF.PureAct := (PositivityTheory.ThKF.pureAct)
  have h_Weil6_ThKEst_Level : PositivityTheory.ThKEst.Level := (PositivityTheory.ThKEst.level)
  have h_Weil6_ThKEnd_MatchStab : PositivityTheory.ThKEnd.MatchStab := (PositivityTheory.ThKEnd.Grp.matchStab_of h_Weil6_ThKF_ArchOp h_Weil6_ThKF_PureAct h_Weil6_ThKEst_Level h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKF_CartanMove : PositivityTheory.ThKF.CartanMove := (PositivityTheory.ThKF.cartanMove_of h_Weil6_ThKF_ArchOp)
  have h_Weil6_ThKF_CartanConj : PositivityTheory.ThKF.CartanConj := (PositivityTheory.ThKF.cartan_conjugacy_holds)
  have h_Weil6_ThKEst_IInv : PositivityTheory.ThKEst.IInv := (PositivityTheory.ThKEst.iInv_of h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEnd_SigRe : PositivityTheory.ThKEnd.SigRe := (PositivityTheory.ThKEnd.Grp.sigRe_of h_Weil6_ThKF_ArchOp h_Weil6_ThKF_CartanMove h_Weil6_ThKF_CartanConj h_Weil6_ThKEst_IInv h_Weil6_ThKCT_SoStab)
  have h_Weil6_ThKEnd_TowerA2 : PositivityTheory.ThKEnd.TowerCodimensionTwo := (PositivityTheory.ThKG.Tow.towerCodimensionTwo_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKCT_UnipEx : PositivityTheory.ThKCT.UnipEx := (PositivityTheory.ThKCT.unipEx_of)
  have h_Weil6_ThKCT_Low : PositivityTheory.ThKCT.Low := (PositivityTheory.ThKCT.low_of)
  have h_Weil6_ThKG_Tow_PairEx : PositivityTheory.ThKG.Tow.PairEx := (PositivityTheory.ThKG.Tow.pairEx_of PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKEst_TriplePair : PositivityTheory.ThKEst.TriplePair := (PositivityTheory.ThKEst.Sq.triplePair_holds)
  have h_GlobalTheory_ThK_EvZero : GlobalTheory.ThK.EvZero := PositivityTheory.ThKF0.evZero
  have h_Weil6_ThKG_MixW : PositivityTheory.ThKG.MixW := (PositivityTheory.Mix.mixW_closed)
  have h_Weil6_ThKG_MixX : PositivityTheory.ThKG.MixX := (PositivityTheory.Mix.mixX_closed)
  have h_Weil6_Mix_AdelSt : PositivityTheory.Mix.AdelSt := (PositivityTheory.Mix.adelic_estimates_holds)
  have h_GlobalTheory_ThK_EvCone : GlobalTheory.ThK.EvCone := (PositivityTheory.ThKF0.evCone_of_adel h_Weil6_Mix_AdelSt)
  have h_GlobalTheory_ThK_StabEx : GlobalTheory.ThK.StabEx := (PositivityTheory.ThKG.Tow.stabEx)
  have h_Weil6_ThKG_Tow_PlaneHerm : PositivityTheory.ThKG.Tow.PlaneHerm := (PositivityTheory.ThKG.Tow.planeHerm)
  have h_Weil6_ThKEst_GrpTop : PositivityTheory.ThKEst.GrpTop := (PositivityTheory.ThKEst.grpTop_of)
  have h_Weil6_ThKEst_EpsOf : PositivityTheory.ThKEst.EpsOf := (PositivityTheory.ThKEst.epsOf_of)
  have h_GlobalTheory_ThK_WeilConv : GlobalTheory.ThK.WeilConv := (PositivityTheory.ThKEst.weilConv hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEst_DomWeilU : PositivityTheory.ThKEst.DomWeilU := (PositivityTheory.ThKEst.domWeilU hSiegelSet)
  have h_Weil6_ThKEst_DomWeil : PositivityTheory.ThKEst.DomWeil := (PositivityTheory.ThKClose.domWeil_of h_Weil6_ThKEst_DomWeilU)
  have h_Weil6_ThKEst_SoSemiU : PositivityTheory.ThKEst.SoSemiU := (PositivityTheory.ThKEst.soSemiU hSiegelSet)
  have h_Weil6_ThKEst_SoSemi : PositivityTheory.ThKEst.SoSemi := (PositivityTheory.ThKClose.soSemi_of h_Weil6_ThKEst_SoSemiU)
  have h_GlobalTheory_ThK_SoDecay : GlobalTheory.ThK.SoDecay := (PositivityTheory.ThKEst.soDecay hSiegelSet)
  have h_Weil6_ThKEst_FinVolU : PositivityTheory.ThKEst.FinVolU := (PositivityTheory.ThKEst.finVolU)
  have h_Weil6_ThKEst_SoFin : PositivityTheory.ThKEst.SoFin := (PositivityTheory.ThKEst.soFin_of)
  have h_Weil6_ThKCT_Ext : PositivityTheory.ThKCT.Ext := ⟨h_Weil6_ThKG_MixW, h_Weil6_ThKG_MixX, h_GlobalTheory_ThK_ThetaBasic, h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_Weil6_ThKG_Tow_PairEx, h_Weil6_ThKG_Tow_PlaneHerm, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_TriplePair, h_GlobalTheory_ThK_WeilConv, h_Weil6_ThKEst_DomWeil, h_Weil6_ThKEst_SoSemi, h_GlobalTheory_ThK_SoDecay, h_Weil6_ThKEst_FinVolU, h_Weil6_ThKEst_SoFin⟩
  have h_Weil6_ThKG_CTKernel : PositivityTheory.ThKG.CTKernel := (PositivityTheory.ThKCT.Ext.kernel h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_CTFub : PositivityTheory.ThKCT.CTFub := (PositivityTheory.ThKCT.ctFub_of h_Weil6_ThKCT_UnipEx h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKCT_Witt : PositivityTheory.ThKCT.Witt := (PositivityTheory.ThKCT.witt_of)
  have h_Weil6_ThKCT_GenAniso : PositivityTheory.ThKCT.GenAniso := (PositivityTheory.ThKCT.genAniso_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKG_MixW h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKCT_Witt h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKCT_Unfold : PositivityTheory.ThKCT.Unfold := (PositivityTheory.ThKCT.unfold_of)
  have h_Weil6_ThKCT_StabDec : PositivityTheory.ThKCT.StabDec := (PositivityTheory.ThKCT.stabDec_of)
  have h_Weil6_ThKCT_EvAdm : PositivityTheory.ThKCT.EvAdm := (PositivityTheory.ThKCT.evAdm_of)
  have h_Weil6_ThKCT_ThetaExp : PositivityTheory.ThKCT.ThetaExp := (PositivityTheory.ThKCT.thetaExp)
  have h_Weil6_ThKCT_EvUniq : PositivityTheory.ThKCT.EvUniq := (PositivityTheory.ThKCT.evUniq_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_MixAB : PositivityTheory.ThKCT.MixAB := (PositivityTheory.ThKCT.Ker.mixAB_of h_Weil6_ThKG_MixW h_Weil6_ThKG_MixX h_GlobalTheory_ThK_EvZero h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_Slice : PositivityTheory.ThKCT.Slice := (PositivityTheory.ThKCT.slice_of)
  have h_Weil6_ThKCT_SchInt : PositivityTheory.ThKCT.SchInt := (PositivityTheory.ThKCT.schInt)
  have h_Weil6_ThKCT_TateAbs : PositivityTheory.ThKCT.TateAbs := (PositivityTheory.ThKCT.tateAbs)
  have h_Weil6_ThKCT_LineInt : PositivityTheory.ThKCT.LineInt := (PositivityTheory.ThKCT.lineInt_of h_Weil6_ThKCT_Slice h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_TateAbs)
  have h_Weil6_ThKCT_SoEv : PositivityTheory.ThKCT.SoEv := (PositivityTheory.ThKCT.soEv_of' h_Weil6_ThKCT_Low)
  have h_Weil6_ThKCT_ConeB : PositivityTheory.ThKCT.ConeB := (PositivityTheory.ThKCT.coneB_of h_Weil6_ThKCT_Unfold h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_MixAB h_Weil6_ThKCT_LineInt h_Weil6_ThKEst_SoSemi h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SoFin h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoEv)
  have h_Weil6_ThKCT_TwoExp : PositivityTheory.ThKCT.TwoExp := (PositivityTheory.ThKCT.Ker.twoExp_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_SoZeroA_ : PositivityTheory.ThKCT.SoZeroA' := (PositivityTheory.ThKCT.soZeroA'_of' h_Weil6_ThKG_MixX h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_GenSmall : PositivityTheory.ThKCT.GenSmall := (PositivityTheory.ThKCT.genSmall_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKCT_ConeB h_Weil6_ThKCT_TwoExp h_Weil6_ThKCT_MixAB h_Weil6_ThKG_MixW h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_Witt h_Weil6_ThKCT_StabDec h_Weil6_ThKCT_UnipEx h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_GlobalTheory_ThK_SoDecay h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SoFin h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoZeroA_ h_Weil6_ThKCT_SoEv)
  have h_Weil6_ThKCT_KFinData : PositivityTheory.ThKCT.KFinData := PositivityTheory.ThKCT.kFinData_of h_GlobalTheory_ThK_StabEx
  have h_Weil6_ThKCT_IwaEx : PositivityTheory.ThKCT.IwaEx := (PositivityTheory.ThKCT.iwaEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKEnd_Comp_SmallAny : PositivityTheory.ThKEnd.Comp.SmallAny := (PositivityTheory.ThKEnd.Comp.smallAny_of h_Weil6_ThKCT_GenSmall h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone)
  have h_Weil6_ThKF_Unimod : PositivityTheory.ThKF.Unimod := (PositivityTheory.ThKF.unimodularity_holds)
  have h_Weil6_ThKEst_DomSoU : PositivityTheory.ThKEst.DomSoU := (PositivityTheory.ThKEst.domSoU hSiegelSet)
  have h_Weil6_ThKEnd_Comp_SoLower : PositivityTheory.ThKEnd.Comp.SoLower := PositivityTheory.ThKEnd.Comp.SoL.soLower_of h_Weil6_ThKG_MixW
  have h_Weil6_ThKEnd_Comp_SoMove : PositivityTheory.ThKEnd.Comp.SoMove := (PositivityTheory.ThKEnd.Comp.soMove_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_Unimod h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_TriplePair h_Weil6_ThKEnd_Comp_SoLower)
  have h_GlobalTheory_RealLift_LieFirst : GlobalTheory.RealLift.LieFirst := PositivityTheory.RL.lieFirst h_LieSecond
  have h_GlobalTheory_ThK_KReal : GlobalTheory.ThK.KReal := PositivityTheory.KRealA.kReal_of_lie h_LieSecond h_GlobalTheory_RealLift_LieFirst
  have h_Weil6_ThK_FinRam : PositivityTheory.ThK.FinRam := (hFinRam)
  have h_Weil6_ThK_FinSplit : PositivityTheory.ThK.FinSplit := (hFinSplit)
  have h_Weil6_ThK_FinInert : PositivityTheory.ThK.FinInert := (hFinInert)
  have h_GlobalTheory_ThK_KFin : GlobalTheory.ThK.KFin := (PositivityTheory.ThK.kFin_of h_Weil6_ThK_FinRam h_Weil6_ThK_FinSplit h_Weil6_ThK_FinInert)
  have h_Weil6_KCo_DictX : PositivityTheory.KCo.DictX := (PositivityTheory.ThKG.StdDict.dictX)
  have h_Weil6_KCo_SecSt : PositivityTheory.KCo.SecSt := (PositivityTheory.KCo.section_statement)
  have h_Weil6_KCo_DictSt : PositivityTheory.KCo.DictSt := (PositivityTheory.KCo.dictSt_of h_Weil6_KCo_DictX h_Weil6_KCo_SecSt)
  have h_GlobalTheory_ThK_KCoinv : GlobalTheory.ThK.KCoinv := (hKCo h_Weil6_KCo_DictSt)
  have h_GlobalTheory_ThK_MatchEx : GlobalTheory.ThK.MatchEx := (PositivityTheory.ThKClose.matchEx_of h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKEnd_Comp_PolStab : PositivityTheory.ThKEnd.Comp.PolStab := (PositivityTheory.ThKEnd.Comp.polStab_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_MatchEx h_Weil6_ThKEnd_MatchStab)
  have h_Weil6_ThKG_PolDense : PositivityTheory.ThKG.PolDense := (GlobalTheory.ThK.Dbl.polDense)
  have h_GlobalTheory_RealLift_FrameEx : GlobalTheory.RealLift.FrameEx := (PositivityTheory.RL.frameEx)
  have h_GlobalTheory_RealLift_DerEx : GlobalTheory.RealLift.DerEx := (PositivityTheory.RL.derEx)
  have h_GlobalTheory_RealLift_FockEx : GlobalTheory.RealLift.FockEx := (PositivityTheory.RL.fockEx h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_LineEx : GlobalTheory.RealLift.LineEx := (PositivityTheory.RL.lineEx)
  have h_GlobalTheory_RealLift_ActsLaws : GlobalTheory.RealLift.ActsLaws := (PositivityTheory.RL.actsLaws)
  have h_GlobalTheory_RealLift_VacLine : GlobalTheory.RealLift.VacLine := (PositivityTheory.RL.vacLine h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_PolRange : GlobalTheory.RealLift.PolRange := (PositivityTheory.ThKEnd.Comp.PR.polRange_of h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine)
  have h_Weil6_ThKEnd_Comp_RealVanish : PositivityTheory.ThKEnd.Comp.RealVanish := (PositivityTheory.ThKEnd.Comp.realVanish_of h_Weil6_ThKF_ArchOp h_Weil6_ThKG_PolDense h_GlobalTheory_RealLift_FrameEx h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_LineEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst)
  have h_Weil6_ThKEnd_Comp_IZero : PositivityTheory.ThKEnd.Comp.IZero := (PositivityTheory.ThKEnd.Comp.iZero_of h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_Unimod h_Weil6_ThKEst_DomWeil h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_Weil6_ThKEnd_Comp_RealVanish)
  have h_Weil6_ThKEnd_AlphaZero : PositivityTheory.ThKEnd.AlphaZero := (PositivityTheory.ThKEnd.Comp.alphaZero_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_GenAniso h_Weil6_ThKEnd_Comp_SmallAny h_Weil6_ThKEnd_Comp_SoMove h_Weil6_ThKEnd_Comp_PolStab h_Weil6_ThKEnd_Comp_IZero)
  have h_Weil6_ThKCT_ConeA : PositivityTheory.ThKCT.ConeA := (PositivityTheory.ThKCT.coneA_of h_Weil6_ThKCT_Unfold h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_MixAB h_Weil6_ThKCT_LineInt h_Weil6_ThKEst_DomWeil)
  have h_Weil6_ThKCT_GenBig : PositivityTheory.ThKCT.GenBig := (PositivityTheory.ThKCT.genBig_of h_Weil6_ThKG_CTKernel h_Weil6_ThKCT_CTFub h_Weil6_ThKCT_ConeA h_Weil6_ThKG_MixW h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKCT_Witt h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKEnd_Comp_BigAny : PositivityTheory.ThKEnd.Comp.BigAny := (PositivityTheory.ThKEnd.Comp.bigAny_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone)
  have h_Weil6_ThKEnd_BetaZero : PositivityTheory.ThKEnd.BetaZero := (PositivityTheory.ThKEnd.Comp.betaZero_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_GenAniso h_Weil6_ThKEnd_Comp_BigAny h_Weil6_ThKEnd_Comp_IZero)
  have h_GlobalTheory_ThK_ActsEx : GlobalTheory.ThK.ActsEx := (PositivityTheory.ThKF0.actsEx)
  have h_Weil6_ThKF_ArchUniq : PositivityTheory.ThKF.ArchUniq := (PositivityTheory.ThKF.A.archUniq)
  have h_Weil6_Mix_PureSt : PositivityTheory.Mix.PureSt := (PositivityTheory.Mix.pure_tensor_estimates_holds)
  have h_Weil6_ThKG_Loc_Bump_ArchDict : PositivityTheory.ThKG.Loc.Bump.ArchDict := (PositivityTheory.ThKG.Loc.Bump.archDict_of)
  have h_Weil6_ThKG_Loc_Bump_ArchHeis : PositivityTheory.ThKG.Loc.Bump.ArchHeis := (PositivityTheory.ThKG.Loc.Bump.archHeis_of)
  have h_Weil6_ThKG_Loc_Cone_ArchCone : PositivityTheory.ThKG.Loc.Cone.ArchCone := (PositivityTheory.ThKG.Loc.Bump.archCone_of h_Weil6_ThKG_Loc_Bump_ArchDict h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKG_Loc_Bump_ArchHeis h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_FrameEx h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_KFinData)
  have h_Weil6_ThKG_Loc_MeasEx : PositivityTheory.ThKG.Loc.MeasEx := (PositivityTheory.ThKG.Loc.Cone.coneFac_of h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone).1
  have h_Weil6_ThKEnd_Comp_ConeFacA2 : PositivityTheory.ThKEnd.Comp.ConeIntegralFactorisation := (PositivityTheory.ThKG.Loc.Cone.coneFac_of h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone).2.1
  have h_Weil6_ThKEnd_Comp_ConePol : PositivityTheory.ThKEnd.Comp.ConePol := (PositivityTheory.ThKEnd.Comp.conePol_of h_Weil6_ThKG_Loc_MeasEx h_Weil6_ThKEnd_Comp_ConeFacA2)
  have h_Weil6_ThKEnd_AlphaLow : PositivityTheory.ThKEnd.AlphaLow := (PositivityTheory.ThKEnd.Comp.alphaLow_of h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKCT_UnipEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_EvCone h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKCT_KFinData h_Weil6_ThKCT_GenBig h_Weil6_ThKEnd_Comp_SmallAny h_Weil6_ThKEnd_Comp_SoMove h_Weil6_ThKEnd_Comp_PolStab h_Weil6_ThKEnd_Comp_ConePol)
  have h_GlobalTheory_ThK_KDecay : GlobalTheory.ThK.KDecay := (PositivityTheory.ThKEst.kDecay hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEnd_Two_SigMod : PositivityTheory.ThKEnd.Two.SigMod := (PositivityTheory.ThKEnd.Two.sigMod_of h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay)
  have h_GlobalTheory_ThK_SplitEx : GlobalTheory.ThK.SplitEx := (PositivityTheory.ThKCT.splitEx_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenSmall h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_Low h_Weil6_ThKEst_TriplePair)
  have h_Weil6_ThKG_Tow_PlaneSkew : PositivityTheory.ThKG.Tow.PlaneSkew := (PositivityTheory.ThKG.Tow.planeSkew)
  have h_Weil6_ThKEnd_Two_SigSplit : PositivityTheory.ThKEnd.Two.SigSplit := (PositivityTheory.ThKEnd.Two.sigSplit_of h_GlobalTheory_ThK_SplitEx h_Weil6_ThKG_Tow_PlaneSkew h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_CTBasic h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_SigRe)
  have h_Weil6_ThKEnd_TwoStep : PositivityTheory.ThKEnd.TwoStep := (PositivityTheory.ThKEnd.Two.twoStep_of' h_Weil6_ThKEnd_Two_SigMod h_Weil6_ThKEnd_Two_SigSplit h_Weil6_ThKEnd_Iwa h_Weil6_ThKEnd_IAut)
  have h_Weil6_ThKEnd_Cusp_LocThree : PositivityTheory.ThKEnd.Cusp.LocThree := (PositivityTheory.ThKEnd.Cusp.locThree)
  have h_Weil6_ThKEnd_Cusp_Places : PositivityTheory.ThKEnd.Cusp.Places := (PositivityTheory.ThKEnd.Cusp.places)
  have h_Weil6_ThKEnd_Cusp_KeyThree : PositivityTheory.ThKEnd.Cusp.KeyThree := (PositivityTheory.ThKEnd.Cusp.Key.keyThree_of_locThree h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_LocThree h_Weil6_ThKEnd_Cusp_Places)
  have h_Weil6_ThKEnd_Cusp_LocSupp : PositivityTheory.ThKEnd.Cusp.LocSupp := (PositivityTheory.ThKEnd.Cusp.locSupp)
  have h_Weil6_ThKEnd_Cusp_LocTwo : PositivityTheory.ThKEnd.Cusp.LocTwo := (PositivityTheory.ThKEnd.Cusp.locTwo_of h_Weil6_ThKEnd_Cusp_LocSupp)
  have h_Weil6_ThKEnd_Cusp_KeyTwo : PositivityTheory.ThKEnd.Cusp.KeyTwo := (PositivityTheory.ThKEnd.Cusp.Key.keyTwo_of_locTwo_vacBar h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_LocTwo h_Weil6_ThKEnd_Cusp_VacBar h_Weil6_ThKEnd_Cusp_Places)
  have h_Weil6_ThKEnd_CuspOfLine : PositivityTheory.ThKEnd.CuspOfLine := (PositivityTheory.ThKEnd.Cusp.cuspOfLine_of_keys h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay h_Weil6_ThKEnd_IAut h_Weil6_ThKEnd_Cusp_KeyThree h_Weil6_ThKEnd_Cusp_KeyTwo)
  have h_Weil6_ThKEst_SiegelAll : PositivityTheory.ThKEst.SiegelAll := (PositivityTheory.ThKEst.siegelAll_of hSiegelSet)
  have h_GlobalTheory_ThK_Dbl_PolSch : GlobalTheory.ThK.Dbl.PolSch := (GlobalTheory.ThK.Dbl.polSch)
  have h_GlobalTheory_ThK_Dbl_GoodNe : GlobalTheory.ThK.Dbl.GoodNe := (GlobalTheory.ThK.Dbl.goodNe)
  have h_Weil6_ThKEnd_Orth_SigRapid : PositivityTheory.ThKEnd.Orth.SigRapid := (PositivityTheory.ThKEst.sigRapid hSiegelSet h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie)
  have h_GlobalTheory_ThK_Dbl_ConstOfGood : GlobalTheory.ThK.Dbl.ConstOfGood := (PositivityTheory.SA.constOfGood GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds)
  have h_GlobalTheory_ThK_Dbl_LocDist : GlobalTheory.ThK.Dbl.LocDist := (GlobalTheory.ThK.Dbl.locDist)
  have h_Weil6_ThKEnd_Orth_SigThConst : PositivityTheory.ThKEnd.Orth.SigThConst := (PositivityTheory.ThKEnd.Orth.sigThConst_fin h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_KDecay h_Weil6_ThKEst_SoFin h_Weil6_ThKF_Unimod h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_GoodNe h_GlobalTheory_ThK_Dbl_ConstOfGood h_GlobalTheory_ThK_Dbl_LocDist h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKEnd_OrthIso : PositivityTheory.ThKEnd.OrthIso := (PositivityTheory.ThKEnd.Orth.orthIso_fin h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKG_Tow_PlaneHerm h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_FinVolU h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_TriplePair h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoDecay h_Weil6_ThKEst_DomSoU h_Weil6_ThKEst_SoFin h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_GoodNe h_Weil6_ThKEnd_Orth_SigRapid h_Weil6_ThKEnd_Orth_SigThConst)
  have h_GlobalTheory_ThK_Dbl_FinLevel : GlobalTheory.ThK.Dbl.FinLevel := (GlobalTheory.ThK.Dbl.finLevel)
  have h_GlobalTheory_ThK_Dbl_Stab2Cpt : GlobalTheory.ThK.Dbl.Stab2Cpt := (GlobalTheory.ThK.Dbl.stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWAniso : GlobalTheory.ThK.Dbl.SWAniso := (GlobalTheory.ThK.Dbl.siegelWeilAniso_of h_SWStd h_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt).1
  have h_GlobalTheory_ThK_Dbl_EisContinues : GlobalTheory.ThK.Dbl.EisContinues := GlobalTheory.ThK.Dbl.eisContinues_of h_EisBL h_FrameConj
  have h_GlobalTheory_ThK_Dbl_BoxSec : GlobalTheory.ThK.Dbl.BoxSec := (GlobalTheory.ThK.Dbl.boxSec_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFull : GlobalTheory.ThK.Dbl.SWFull := (GlobalTheory.ThK.Dbl.swFull_of h_GlobalTheory_ThK_Dbl_SWAniso h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSec)
  have h_GlobalTheory_ThK_Dbl_DblW : GlobalTheory.ThK.Dbl.DblW := (GlobalTheory.ThK.Dbl.dblW)
  have h_GlobalTheory_ThK_Dbl_HgtEx : GlobalTheory.ThK.Dbl.HgtEx := GlobalTheory.ThK.Dbl.hgtEx_of h_GlobalTheory_ThK_Dbl_Stab2Cpt
  have h_GlobalTheory_ThK_Dbl_HgtInt : GlobalTheory.ThK.Dbl.HgtInt := GlobalTheory.ThK.Dbl.hgtInt_of h_GlobalTheory_ThK_Dbl_Stab2Cpt
  have h_GlobalTheory_ThK_Dbl_OffOpen : GlobalTheory.ThK.Dbl.OffOpen := (GlobalTheory.ThK.Dbl.offOpen)
  have h_GlobalTheory_ThK_Dbl_HtEmb : GlobalTheory.ThK.Dbl.HtEmb := (GlobalTheory.ThK.Dbl.htEmb)
  have h_Weil6_ThKEnd_Grp_UnipUGood : PositivityTheory.ThKEnd.Grp.UnipUGood := (PositivityTheory.ThKEnd.Grp.unipUGood)
  have h_Weil6_ThKEnd_Grp_UnipLine : PositivityTheory.ThKEnd.Grp.UnipLine := (PositivityTheory.ThKEnd.Grp.unipLine)
  have h_GlobalTheory_ThK_Dbl_CptAll : GlobalTheory.ThK.Dbl.CptAll := (GlobalTheory.ThK.Dbl.cptAll_of h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_GlobalTheory_ThK_Dbl_LeviEx : GlobalTheory.ThK.Dbl.LeviEx := (GlobalTheory.ThK.Dbl.leviEx)
  have h_GlobalTheory_ThK_Dbl_OrthIn : GlobalTheory.ThK.Dbl.OrthIn := ⟨h_GlobalTheory_ThK_Dbl_SWFull, h_GlobalTheory_ThK_Dbl_BoxSec, h_GlobalTheory_ThK_Dbl_DblW, h_GlobalTheory_ThK_Dbl_HgtEx, h_GlobalTheory_ThK_Dbl_HgtInt, h_GlobalTheory_ThK_Dbl_Stab2Cpt, h_GlobalTheory_ThK_Dbl_EisContinues, h_GlobalTheory_ThK_Dbl_OffOpen, h_GlobalTheory_ThK_Dbl_HtEmb, h_Weil6_ThKEnd_Grp_UnipUGood, h_Weil6_ThKEnd_Grp_UnipLine, h_GlobalTheory_ThK_Dbl_CptAll, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_FinVolU, h_GlobalTheory_ThK_ThetaBasic, h_Weil6_ThKF_ArchOp, h_Weil6_ThKF_CartanConj, h_Weil6_ThKF_CartanMove, h_GlobalTheory_ThK_Dbl_LeviEx⟩
  have h_GlobalTheory_ThK_Dbl_LInt2 : GlobalTheory.ThK.Dbl.LInt2 := GlobalTheory.ThK.Dbl.lInt2
  have h_GlobalTheory_ThK_Dbl_SWAnisoX : GlobalTheory.ThK.Dbl.SWAnisoX := (GlobalTheory.ThK.Dbl.siegelWeilAniso_of h_SWStd h_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt).2
  have h_GlobalTheory_ThK_Dbl_BoxSecX : GlobalTheory.ThK.Dbl.BoxSecX := (GlobalTheory.ThK.Dbl.boxSecX_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFullX : GlobalTheory.ThK.Dbl.SWFullX := (GlobalTheory.ThK.Dbl.swFullX_of h_GlobalTheory_ThK_Dbl_SWAnisoX h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSecX)
  have h_GlobalTheory_ThK_Dbl_DblX : GlobalTheory.ThK.Dbl.DblX := (GlobalTheory.ThK.Dbl.dblX)
  have h_GlobalTheory_ThK_Dbl_NormZeta : GlobalTheory.ThK.Dbl.NormZeta := (GlobalTheory.ThK.Dbl.normZeta_of h_GlobalTheory_ThK_Dbl_SWFullX h_GlobalTheory_ThK_Dbl_BoxSecX h_GlobalTheory_ThK_Dbl_DblX h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_HgtInt h_GlobalTheory_ThK_Dbl_Stab2Cpt h_GlobalTheory_ThK_Dbl_CptAll h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_PolSch)
  have h_GlobalTheory_ThK_Dbl_EulerProd : GlobalTheory.ThK.Dbl.EulerProd := (GlobalTheory.ThK.Dbl.eulerProd)
  have h_GlobalTheory_ThK_Dbl_LocMeas : GlobalTheory.ThK.Dbl.LocMeas := (GlobalTheory.ThK.Dbl.locMeas)
  have h_GlobalTheory_ThK_Dbl_LocUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := GlobalTheory.ThK.Dbl.locUnrInert
  have h_GlobalTheory_ThK_Dbl_LocUnr : GlobalTheory.ThK.Dbl.LocUnr := (GlobalTheory.ThK.Dbl.locUnr_of h_GlobalTheory_ThK_Dbl_LocUnrSplit h_GlobalTheory_ThK_Dbl_LocUnrInert)
  have h_GlobalTheory_ThK_Dbl_RealInv : GlobalTheory.ThK.Dbl.RealInv := (GlobalTheory.ThK.Dbl.realInv_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_Dbl_DProd : GlobalTheory.ThK.Dbl.DProd := (GlobalTheory.ThK.Dbl.dProd)
  have h_GlobalTheory_ThK_Dbl_NonZeroBot : GlobalTheory.ThK.Dbl.NonZeroBot := (GlobalTheory.ThK.Dbl.nonZeroBottom_of_doubling_integral h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_Dbl_LInt2 h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_NormZeta h_GlobalTheory_ThK_Dbl_EulerProd h_GlobalTheory_ThK_Dbl_LocMeas h_GlobalTheory_ThK_Dbl_LocUnr h_GlobalTheory_ThK_Dbl_BadFactor h_GlobalTheory_ThK_Dbl_RealInv h_GlobalTheory_ThK_Dbl_DProd)
  have h_GlobalTheory_ThK_TowerA : GlobalTheory.ThK.TowerA := (PositivityTheory.ThKG.Tow.towerA_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_TowerB : GlobalTheory.ThK.TowerB := (PositivityTheory.ThKG.Tow.towerB_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_CTBigZero : GlobalTheory.ThK.CTBigZero := (PositivityTheory.ThKCT.ctBigZero_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallZero : GlobalTheory.ThK.CTSmallZero := (PositivityTheory.ThKCT.ctSmallZero_of h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_Dbl_SchToPol : GlobalTheory.ThK.Dbl.SchToPol := (GlobalTheory.ThK.Dbl.schToPol_of h_GlobalTheory_ThK_WeilConv)
  have h_GlobalTheory_ThK_Dbl_ToSo : GlobalTheory.ThK.Dbl.ToSo := (GlobalTheory.ThK.Dbl.toSo_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_CptAll)
  have h_GlobalTheory_ThK_NonZeroAn : GlobalTheory.ThK.NonZeroAn := (GlobalTheory.ThK.Dbl.nonZeroAn_of h_GlobalTheory_ThK_Dbl_NonZeroBot h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero h_GlobalTheory_ThK_Dbl_SchToPol h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_LeviEx h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_Dbl_ToSo)
  have h_Weil6_ThKEnd_OrthAn : PositivityTheory.ThKEnd.OrthAn := (GlobalTheory.ThK.Dbl.orthAn_of h_GlobalTheory_ThK_Dbl_OrthIn h_Weil6_ThKEnd_Orth_SigRapid h_Weil6_ThKEnd_Orth_SigThConst h_GlobalTheory_ThK_NonZeroAn h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero)
  have h_Weil6_ThKEst_SqAll : PositivityTheory.ThKEst.SqAll := (PositivityTheory.ThKEst.sqAll)
  have h_Weil6_ThKEst_SqSo : PositivityTheory.ThKEst.SqSo := (PositivityTheory.ThKEst.sqSo)
  have h_Weil6_ThKEst_LatCpt : PositivityTheory.ThKEst.LatCpt := (PositivityTheory.ThKEst.latCpt_of)
  have h_Weil6_ThKEst_LatTor : PositivityTheory.ThKEst.LatTor := (PositivityTheory.ThKEst.latTor)
  have h_Weil6_ThKEst_LatFull : PositivityTheory.ThKEst.LatFull := (PositivityTheory.ThKEst.latFull)
  have h_GlobalTheory_ThK_SqInt : GlobalTheory.ThK.SqInt := (PositivityTheory.ThKEst.Sq.sqInt_of_leaves h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_SqAll h_Weil6_ThKEst_SqSo h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_LatCpt h_Weil6_ThKEst_LatTor h_Weil6_ThKEst_LatFull)
  have h_Weil6_ThKEnd_PerpZero : PositivityTheory.ThKEnd.PerpZero := (PositivityTheory.ThKEnd.Grp.perpZero_of h_GlobalTheory_ThK_SqInt h_Weil6_ThKEnd_IAut)
  have h_Weil6_ThKEnd_Leaves : PositivityTheory.ThKEnd.Leaves := ⟨h_Weil6_ThKEnd_Iwa, h_Weil6_ThKEnd_CTBasic, h_Weil6_ThKEnd_LineMove, h_Weil6_ThKEnd_IAut, h_Weil6_ThKEnd_MatchStab, h_Weil6_ThKEnd_SigRe, h_Weil6_ThKEnd_TowerA2, h_Weil6_ThKEnd_AlphaZero, h_Weil6_ThKEnd_BetaZero, h_Weil6_ThKEnd_AlphaLow, h_Weil6_ThKEnd_TwoStep, h_Weil6_ThKEnd_CuspOfLine, h_Weil6_ThKEnd_OrthIso, h_Weil6_ThKEnd_OrthAn, h_Weil6_ThKEnd_PerpZero⟩
  have h_GlobalTheory_ThK_EndA : GlobalTheory.ThK.EndA := (PositivityTheory.ThKEnd.endA_of h_Weil6_ThKEnd_Leaves h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_MatchEx)
  have h_GlobalTheory_ThK_EndB : GlobalTheory.ThK.EndB := (PositivityTheory.ThKEnd.endB_of h_Weil6_ThKEnd_Leaves h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_MatchEx)
  exact ⟨h_GlobalTheory_ThK_EndA, h_GlobalTheory_ThK_EndB⟩
