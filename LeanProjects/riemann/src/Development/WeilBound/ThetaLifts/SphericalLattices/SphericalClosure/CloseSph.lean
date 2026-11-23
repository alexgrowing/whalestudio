import Development.WeilBound.ThetaLifts.AgreeOfLeaves
import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaEvaluationZeroCone
import Development.WeilBound.ThetaLifts.WeilDomination.ExistsUnitChrWNe
import Development.WeilBound.ThetaLifts.CartanFactorisation.InjPure
import Mathlib
import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountFinal
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
import Development.WeilBound.ThetaLifts.WeilDomination.SwAnisoXOf
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFin
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.SmallCones.SplitInv
import Development.WeilBound.ThetaLifts.LocalTheory.HypOf
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.FLocBOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.BumpAFin
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.DarbouxExt
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.UnramifiedDeterminedBySphericalHolds
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOfLie
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ExistsVol
import Development.WeilBound.ThetaLifts.LocalTheory.LocAOf
import Development.WeilBound.ThetaLifts.LocalTheory.LocBOf
import Development.WeilBound.ThetaLifts.Reductions.TopPolarZero.PolZero
import Development.WeilBound.ThetaLifts.Reductions.JoinTriOf
import Development.WeilBound.ThetaLifts.SphericalLattices.SphericalClosure.EndCore
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaKillsCuspFormsSpherical
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxFinTOfPublished

theorem PositivityTheory.Sph.Tr.closeSph
    (hKCo : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv)
    (hSo : GlobalTheory.ThK.KFin → PositivityTheory.ThKF.SoCoinv)
    (hH1Ram : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne)
    (hFinRam : PositivityTheory.ThK.FinRam)
    (hFinSplit : PositivityTheory.ThK.FinSplit)
    (hSph : PositivityTheory.Sph.SphTri)
    (hFinInert : PositivityTheory.ThK.FinInert)
    (h_GlobalTheory_RealLift_LieSecond : GlobalTheory.RealLift.LieSecond)
    (h_Weil6_ThKF_ArchLie : PositivityTheory.ThKF.ArchLie)
    (h_GlobalTheory_ThK_KReal : GlobalTheory.ThK.KReal)
    (hSiegelSet : GlobalTheory.Published.SiegelSetUnitary)
    (h_GlobalTheory_ThK_Dbl_EisBL : GlobalTheory.ThK.Dbl.EisBL)
    (h_GlobalTheory_ThK_Dbl_SiegelWeilStd : GlobalTheory.ThK.Dbl.SiegelWeilStd)
    (h_Weil6_ThKG_Tow_WeilEx : PositivityTheory.ThKG.Tow.WeilEx) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching := by
  have h_GlobalTheory_ThK_EvZero : GlobalTheory.ThK.EvZero := (PositivityTheory.ThKF0.evaluation_at_zero_and_cone).1
  have h_GlobalTheory_ThK_EvCone : GlobalTheory.ThK.EvCone := (PositivityTheory.ThKF0.evaluation_at_zero_and_cone).2
  have h_GlobalTheory_ThK_StabEx : GlobalTheory.ThK.StabEx := (PositivityTheory.ThKG.Tow.stabEx)
  have h_GlobalTheory_ThK_TowerA : GlobalTheory.ThK.TowerA := (PositivityTheory.ThKG.Tow.towerA_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_TowerB : GlobalTheory.ThK.TowerB := (PositivityTheory.ThKG.Tow.towerB_of PositivityTheory.ThKG.Tow.planeEx PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_GlobalTheory_ThK_FacNe : GlobalTheory.ThK.FacNe := (PositivityTheory.ThK.Close.facNe)
  have h_Weil6_KCo_DictX : PositivityTheory.KCo.DictX := (PositivityTheory.ThKG.StdDict.dictX)
  have h_Weil6_KCo_SecSt : PositivityTheory.KCo.SecSt := (PositivityTheory.KCo.section_statement)
  have h_Weil6_KCo_DictSt : PositivityTheory.KCo.DictSt := (PositivityTheory.KCo.dictSt_of h_Weil6_KCo_DictX h_Weil6_KCo_SecSt)
  have h_GlobalTheory_ThK_KCoinv : GlobalTheory.ThK.KCoinv := (hKCo h_Weil6_KCo_DictSt)
  have h_GlobalTheory_ThK_MatchEx : GlobalTheory.ThK.MatchEx := (PositivityTheory.ThKClose.matchEx_of h_GlobalTheory_ThK_KCoinv)
  have h_Weil6_ThKG_LeviEx : PositivityTheory.ThKG.LeviEx := (PositivityTheory.ThKG.Tow.leviEx)
  have h_Weil6_ThKG_PolDense : PositivityTheory.ThKG.PolDense := (GlobalTheory.ThK.Dbl.polDense)
  have h_GlobalTheory_ThK_ThetaBasic : GlobalTheory.ThK.ThetaBasic := (PositivityTheory.ThKF0.thetaBasic)
  have h_GlobalTheory_ThK_WeilConv : GlobalTheory.ThK.WeilConv := (PositivityTheory.ThKEst.weilConv hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_GlobalTheory_ThK_SoCont : GlobalTheory.ThK.SoCont := (PositivityTheory.ThKEst.soCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKG_MixW : PositivityTheory.ThKG.MixW := (PositivityTheory.Mix.mixW_closed)
  have h_Weil6_ThKG_MixX : PositivityTheory.ThKG.MixX := (PositivityTheory.Mix.mixX_closed)
  have h_Weil6_ThKG_Tow_PairEx : PositivityTheory.ThKG.Tow.PairEx := (PositivityTheory.ThKG.Tow.pairEx_of PositivityTheory.ThKG.Tow.modelEx h_Weil6_ThKG_Tow_WeilEx)
  have h_Weil6_ThKG_Tow_PlaneHerm : PositivityTheory.ThKG.Tow.PlaneHerm := (PositivityTheory.ThKG.Tow.planeHerm)
  have h_Weil6_ThKEst_GrpTop : PositivityTheory.ThKEst.GrpTop := (PositivityTheory.ThKEst.grpTop_of)
  have h_Weil6_ThKEst_EpsOf : PositivityTheory.ThKEst.EpsOf := (PositivityTheory.ThKEst.epsOf_of)
  have h_Weil6_ThKEst_TriplePair : PositivityTheory.ThKEst.TriplePair := (PositivityTheory.ThKEst.Sq.triplePair_holds)
  have h_Weil6_ThKEst_DomWeilU : PositivityTheory.ThKEst.DomWeilU := (PositivityTheory.ThKEst.domWeilU hSiegelSet)
  have h_Weil6_ThKEst_DomWeil : PositivityTheory.ThKEst.DomWeil := (PositivityTheory.ThKClose.domWeil_of h_Weil6_ThKEst_DomWeilU)
  have h_Weil6_ThKEst_SoSemiU : PositivityTheory.ThKEst.SoSemiU := (PositivityTheory.ThKEst.soSemiU hSiegelSet)
  have h_Weil6_ThKEst_SoSemi : PositivityTheory.ThKEst.SoSemi := (PositivityTheory.ThKClose.soSemi_of h_Weil6_ThKEst_SoSemiU)
  have h_GlobalTheory_ThK_SoDecay : GlobalTheory.ThK.SoDecay := (PositivityTheory.ThKEst.soDecay hSiegelSet)
  have h_Weil6_ThKEst_FinVolU : PositivityTheory.ThKEst.FinVolU := (PositivityTheory.ThKEst.finVolU)
  have h_Weil6_ThKEst_SoFin : PositivityTheory.ThKEst.SoFin := (PositivityTheory.ThKEst.soFin_of)
  have h_Weil6_ThKCT_Ext : PositivityTheory.ThKCT.Ext := ⟨h_Weil6_ThKG_MixW, h_Weil6_ThKG_MixX, h_GlobalTheory_ThK_ThetaBasic, h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_Weil6_ThKG_Tow_PairEx, h_Weil6_ThKG_Tow_PlaneHerm, h_Weil6_ThKEst_GrpTop, h_Weil6_ThKEst_EpsOf, h_Weil6_ThKEst_TriplePair, h_GlobalTheory_ThK_WeilConv, h_Weil6_ThKEst_DomWeil, h_Weil6_ThKEst_SoSemi, h_GlobalTheory_ThK_SoDecay, h_Weil6_ThKEst_FinVolU, h_Weil6_ThKEst_SoFin⟩
  have h_GlobalTheory_ThK_SplitEx : GlobalTheory.ThK.SplitEx := (PositivityTheory.ThKCT.ct_all h_Weil6_ThKCT_Ext).2.1
  have h_Weil6_ThKCT_GenBig : PositivityTheory.ThKCT.GenBig := (PositivityTheory.ThKCT.Ext.genBig h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_GenAniso : PositivityTheory.ThKCT.GenAniso := (PositivityTheory.ThKCT.Ext.genAniso h_Weil6_ThKCT_Ext)
  have h_Weil6_ThKCT_KFinData : PositivityTheory.ThKCT.KFinData := (PositivityTheory.ThKCT.kFinData_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKCT_IwaEx : PositivityTheory.ThKCT.IwaEx := (PositivityTheory.ThKCT.iwaEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKCT_UnipEx : PositivityTheory.ThKCT.UnipEx := (PositivityTheory.ThKCT.unipEx_of)
  have h_GlobalTheory_ThK_CTBigZero : GlobalTheory.ThK.CTBigZero := (PositivityTheory.ThKCT.ctBigZero_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKG_Tow_PlaneHerm h_GlobalTheory_ThK_EvCone h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallZero : GlobalTheory.ThK.CTSmallZero := (PositivityTheory.ThKCT.ctSmallZero_of h_Weil6_ThKCT_GenAniso h_Weil6_ThKCT_KFinData h_GlobalTheory_ThK_StabEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTBigCone : GlobalTheory.ThK.CTBigCone := (PositivityTheory.ThKCT.ctBigCone_of h_Weil6_ThKCT_GenBig h_Weil6_ThKCT_KFinData h_Weil6_ThKCT_IwaEx h_Weil6_ThKG_Tow_PairEx h_GlobalTheory_ThK_EvZero h_Weil6_ThKCT_UnipEx h_Weil6_ThKEst_TriplePair)
  have h_GlobalTheory_ThK_CTSmallCone : GlobalTheory.ThK.CTSmallCone := (PositivityTheory.ThKCT.ct_all h_Weil6_ThKCT_Ext).2.2.2.2.2
  have h_Weil6_ThKF_ILeft : PositivityTheory.ThKF.ILeft := (PositivityTheory.ThKF.iLeft h_GlobalTheory_ThK_ThetaBasic)
  have h_GlobalTheory_ThK_AnAll : GlobalTheory.ThK.AnAll := (PositivityTheory.ThKF.anAll_of h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ILeft)
  have h_Weil6_ThKF_LocUPairEx : PositivityTheory.ThKF.LocUPairEx := (PositivityTheory.ThKH.Locpair.locUPairEx)
  have h_Weil6_ThKF_MaxFin : PositivityTheory.HoweDualityUnitaryAlt.MaxFinT := PositivityTheory.Sph.maxFinT_of hSph
  have h_Weil6_ThKF_ArchOp : PositivityTheory.ThKF.ArchOp := (PositivityTheory.ThKF.A.archOp)
  have h_Weil6_ThKF_ArchUniq : PositivityTheory.ThKF.ArchUniq := (PositivityTheory.ThKF.A.archUniq)
  have h_GlobalTheory_RealLift_DerEx : GlobalTheory.RealLift.DerEx := (PositivityTheory.RL.derEx)
  have h_GlobalTheory_RealLift_FockEx : GlobalTheory.RealLift.FockEx := (PositivityTheory.KRealA.i_fockex h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_ActsLaws : GlobalTheory.RealLift.ActsLaws := (PositivityTheory.KRealA.i_actslaws)
  have h_GlobalTheory_RealLift_VacLine : GlobalTheory.RealLift.VacLine := (PositivityTheory.KRealA.i_vacline h_GlobalTheory_RealLift_DerEx)
  have h_GlobalTheory_RealLift_PolRange : GlobalTheory.RealLift.PolRange := (PositivityTheory.ThKEnd.Comp.PR.polRange_of h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine)
  have h_GlobalTheory_RealLift_LieFirst : GlobalTheory.RealLift.LieFirst := (PositivityTheory.RL.lieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThKR_JoinTri : PositivityTheory.ThKR.JoinTri := PositivityTheory.ThKR.Join.joinTri_of h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond
  have h_Weil6_ThKF_PolCount : PositivityTheory.ThKF.PolCount := (PositivityTheory.ThKF.polCount_of_derEx h_GlobalTheory_RealLift_DerEx)
  have h_Weil6_ThKF_CartanConj : PositivityTheory.ThKF.CartanConj := (PositivityTheory.ThKF.cartan_conjugacy_holds)
  have h_Weil6_ThKF_CartanMove : PositivityTheory.ThKF.CartanMove := (PositivityTheory.ThKF.cartanMove_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_PolRe : GlobalTheory.ThK.PolRe := (PositivityTheory.HoweDualityUnitaryAlt.polRe_of2T h_Weil6_ThKR_JoinTri h_Weil6_ThKF_MaxFin h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_Weil6_ThKF_PolCount h_Weil6_ThKF_CartanConj h_Weil6_ThKF_CartanMove h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ILeft)
  have h_GlobalTheory_ThK_Dbl_LInt2 : GlobalTheory.ThK.Dbl.LInt2 := GlobalTheory.ThK.Dbl.lInt2
  have h_GlobalTheory_ThK_Dbl_HgtEx : GlobalTheory.ThK.Dbl.HgtEx := (GlobalTheory.ThK.Dbl.hgtEx)
  have h_GlobalTheory_ThK_Dbl_FrameConj : GlobalTheory.ThK.Dbl.FrameConj := (GlobalTheory.ThK.Dbl.frameConj)
  have h_GlobalTheory_ThK_Dbl_FinLevel : GlobalTheory.ThK.Dbl.FinLevel := (GlobalTheory.ThK.Dbl.finLevel)
  have h_GlobalTheory_ThK_Dbl_Stab2Cpt : GlobalTheory.ThK.Dbl.Stab2Cpt := (GlobalTheory.ThK.Dbl.stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWAnisoX : GlobalTheory.ThK.Dbl.SWAnisoX := (PositivityTheory.ThKClose.swAnisoX_of h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_FrameConj h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_EisContinues : GlobalTheory.ThK.Dbl.EisContinues := (GlobalTheory.ThK.Dbl.eisContinues_of h_GlobalTheory_ThK_Dbl_EisBL h_GlobalTheory_ThK_Dbl_FrameConj)
  have h_GlobalTheory_ThK_Dbl_BoxSecX : GlobalTheory.ThK.Dbl.BoxSecX := (GlobalTheory.ThK.Dbl.boxSecX_of h_GlobalTheory_ThK_Dbl_FinLevel h_GlobalTheory_ThK_Dbl_Stab2Cpt)
  have h_GlobalTheory_ThK_Dbl_SWFullX : GlobalTheory.ThK.Dbl.SWFullX := (GlobalTheory.ThK.Dbl.swFullX_of h_GlobalTheory_ThK_Dbl_SWAnisoX h_GlobalTheory_ThK_Dbl_EisContinues h_GlobalTheory_ThK_Dbl_BoxSecX)
  have h_GlobalTheory_ThK_Dbl_DblX : GlobalTheory.ThK.Dbl.DblX := (GlobalTheory.ThK.Dbl.dblX)
  have h_GlobalTheory_ThK_Dbl_HgtInt : GlobalTheory.ThK.Dbl.HgtInt := (GlobalTheory.ThK.Dbl.hgtInt)
  have h_Weil6_ThKEst_SiegelAll : PositivityTheory.ThKEst.SiegelAll := (PositivityTheory.ThKEst.siegelAll_of hSiegelSet)
  have h_Weil6_ThKF_Unimod : PositivityTheory.ThKF.Unimod := (PositivityTheory.ThKF.unimodularity_holds)
  have h_GlobalTheory_ThK_Dbl_CptAll : GlobalTheory.ThK.Dbl.CptAll := (GlobalTheory.ThK.Dbl.cptAll_of h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_GlobalTheory_ThK_Dbl_PolSch : GlobalTheory.ThK.Dbl.PolSch := (GlobalTheory.ThK.Dbl.polSch)
  have h_GlobalTheory_ThK_Dbl_NormZeta : GlobalTheory.ThK.Dbl.NormZeta := (GlobalTheory.ThK.Dbl.normZeta_of h_GlobalTheory_ThK_Dbl_SWFullX h_GlobalTheory_ThK_Dbl_BoxSecX h_GlobalTheory_ThK_Dbl_DblX h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_HgtInt h_GlobalTheory_ThK_Dbl_Stab2Cpt h_GlobalTheory_ThK_Dbl_CptAll h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_PolSch)
  have h_GlobalTheory_ThK_Dbl_EulerProd : GlobalTheory.ThK.Dbl.EulerProd := (GlobalTheory.ThK.Dbl.eulerProd)
  have h_GlobalTheory_ThK_Dbl_LocMeas : GlobalTheory.ThK.Dbl.LocMeas := (GlobalTheory.ThK.Dbl.locMeas)
  have h_GlobalTheory_ThK_Dbl_LocUnrSplit : GlobalTheory.ThK.Dbl.LocUnrSplit := (GlobalTheory.ThK.Dbl.locUnrSplit)
  have h_GlobalTheory_ThK_Dbl_LocUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := (GlobalTheory.ThK.Dbl.Inert.main)
  have h_GlobalTheory_ThK_Dbl_LocUnr : GlobalTheory.ThK.Dbl.LocUnr := (GlobalTheory.ThK.Dbl.locUnr_of h_GlobalTheory_ThK_Dbl_LocUnrSplit h_GlobalTheory_ThK_Dbl_LocUnrInert)
  have h_GlobalTheory_ThK_Dbl_BadFactor : GlobalTheory.ThK.Dbl.BadFactor := (GlobalTheory.ThK.Dbl.badFactor)
  have h_GlobalTheory_ThK_Dbl_RealInv : GlobalTheory.ThK.Dbl.RealInv := (GlobalTheory.ThK.Dbl.realInv_of h_Weil6_ThKF_ArchOp)
  have h_GlobalTheory_ThK_Dbl_DProd : GlobalTheory.ThK.Dbl.DProd := (GlobalTheory.ThK.Dbl.dProd)
  have h_GlobalTheory_ThK_Dbl_NonZeroBot : GlobalTheory.ThK.Dbl.NonZeroBot := (GlobalTheory.ThK.Dbl.nonZeroBottom_of_doubling_integral h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_Dbl_LInt2 h_GlobalTheory_ThK_Dbl_HgtEx h_GlobalTheory_ThK_Dbl_NormZeta h_GlobalTheory_ThK_Dbl_EulerProd h_GlobalTheory_ThK_Dbl_LocMeas h_GlobalTheory_ThK_Dbl_LocUnr h_GlobalTheory_ThK_Dbl_BadFactor h_GlobalTheory_ThK_Dbl_RealInv h_GlobalTheory_ThK_Dbl_DProd)
  have h_GlobalTheory_ThK_Dbl_SchToPol : GlobalTheory.ThK.Dbl.SchToPol := (GlobalTheory.ThK.Dbl.schToPol_of h_GlobalTheory_ThK_WeilConv)
  have h_GlobalTheory_ThK_Dbl_LeviEx : GlobalTheory.ThK.Dbl.LeviEx := (GlobalTheory.ThK.Dbl.leviEx)
  have h_Weil6_ThK_FinRam : PositivityTheory.ThK.FinRam := (hFinRam)
  have h_Weil6_ThK_FinSplit : PositivityTheory.ThK.FinSplit := (hFinSplit)
  have h_Weil6_ThK_FinInert : PositivityTheory.ThK.FinInert := (hFinInert)
  have h_GlobalTheory_ThK_KFin : GlobalTheory.ThK.KFin := (PositivityTheory.ThK.kFin_of h_Weil6_ThK_FinRam h_Weil6_ThK_FinSplit h_Weil6_ThK_FinInert)
  have h_GlobalTheory_ThK_Dbl_ToSo : GlobalTheory.ThK.Dbl.ToSo := (GlobalTheory.ThK.Dbl.toSo_of h_GlobalTheory_ThK_KReal h_GlobalTheory_ThK_KFin h_GlobalTheory_ThK_KCoinv h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_Dbl_CptAll)
  have h_GlobalTheory_ThK_NonZeroAn : GlobalTheory.ThK.NonZeroAn := (GlobalTheory.ThK.Dbl.nonZeroAn_of h_GlobalTheory_ThK_Dbl_NonZeroBot h_GlobalTheory_ThK_TowerA h_GlobalTheory_ThK_TowerB h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_CTBigZero h_GlobalTheory_ThK_CTSmallZero h_GlobalTheory_ThK_Dbl_SchToPol h_GlobalTheory_ThK_Dbl_PolSch h_GlobalTheory_ThK_Dbl_LeviEx h_GlobalTheory_ThK_SplitEx h_GlobalTheory_ThK_Dbl_ToSo)
  have h_GlobalTheory_ThK_KDecay : GlobalTheory.ThK.KDecay := (PositivityTheory.ThKEst.kDecay hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKEst_SqAll : PositivityTheory.ThKEst.SqAll := (PositivityTheory.ThKEst.sqAll)
  have h_Weil6_ThKEst_SqSo : PositivityTheory.ThKEst.SqSo := (PositivityTheory.ThKEst.sqSo)
  have h_Weil6_ThKEst_LatCpt : PositivityTheory.ThKEst.LatCpt := (PositivityTheory.ThKEst.latCpt_of)
  have h_Weil6_ThKEst_LatTor : PositivityTheory.ThKEst.LatTor := (PositivityTheory.ThKEst.latTor)
  have h_Weil6_ThKEst_LatFull : PositivityTheory.ThKEst.LatFull := (PositivityTheory.ThKEst.latFull)
  have h_GlobalTheory_ThK_SqInt : GlobalTheory.ThK.SqInt := (PositivityTheory.ThKEst.Sq.sqInt_of_leaves h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_SqAll h_Weil6_ThKEst_SqSo h_Weil6_ThKEst_SoFin h_Weil6_ThKEst_LatCpt h_Weil6_ThKEst_LatTor h_Weil6_ThKEst_LatFull)
  have h_Weil6_ThKF_ICont : PositivityTheory.ThKF.ICont := (PositivityTheory.ThKEst.iCont hSiegelSet h_GlobalTheory_ThK_ThetaBasic)
  have h_Weil6_ThKF_RadMax : PositivityTheory.ThKF.RadMax := (PositivityTheory.ThKF.Unit.radMax_of h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_PolRange h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThK_LocPairEx : PositivityTheory.ThK.LocPairEx := (PositivityTheory.ThKH.Locpair.locPairEx)
  have h_Weil6_ThK_SiegelTransport : PositivityTheory.ThK.SiegelTransport := (PositivityTheory.ThK.siegel_transport)
  have h_Weil6_ThK_LinearAct : PositivityTheory.ThK.LinearAct := (PositivityTheory.ThK.split_character_fixes_evaluation)
  have h_Weil6_ThKF_SoCoinv : PositivityTheory.ThKF.SoCoinv := (hSo h_GlobalTheory_ThK_KFin)
  have h_Weil6_ThKF_Kills : PositivityTheory.ThKF.Kills := (PositivityTheory.Sph.theta_kills_cusp_forms_spherical h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoCont h_GlobalTheory_ThK_SqInt h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_ICont h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_Weil6_ThKF_RadMax hSph h_Weil6_ThKR_JoinTri h_Weil6_ThKF_SoCoinv)
  have h_GlobalTheory_ThK_Factor : GlobalTheory.ThK.Factor := (PositivityTheory.ThKF.factor_of h_GlobalTheory_ThK_KDecay h_Weil6_ThKF_Kills)
  have h_GlobalTheory_ThK_PolZero : GlobalTheory.ThK.PolZero := (PositivityTheory.ThKR.polynomial_vanishing_of_compactness h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne_holds h_GlobalTheory_ThK_NonZeroAn h_GlobalTheory_ThK_Factor h_GlobalTheory_ThK_MatchEx h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_KDecay h_Weil6_ThKF_ICont h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf h_Weil6_ThKEst_SiegelAll h_Weil6_ThKEst_FinVolU h_Weil6_ThKF_Unimod)
  have h_Weil6_ThKCT_StabDec : PositivityTheory.ThKCT.StabDec := (PositivityTheory.ThKCT.stabDec_of)
  have h_Weil6_ThKG_Loc_SplitInv2 : PositivityTheory.ThKG.Loc.SplitInv2 := (PositivityTheory.ThKCT.splitInv2_of h_Weil6_ThKCT_UnipEx h_Weil6_ThKCT_StabDec h_GlobalTheory_ThK_ThetaBasic h_Weil6_ThKEst_TriplePair h_Weil6_ThKEst_GrpTop h_Weil6_ThKEst_EpsOf)
  have h_Weil6_ThKG_Loc_Hyp : PositivityTheory.ThKG.Loc.Hyp := (PositivityTheory.ThKG.Loc.hyp_of h_GlobalTheory_ThK_ThetaBasic h_GlobalTheory_ThK_WeilConv h_GlobalTheory_ThK_SoCont h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv h_Weil6_ThKF_Kills h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchLie h_Weil6_ThKF_ArchUniq h_GlobalTheory_ThK_SplitEx h_Weil6_ThKG_Loc_SplitInv2 h_GlobalTheory_ThK_EvZero h_GlobalTheory_ThK_FacNe)
  have h_Weil6_ThKG_Loc_MeasEx : PositivityTheory.ThKG.Loc.MeasEx := (PositivityTheory.ThKG.Loc.Cone.measEx_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKG_Loc_Cone_IdeleFub : PositivityTheory.ThKG.Loc.Cone.IdeleFub := (PositivityTheory.ThKG.Loc.Cone.ideleFub)
  have h_Weil6_ThKG_Loc_Cone_IdealId0 : PositivityTheory.ThKG.Loc.Cone.IdealId0 := (PositivityTheory.ThKG.Loc.Cone.Id.idealId0)
  have h_Weil6_ThKCT_ThetaExp : PositivityTheory.ThKCT.ThetaExp := (PositivityTheory.ThKCT.thetaExp)
  have h_Weil6_ThKCT_EvUniq : PositivityTheory.ThKCT.EvUniq := (PositivityTheory.ThKCT.evUniq_of h_Weil6_ThKCT_ThetaExp)
  have h_Weil6_ThKCT_MixAB : PositivityTheory.ThKCT.MixAB := (PositivityTheory.ThKCT.Ker.mixAB_of h_Weil6_ThKG_MixW h_Weil6_ThKG_MixX h_GlobalTheory_ThK_EvZero h_Weil6_ThKG_Tow_PairEx h_Weil6_ThKCT_ThetaExp h_Weil6_ThKCT_EvUniq)
  have h_Weil6_ThKCT_SoStab : PositivityTheory.ThKCT.SoStab := (PositivityTheory.ThKCT.soStab_of)
  have h_Weil6_ThKCT_Low : PositivityTheory.ThKCT.Low := (PositivityTheory.ThKCT.low_of)
  have h_Weil6_ThKCT_SoEv : PositivityTheory.ThKCT.SoEv := (PositivityTheory.ThKCT.soEv_of' h_Weil6_ThKCT_Low)
  have h_Weil6_ThKCT_LinEx : PositivityTheory.ThKCT.LinEx := (PositivityTheory.ThKCT.linEx_of)
  have h_Weil6_ThKG_Loc_FLocB : PositivityTheory.ThKG.Loc.FLocB := (PositivityTheory.ThKG.Loc.FL.fLocB_of h_Weil6_ThKG_Loc_Cone_IdeleFub h_Weil6_ThKG_Loc_Cone_IdealId0 h_GlobalTheory_ThK_StabEx h_Weil6_ThKCT_IwaEx h_Weil6_ThKCT_MixAB h_Weil6_ThKEst_TriplePair h_Weil6_ThKCT_SoStab h_Weil6_ThKCT_SoEv h_Weil6_ThKCT_LinEx)
  have h_Weil6_ThKCT_Slice : PositivityTheory.ThKCT.Slice := (PositivityTheory.ThKCT.slice_of)
  have h_Weil6_ThKCT_SchInt : PositivityTheory.ThKCT.SchInt := (PositivityTheory.ThKCT.schInt)
  have h_Weil6_ThKG_Loc_BumpA : PositivityTheory.ThKG.Loc.BumpA := (PositivityTheory.ThKG.Loc.Bump.bumpA_fin h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_MixAB)
  have h_Weil6_ThKG_Loc_BumpB : PositivityTheory.ThKG.Loc.BumpB := (PositivityTheory.ThKG.Loc.Bump.bumpB_fin h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_Weil6_ThKCT_MixAB)
  have h_Weil6_ThKG_Loc_RealUniq : PositivityTheory.ThKG.Loc.RealUniq := (PositivityTheory.ThKG.CayleyTransformDarboux.realUniq)
  have h_Weil6_ThKG_Loc_H1Unr2 : PositivityTheory.ThKG.Loc.UnramifiedMultiplicityOneProportional := (PositivityTheory.ThKG.Loc.unramifiedProportional_holds)
  have h_Weil6_ThKG_Loc_H1Ram : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne := (hH1Ram)
  have h_Weil6_ThKG_Loc_H1Inf : PositivityTheory.ThKG.Loc.ArchimedeanMultiplicityOne := (PositivityTheory.ThKG.CayleyTransformDarboux.archimedean_multiplicity_one_of_lie h_GlobalTheory_RealLift_LieFirst h_GlobalTheory_RealLift_LieSecond)
  have h_Weil6_ThKG_Loc_Hyp2 : PositivityTheory.ThKG.Loc.Hyp2 := ⟨h_Weil6_ThKG_Loc_MeasEx, h_Weil6_ThKG_Loc_FLocB, h_Weil6_ThKG_Loc_BumpA, h_Weil6_ThKG_Loc_BumpB, h_Weil6_ThKG_Loc_RealUniq, h_Weil6_ThKG_Loc_H1Unr2, h_Weil6_ThKG_Loc_H1Ram, h_Weil6_ThKG_Loc_H1Inf, h_GlobalTheory_ThK_CTBigZero, h_GlobalTheory_ThK_CTSmallCone, h_GlobalTheory_ThK_CTBigCone, h_GlobalTheory_ThK_CTSmallZero⟩
  have h_GlobalTheory_ThK_ActsEx : GlobalTheory.ThK.ActsEx := (PositivityTheory.ThKF0.actsEx)
  have h_Weil6_Mix_PureSt : PositivityTheory.Mix.PureSt := (PositivityTheory.Mix.pure_tensor_estimates_holds)
  have h_Weil6_ThKG_Loc_Bump_ArchDict : PositivityTheory.ThKG.Loc.Bump.ArchDict := (PositivityTheory.ThKG.Loc.Bump.archDict_of)
  have h_Weil6_ThKG_Loc_Bump_ArchHeis : PositivityTheory.ThKG.Loc.Bump.ArchHeis := (PositivityTheory.ThKG.Loc.Bump.archHeis_of)
  have h_GlobalTheory_RealLift_FrameEx : GlobalTheory.RealLift.FrameEx := (PositivityTheory.KRealA.i_frameex)
  have h_Weil6_ThKCT_EvAdm : PositivityTheory.ThKCT.EvAdm := (PositivityTheory.ThKCT.evAdm_of)
  have h_Weil6_ThKG_Loc_Cone_ArchCone : PositivityTheory.ThKG.Loc.Cone.ArchCone := (PositivityTheory.ThKG.Loc.Bump.archCone_of h_Weil6_ThKG_Loc_Bump_ArchDict h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKCT_Slice h_Weil6_ThKG_Loc_Bump_ArchHeis h_Weil6_ThKF_ArchUniq h_Weil6_ThKCT_SchInt h_GlobalTheory_RealLift_ActsLaws h_GlobalTheory_RealLift_DerEx h_GlobalTheory_RealLift_VacLine h_GlobalTheory_RealLift_FockEx h_GlobalTheory_RealLift_FrameEx h_Weil6_ThKCT_EvAdm h_Weil6_ThKCT_KFinData)
  have h_Weil6_ThKG_Loc_Cone_VacFixX : PositivityTheory.ThKG.Loc.Cone.VacFixX := (PositivityTheory.ThKG.Loc.Cone.vacFixX_of h_GlobalTheory_ThK_StabEx)
  have h_Weil6_ThKG_Loc_ConeFacA : PositivityTheory.ThKG.Loc.ConeFacA := (PositivityTheory.ThKG.Loc.Cone.coneFac_all h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone h_Weil6_ThKG_Loc_Cone_VacFixX).2.1
  have h_Weil6_ThKG_Loc_StdA : PositivityTheory.ThKG.Loc.StdA := (PositivityTheory.ThKG.Std.stdA)
  have h_Weil6_ThKG_LocA_ : PositivityTheory.ThKG.LocA' := (PositivityTheory.ThKG.Loc.locA_of h_Weil6_ThKG_Loc_Hyp h_Weil6_ThKG_Loc_Hyp2 h_Weil6_ThKG_Loc_ConeFacA h_Weil6_ThKG_Loc_StdA)
  have h_Weil6_ThKG_Loc_ConeFacB : PositivityTheory.ThKG.Loc.ConeFacB := (PositivityTheory.ThKG.Loc.Cone.coneFac_all h_GlobalTheory_ThK_ActsEx h_GlobalTheory_ThK_StabEx h_Weil6_ThKF_ArchOp h_Weil6_ThKF_ArchUniq h_Weil6_Mix_PureSt h_Weil6_ThKG_Loc_Cone_ArchCone h_Weil6_ThKG_Loc_Cone_VacFixX).2.2
  have h_Weil6_ThKG_Loc_StdB : PositivityTheory.ThKG.Loc.StdB := (PositivityTheory.ThKG.Std.stdB)
  have h_Weil6_ThKG_LocB_ : PositivityTheory.ThKG.LocB' := (PositivityTheory.ThKG.Loc.locB_of h_Weil6_ThKG_Loc_Hyp h_Weil6_ThKG_Loc_Hyp2 h_Weil6_ThKG_Loc_ConeFacB h_Weil6_ThKG_Loc_StdB)
  have h_GlobalTheory_ThK_EndA : GlobalTheory.ThK.EndA := (PositivityTheory.Sph.Tr.endAB_sph hSiegelSet h_Weil6_ThKG_Tow_WeilEx hKCo hFinRam hFinSplit hFinInert h_GlobalTheory_RealLift_LieSecond h_Weil6_ThKF_ArchLie h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL).1
  have h_Weil6_ThKG_EndA_ : PositivityTheory.ThKG.EndA' := (PositivityTheory.ThKG.endA'_of h_GlobalTheory_ThK_EndA)
  have h_GlobalTheory_ThK_EndB : GlobalTheory.ThK.EndB := (PositivityTheory.Sph.Tr.endAB_sph hSiegelSet h_Weil6_ThKG_Tow_WeilEx hKCo hFinRam hFinSplit hFinInert h_GlobalTheory_RealLift_LieSecond h_Weil6_ThKF_ArchLie h_GlobalTheory_ThK_Dbl_SiegelWeilStd h_GlobalTheory_ThK_Dbl_EisBL).2
  have h_Weil6_ThKG_EndB_ : PositivityTheory.ThKG.EndB' := (PositivityTheory.ThKG.endB'_of h_GlobalTheory_ThK_EndB)
  have h_Weil6_ThKG_Leaves : PositivityTheory.ThKG.Leaves := ⟨h_GlobalTheory_ThK_EvZero, h_GlobalTheory_ThK_EvCone, h_GlobalTheory_ThK_StabEx, h_GlobalTheory_ThK_TowerA, h_GlobalTheory_ThK_TowerB, h_GlobalTheory_ThK_FacNe, h_GlobalTheory_ThK_MatchEx, h_Weil6_ThKG_LeviEx, h_Weil6_ThKG_PolDense, h_GlobalTheory_ThK_WeilConv, h_GlobalTheory_ThK_SoCont, h_GlobalTheory_ThK_SplitEx, h_GlobalTheory_ThK_CTBigZero, h_GlobalTheory_ThK_CTSmallZero, h_GlobalTheory_ThK_CTBigCone, h_GlobalTheory_ThK_CTSmallCone, h_GlobalTheory_ThK_AnAll, h_GlobalTheory_ThK_PolRe, h_GlobalTheory_ThK_NonZeroAn, h_GlobalTheory_ThK_PolZero, h_Weil6_ThKG_LocA_, h_Weil6_ThKG_LocB_, h_Weil6_ThKG_EndA_, h_Weil6_ThKG_EndB_, h_GlobalTheory_ThK_KReal, h_GlobalTheory_ThK_KFin⟩
  exact PositivityTheory.ThKG.agree_of_leaves h_Weil6_ThKG_Leaves h_GlobalTheory_ThK_KDecay h_GlobalTheory_ThK_KCoinv
