import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PActsLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ChineseRemainderFiniteCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulActionInclusion
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PColQEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.SmRangeCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeSignEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDualForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceEqZeroOfBot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PFieldLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PFixLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FixZOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationBoundaryCriterionOfWdBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationCocycleLiftCriterionOfWdBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerOmegaBounded
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PGoodZ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RatioMemRB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IdJCriterion
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PIdVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.EuclideanHeightMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulExactWeaklyRegular
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoExactOfGl2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoInjectiveOfGl1
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WeightInverseContinuity
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KSubOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKapInd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TmulMemTensorRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKunDec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PoincareLelong
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ProjectiveLineTwo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLCupRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MemOmAIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLatOm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MapUnitEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocForms
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocMax
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocReg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdUniImpliesMJ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMinorSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMuSpan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.POmLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeDifferentialIdentityApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ProductCupOfSystem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdOneApply
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPTheta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PrBOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IntegralClosureMonoSubset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ValuationMulBis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RCupOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRCupTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.UnscUnscInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRestrictionTraceDegreeOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRYBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IntegralClosureFiniteGenerated
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceMemRB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRegulatorTrivialCase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRegLat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PResVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRowEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSubQEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeOneOfUniversalDerivation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeTwoOfUniversalDerivation
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysOk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RowMuNull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PThMuLat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MemUniInr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PValBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerDegree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdUni
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.YbValTensor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCmpG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCmpT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCols
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeltaConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ZActionCriterion
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MinorsCocycle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ImgTransInlE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PowMulMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CechZero
open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

private theorem field0 : UpperTheory.Gal.productCup_of_system.Field0 := by
  have hZFam : UpperTheory.Gal.productCup_of_system.ZFam := UpperTheory.Gal.productCup_of_system.zFam_of
  have hLatOm : UpperTheory.Gal.productCup_of_system.LatOm := UpperTheory.Gal.productCup_of_system.latOm_of
  have hLatA : UpperTheory.Gal.productCup_of_system.LatA := UpperTheory.Gal.productCup_of_system.latA_of
  have hDualForm : UpperTheory.Gal.productCup_of_system.DualForm := UpperTheory.Gal.productCup_of_system.dualForm_of
  have hIdJ : UpperTheory.Gal.productCup_of_system.IdJ := UpperTheory.Gal.productCup_of_system.idJ_of hLatOm hLatA hDualForm
  have hActsLin : UpperTheory.Gal.productCup_of_system.ActsLin := UpperTheory.Gal.productCup_of_system.actsLin_of
  have hGoodZ : UpperTheory.Gal.productCup_of_system.GoodZ := UpperTheory.Gal.productCup_of_system.goodZ_of
  have hIdIJ : UpperTheory.Gal.productCup_of_system.IdIJ := UpperTheory.Gal.productCup_of_system.idIJ_of hIdJ hActsLin hGoodZ
  have hReg0 : UpperTheory.Gal.productCup_of_system.Reg0 := UpperTheory.Gal.productCup_of_system.deRhamRegulator_trivial_case
  have hKer0 : UpperTheory.Gal.productCup_of_system.Ker0 := UpperTheory.Gal.productCup_of_system.kernelZero_holds
  have hRegLat : UpperTheory.Gal.productCup_of_system.RegLat := UpperTheory.Gal.productCup_of_system.regLat_of hReg0 hKer0
  have hHtpy : UpperTheory.Gal.productCup_of_system.Htpy := UpperTheory.Gal.productCup_of_system.htpy_of
  have hK1Mod : UpperTheory.Gal.productCup_of_system.KoszulExactBelowLengthOfWeaklyRegular := UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy hHtpy
  have hK1 : UpperTheory.Gal.productCup_of_system.K1 := UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound hK1Mod
  have hRS : UpperTheory.Gal.productCup_of_system.RS := UpperTheory.Gal.productCup_of_system.rS_of
  have hLocD : UpperTheory.Gal.productCup_of_system.LocD := UpperTheory.Gal.productCup_of_system.locD_of hRS hHtpy
  have hColZ : UpperTheory.Gal.productCup_of_system.ColZ := UpperTheory.Gal.productCup_of_system.colZ_of hRegLat hLatOm hDualForm hK1 hLocD hGoodZ
  have hWdBasic : UpperTheory.Gal.productCup_of_system.WdBasic := UpperTheory.Gal.productCup_of_system.wdBasic_of
  have hGL2 : UpperTheory.Gal.productCup_of_system.FiltrationCocycleLiftCriterion := UpperTheory.Gal.productCup_of_system.filtrationCocycleLiftCriterion_of_wdBasic hWdBasic
  have hSubQEx : UpperTheory.Gal.productCup_of_system.SubQEx := UpperTheory.Gal.productCup_of_system.subQEx_of hRS hWdBasic
  have hK2Ex : UpperTheory.Gal.productCup_of_system.KoszulCocycleExistsWithPrescribedComponent := UpperTheory.Gal.productCup_of_system.koszulTwoExact_of_gl2 hGL2 hSubQEx
  have hGL1 : UpperTheory.Gal.productCup_of_system.FiltrationBoundaryCriterion := UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic hWdBasic
  have hK2Inj : UpperTheory.Gal.productCup_of_system.KoszulBoundaryOfComponentMemIdeal := UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 hGL1 hSubQEx
  have hKSub : UpperTheory.Gal.productCup_of_system.KSub := UpperTheory.Gal.productCup_of_system.kSub_of hGL1 hSubQEx
  have hDet : UpperTheory.Gal.productCup_of_system.Det := UpperTheory.Gal.productCup_of_system.det_of
  have hThMu : UpperTheory.Gal.productCup_of_system.ThMu := UpperTheory.Gal.productCup_of_system.thMu_of hDet
  have hThMuLat : UpperTheory.Gal.productCup_of_system.ThMuLat := UpperTheory.Gal.productCup_of_system.thMuLat_of
  have hMuSpan : UpperTheory.Gal.productCup_of_system.MuSpan := UpperTheory.Gal.productCup_of_system.muSpan_of
  have hWdUni : UpperTheory.Gal.productCup_of_system.WdUni := UpperTheory.Gal.productCup_of_system.wdUni_of
  have hKapInd : UpperTheory.Gal.productCup_of_system.KapInd := UpperTheory.Gal.productCup_of_system.kapInd_of hThMu hWdUni
  have hSysOk : UpperTheory.Gal.productCup_of_system.SysOk := UpperTheory.Gal.productCup_of_system.sysOk_of hWdUni
  have hZCol : UpperTheory.Gal.productCup_of_system.ZCol := UpperTheory.Gal.productCup_of_system.zCol_of hIdIJ hColZ hK2Ex hK2Inj hKSub hRS hThMu hThMuLat hMuSpan hKapInd hActsLin hSysOk hGoodZ hWdBasic hWdUni
  have hColQEx : UpperTheory.Gal.productCup_of_system.ColQEx := UpperTheory.Gal.productCup_of_system.colQEx_of hWdUni
  have hL2 : UpperTheory.Gal.productCup_of_system.L2 := UpperTheory.Gal.productCup_of_system.localTwo_of_gl2 hGL2 hColQEx hWdUni
  have hSysL2 : UpperTheory.Gal.productCup_of_system.CechKoszulSystemCocycleGluing := UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_two_of_universalDerivation hL2 hSysOk hWdUni
  have hZEx : UpperTheory.Gal.productCup_of_system.ZEx := UpperTheory.Gal.productCup_of_system.zEx_of hZCol hColZ hSysL2 hK2Inj hKSub hRS hActsLin hSysOk hGoodZ hThMuLat
  have hRCup : UpperTheory.Gal.productCup_of_system.RCup := UpperTheory.Gal.productCup_of_system.rCup_of hWdUni
  have hSysBasic : UpperTheory.Gal.productCup_of_system.SysBasic := UpperTheory.Gal.productCup_of_system.sysBasic_of hWdUni hWdBasic
  have hPCup : UpperTheory.Gal.productCup_of_system.PCup := UpperTheory.Gal.productCup_of_system.pCup_of hRCup hSysBasic hSysOk hActsLin hGoodZ
  have hMJ : UpperTheory.Gal.productCup_of_system.MJ := UpperTheory.Gal.productCup_of_system.mJ_of hWdUni
  have hPTheta : UpperTheory.Gal.productCup_of_system.PTheta := UpperTheory.Gal.productCup_of_system.pTheta_of hMJ hThMu hThMuLat hKapInd hLatA hActsLin hGoodZ hSysBasic hSysOk
  have hPLift : UpperTheory.Gal.productCup_of_system.PLift := UpperTheory.Gal.productCup_of_system.pLift_of hThMu hThMuLat hKapInd hActsLin hLatA hGoodZ hSysOk hWdUni
  have hColP : UpperTheory.Gal.productCup_of_system.ColP := UpperTheory.Gal.productCup_of_system.colP_of hRegLat hLatOm hLatA hK1 hLocD hGoodZ
  have hL1 : UpperTheory.Gal.productCup_of_system.L1 := UpperTheory.Gal.productCup_of_system.localOne_of_gl1 hGL1 hColQEx hWdUni
  have hSysL1 : UpperTheory.Gal.productCup_of_system.CechKoszulSystemBoundaryCriterion := UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation hL1 hSysOk hWdUni
  have hPCmp : UpperTheory.Gal.productCup_of_system.PCmp := UpperTheory.Gal.productCup_of_system.pCmp_of hPLift hColP hSysL1 hSysBasic hSysOk hK2Inj hKSub hRS hGoodZ hThMuLat hMuSpan hActsLin hWdUni
  have hPInt : UpperTheory.Gal.productCup_of_system.PInt := UpperTheory.Gal.productCup_of_system.pInt_of hWdUni hGoodZ
  have hEdgeRel : UpperTheory.Gal.productCup_of_system.EdgeRel := UpperTheory.Gal.productCup_of_system.edgeRel_of hWdUni
  have hZAct : UpperTheory.Gal.productCup_of_system.ZAct := UpperTheory.Gal.productCup_of_system.zAct_of hPCup hPTheta hPCmp hPInt hEdgeRel hSysBasic hGoodZ
  have hRCupTop : UpperTheory.Gal.productCup_of_system.RCupTop := UpperTheory.Gal.productCup_of_system.rCupTop_of hWdUni hGoodZ
  have hKunDec : UpperTheory.Gal.productCup_of_system.KunDec := UpperTheory.Gal.productCup_of_system.kunDec_of hWdUni
  have hZId : UpperTheory.Gal.productCup_of_system.ZId := UpperTheory.Gal.productCup_of_system.zId_of hZAct hRCupTop hKunDec hSysBasic hGoodZ
  have hPrB : UpperTheory.Gal.productCup_of_system.PrB := UpperTheory.Gal.productCup_of_system.prB_of hGoodZ
  have hValBasic : UpperTheory.Gal.productCup_of_system.ValBasic := UpperTheory.Gal.productCup_of_system.valBasic_of
  have hLocMax : UpperTheory.Gal.productCup_of_system.LocMax := UpperTheory.Gal.productCup_of_system.locMax_of hValBasic
  have hLocOne : UpperTheory.Gal.productCup_of_system.LocOne := UpperTheory.Gal.productCup_of_system.locOne_of hLocMax hValBasic
  have hLocForms : UpperTheory.Gal.productCup_of_system.LocForms := UpperTheory.Gal.productCup_of_system.locForms_of hLocOne
  have hDtBasic : UpperTheory.Gal.productCup_of_system.DtBasic := UpperTheory.Gal.productCup_of_system.dtBasic_of
  have hCRT : UpperTheory.Gal.productCup_of_system.CRT := UpperTheory.Gal.productCup_of_system.cRT_of
  have hRT1 : UpperTheory.Gal.productCup_of_system.ResidueOfTraceIsFiberSum := UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one
  have hResVal : UpperTheory.Gal.productCup_of_system.ResVal := UpperTheory.Gal.productCup_of_system.resVal_of hValBasic
  have hTrVal : UpperTheory.Gal.productCup_of_system.TrVal := UpperTheory.Gal.productCup_of_system.trVal_of hRT1 hResVal hCRT hValBasic
  have hOmLoc : UpperTheory.Gal.productCup_of_system.OmLoc := UpperTheory.Gal.productCup_of_system.omLoc_of
  have hIdVal : UpperTheory.Gal.productCup_of_system.IdVal := UpperTheory.Gal.productCup_of_system.idVal_of hLocForms hDtBasic hCRT hTrVal hResVal hLatA hValBasic hOmLoc
  have hRedK : UpperTheory.Gal.productCup_of_system.RedK := UpperTheory.Gal.productCup_of_system.redK_of
  have hRYBasic : UpperTheory.Gal.productCup_of_system.RYBasic := UpperTheory.Gal.productCup_of_system.rYBasic_of
  have hFixZ : UpperTheory.Gal.productCup_of_system.FixZ := UpperTheory.Gal.productCup_of_system.fixZ_of hValBasic hRYBasic
  have hDtPull : UpperTheory.Gal.productCup_of_system.DtPull := UpperTheory.Gal.productCup_of_system.dtPull_of hLocOne hValBasic
  have hMinorSum : UpperTheory.Gal.productCup_of_system.MinorSum := UpperTheory.Gal.productCup_of_system.minorSum_of
  have hValG : UpperTheory.Gal.productCup_of_system.ValG := UpperTheory.Gal.productCup_of_system.valG_of hIdVal hRedK hFixZ hDtPull hMinorSum hDtBasic hValBasic
  have hLG : UpperTheory.Gal.productCup_of_system.LG := UpperTheory.Gal.productCup_of_system.lG_of
  have hRYFT : UpperTheory.Gal.productCup_of_system.RYFT := UpperTheory.Gal.productCup_of_system.rYFT_of
  have hLocReg : UpperTheory.Gal.productCup_of_system.LocReg := UpperTheory.Gal.productCup_of_system.locReg_of hLocForms hDtBasic hValBasic
  have hYKE : UpperTheory.Gal.productCup_of_system.YKE := UpperTheory.Gal.productCup_of_system.yKE_of hLG hOmLoc hRYFT hHtpy hK1 hLocReg hValBasic hRYBasic
  have hLocEq : UpperTheory.Gal.productCup_of_system.LocEq := UpperTheory.Gal.productCup_of_system.locEq_of hValBasic hRYBasic
  have hPtT : UpperTheory.Gal.productCup_of_system.PtT := UpperTheory.Gal.productCup_of_system.ptT_of hLocEq hValBasic hRYBasic
  have hPtG : UpperTheory.Gal.productCup_of_system.PtG := UpperTheory.Gal.productCup_of_system.ptG_of hLocEq hValBasic hRYBasic hPtT
  have hFixLoc : UpperTheory.Gal.productCup_of_system.FixLoc := UpperTheory.Gal.productCup_of_system.fixLoc_of hValBasic
  have hGMap : UpperTheory.Gal.productCup_of_system.GMap := UpperTheory.Gal.productCup_of_system.gMap_of hRYBasic hWdUni
  have hYCols : UpperTheory.Gal.productCup_of_system.YCols := UpperTheory.Gal.productCup_of_system.yCols_of hYKE hPtG hPtT hFixLoc hGMap hThMuLat hSysOk hRS hRYBasic
  have hYBig : UpperTheory.Gal.productCup_of_system.YBig := UpperTheory.Gal.productCup_of_system.yBig_of hYCols hYKE hK2Ex hSysL2 hSysOk hRS hPtT hLocMax hFixZ hGMap hDtBasic hValBasic hRYBasic hOmLoc
  have hThT : UpperTheory.Gal.productCup_of_system.ThT := UpperTheory.Gal.productCup_of_system.thT_of hDet
  have hYXi : UpperTheory.Gal.productCup_of_system.YXi := UpperTheory.Gal.productCup_of_system.yXi_of hMJ hThT hDtBasic hSysBasic hRYBasic hOmLoc
  have hYCmpT : UpperTheory.Gal.productCup_of_system.YCmpT := UpperTheory.Gal.productCup_of_system.yCmpT_of hYXi hYCols hYKE hPtT hSysL1 hSysBasic hSysOk hK2Inj hRS hLocMax hFixZ hValBasic hRYBasic hDtBasic hOmLoc
  have hK3 : UpperTheory.Gal.productCup_of_system.K3 := UpperTheory.Gal.productCup_of_system.koszulThree_of_det hDet hK2Inj hKSub hWdBasic
  have hYCmpG : UpperTheory.Gal.productCup_of_system.YCmpG := UpperTheory.Gal.productCup_of_system.yCmpG_of hYCols hYKE hPtG hFixLoc hK1 hK2Inj hK3 hLocReg hLocMax hLocForms hSysL1 hSysBasic hSysOk hRS hValBasic hRYBasic hOmLoc hWdUni
  have hYMain : UpperTheory.Gal.productCup_of_system.YMain := UpperTheory.Gal.productCup_of_system.yMain_of hValG hYBig hYCmpT hYCmpG hGMap hCRT hThMu hKapInd hActsLin hDtBasic hSysBasic hRYBasic hOmLoc hWdUni
  have hLCupRel : UpperTheory.Gal.productCup_of_system.LCupRel := UpperTheory.Gal.productCup_of_system.lCupRel_of hWdUni
  have hEdgeInj : UpperTheory.Gal.productCup_of_system.EdgeInj := UpperTheory.Gal.productCup_of_system.edgeInj_of hWdUni
  have hRowEx : UpperTheory.Gal.productCup_of_system.RowEx := UpperTheory.Gal.productCup_of_system.rowEx_of hLG hOmLoc hRYBasic hRYFT hValBasic hWdBasic
  have hEdgeB : UpperTheory.Gal.productCup_of_system.EdgeB := UpperTheory.Gal.productCup_of_system.edgeB_of hEdgeInj hRowEx hL1 hRYBasic hWdUni hWdBasic
  have hTrTop : UpperTheory.Gal.productCup_of_system.TrTop := UpperTheory.Gal.productCup_of_system.trTop_of
  have hTrLin : UpperTheory.Gal.productCup_of_system.TrLin := UpperTheory.Gal.productCup_of_system.trLin_of
  have hFieldLe : UpperTheory.Gal.productCup_of_system.FieldLe := UpperTheory.Gal.productCup_of_system.fieldLe_of hZFam hZEx hZId hPrB hYMain hGMap hLCupRel hEdgeB hTrTop hRT1 hTrLin hSysBasic hRYBasic hOmLoc
  have hField0 : UpperTheory.Gal.productCup_of_system.Field0 := UpperTheory.Gal.productCup_of_system.field0_of hFieldLe hValBasic
  exact hField0

theorem UpperTheory.Cb.exists_chart_lift_of_finite_cover :
    ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'),
      IsFinCover ℂ K x → IsFinCover ℂ K' x →
      (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) →
      IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) →
      (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) →
      (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) →
      ∀ (Fx : Finset (fib ℂ K' x)), (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) →
      (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
        ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
          ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) →
      ∀ A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ,
      (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
        c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧ ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) →
      (∀ e ∈ Fx, (1 - A e).det ≠ 0) →
      ∀ u : ∀ p : ℕ, (cech fun I => omB ℂ K (rB ℂ K x I) a).H p →ₗ[ℂ] (cech fun I => omB ℂ K (rB ℂ K x I) a).H p,
      (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p),
        ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ K' (RY x j2 (lft s) (rgt s)) a).Z p,
          (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
          ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p,
            u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
      (∀ p : ℕ, FiniteDimensional ℂ ((cech fun I => omB ℂ K (rB ℂ K x I) a).H p)) →
      ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) =
        ∑ e ∈ Fx, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a / (1 - A e).det :=
  field0
