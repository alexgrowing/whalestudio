import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.CupLeib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EvExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StExOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StUniq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StTopOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUniqOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StairCupFirst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeCupOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumToAcrTeichmuller
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLogUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatDegreeLgLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemMulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwUgCompAlgebraMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResGenRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecResMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecMapRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecPairApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDivPowSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullPullOfPullC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcMorCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernClassFamily

set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison.E.Main

theorem inSch : InSch := GlobalTheory.EtC.sch_cls_cocycle_sec

theorem stAdd : StAdd := GlobalTheory.CompanionTheory.StairAdd.stAdd

theorem stCol : StCol := GlobalTheory.CompanionTheory.EdgeStair.stCol

theorem stEx : StEx := GlobalTheory.CompanionTheory.EdgeStair.stEx_of_stCol stCol

theorem stUniq : StUniq := GlobalTheory.CompanionTheory.EdgeStair.stUniq stCol

theorem stTop : StTop := GlobalTheory.CompanionTheory.EdgeMap.stTop_of_stCol stCol

theorem edgeUniq : EdgeUniq := GlobalTheory.CompanionTheory.EdgeClass.edgeUniq_of stCol stAdd stUniq

theorem edgeMap : EdgeMap := GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap

theorem stCupA : StCupA := GlobalTheory.CompanionTheory.StairCupFirst.stCupA cupLeib

theorem stCupB : StCupB := GlobalTheory.CompanionTheory.Staircase.stCupB cupLeib stCol

theorem edgeCup : EdgeCup := GlobalTheory.CompanionTheory.EdgeMap.edgeCup_of_steps cupCls stTop stCupA stCupB

theorem lcCover : LcCover := GlobalTheory.CompanionTheory.LcCoverProof.lcCover

theorem locSplit : LocSplit := GlobalTheory.CompanionTheory.LocSplitProof.locSplit

theorem primAlg : PrimAlg := GlobalTheory.CompanionTheory.PrimAlgProof.primAlg

theorem rootPow : RootPow := GlobalTheory.CompanionTheory.RootPowLC.rootPow primAlg

theorem rootsEx : RootsEx := GlobalTheory.CompanionTheory.RootsC.rootsEx

theorem lcIdem : LcIdem := GlobalTheory.CompanionTheory.TiltIdem.lcIdem

theorem lcSpec : LcSpec := GlobalTheory.CompanionTheory.LcSp.lcSpec_of_lcIdem lcIdem

theorem lcNat : LcNat := GlobalTheory.CompanionTheory.LcNatProof.lcNat lcIdem lcSpec

theorem logEx : LogEx := GlobalTheory.CompanionTheory.CrisLog.logEx

theorem logAlg : LogAlg := GlobalTheory.CompanionTheory.LogAlgPf.logAlg

theorem logMul : LogMul := GlobalTheory.CompanionTheory.LogMulPf.logMul logAlg logEx

theorem logEps : LogEps := GlobalTheory.CompanionTheory.LogEpsP.logEps

theorem epsRoot : EpsRoot := GlobalTheory.CompanionTheory.EpsRootProof.epsRoot

theorem lcLog : LcLog := GlobalTheory.CompanionTheory.LcLogProof.lcLog lcIdem lcSpec lcCover logEx logMul logEps epsRoot

theorem lineBC : LineBC := GlobalTheory.CompanionTheory.LineBase.lineBC

theorem twUg : TwUg := GlobalTheory.CompanionTheory.TwUg.twUg_prop

theorem fPhi : FPhi := GlobalTheory.CompanionTheory.FrobLc.fPhi

theorem fKum : FKum := GlobalTheory.CompanionTheory.FKum.fKum rootPow lcLog

theorem liftEx : LiftEx := GlobalTheory.CompanionTheory.LineLift.liftEx

theorem firstChern_unique : FirstChernUniqueEtale := GlobalTheory.CompanionTheory.EtChern.chern_class_unique_of_lift_and_log liftEx logEx

theorem repBasic : RepBasic := GlobalTheory.CompanionTheory.EtEdge.repBasic evExt evNat inSch

theorem repConc : RepConc := GlobalTheory.CompanionTheory.EdgeMap.repConc_of_inputs evExt inSch repBasic

theorem repCup : RepCup := GlobalTheory.CompanionTheory.EdgeRep.repCup evExt evNat repBasic repConc inSch

theorem repOp : RepOp := GlobalTheory.CompanionTheory.EdgeRep.repOp evNat repConc repBasic

theorem resLoc : ResLoc := GlobalTheory.CompanionTheory.EdgeMap.resLoc

theorem resZero : ResZero := GlobalTheory.CompanionTheory.EtRes.resZero

theorem cechPt : CechPt := GlobalTheory.CompanionTheory.CechPts.cechPt_spec

theorem lineMap : LineMap := GlobalTheory.CompanionTheory.CechLine.lineMap_exists cechPt

theorem chern_class_compatible_system : FirstChernCompatibleSystem := GlobalTheory.CompanionTheory.ChernSys.chern_class_compatible_system cechPt

theorem firstChern_primitive_kummer : FirstChernCoboundary := GlobalTheory.CompanionTheory.KummerPrimitive.main evExt evNat evDel repConc repBasic cechPt

theorem resSplit : ResSplit := GlobalTheory.CompanionTheory.ResSplitProof.resSplit resLoc locSplit lcCover

theorem repRoot : RepRoot := GlobalTheory.CompanionTheory.EtRoot.repRoot repConc resZero

theorem redRoot : RedRoot := GlobalTheory.CompanionTheory.EdgeMap.redRoot_of_rep repRoot repOp repConc

theorem twZero : TwZero := GlobalTheory.CompanionTheory.TwZeroGen.twZero rootPow lcCover repRoot

theorem kapSpec : KapSpec := GlobalTheory.CompanionTheory.KapSpecProof.kapSpec lcCover repRoot

theorem kapBij : KapBij := GlobalTheory.CompanionTheory.KapBij.kapBij lcCover repRoot kapSpec

theorem kapMul : KapMul := GlobalTheory.CompanionTheory.KapMulE.kapMul_of lcCover repRoot kapSpec

theorem kapRed : KapRed := GlobalTheory.CompanionTheory.CstE.KapRedP.kapRed lcCover repRoot kapSpec

theorem kumPow : KumPow := GlobalTheory.CompanionTheory.KumPowProof.kumPow lcCover repRoot kapSpec primAlg

theorem resGood : ResGood := GlobalTheory.CompanionTheory.EdgeRes.resGood kapSpec kapBij resZero resSplit

theorem etSpec : EtSpec := GlobalTheory.CompanionTheory.EtSpecProof.etSpec resGood stEx edgeUniq repBasic resZero

theorem etNat : EtNat := GlobalTheory.CompanionTheory.EtNatProof.etNat etSpec edgeMap repBasic kapSpec twZero

theorem etRed : EtRed := GlobalTheory.CompanionTheory.EdgeRed.etRed etSpec edgeMap repBasic repOp kapSpec kapRed

theorem etCup : EtCup := GlobalTheory.CompanionTheory.EdgeProduct.etCup etSpec resGood edgeCup repBasic repCup kapMul

theorem etRoot : EtRoot := GlobalTheory.CompanionTheory.EdgeRoot.etRoot_of_spec etSpec repRoot kapSpec

theorem etale_chern_class_eq_kummer_class : EtaleFirstChernKummer := GlobalTheory.CompanionTheory.EtaleChernClass.etale_chern_class_eq_kummer_class etSpec resGood stCol firstChern_primitive_kummer kumPow

theorem fRed : FRed := GlobalTheory.CompanionTheory.EtReduction.fred_of_etRed etRed

theorem fEqui : FEqui := GlobalTheory.CompanionTheory.FEquiProof.fEqui etNat twUg

theorem fNat : FNat := GlobalTheory.CompanionTheory.FNatProof.fNat etNat

theorem fRes : FRes := GlobalTheory.CompanionTheory.FResProof.fRes etNat

theorem fCup : FCup := GlobalTheory.CompanionTheory.EtCupF.fCup etCup morCup lcSpec

theorem fRoot : FRoot := GlobalTheory.CompanionTheory.FRootCls.froot etRoot redRoot morCup lcSpec

theorem fUntw : FUntw := GlobalTheory.CompanionTheory.FUntwPf.main fCup fRoot cupOne

theorem firstChern_family : FirstChernClassFamily := firstChern_family_of_lifts lineBC lineMap chern_class_compatible_system etale_chern_class_eq_kummer_class fKum fRes fUntw

theorem etale_comparison_map : EtaleComparisonMapExists := etale_comparison_map_of_facts rootsEx lcNat fRed fEqui fPhi fNat fCup fRoot firstChern_family

end CrystallineSemistableComparison.E.Main
