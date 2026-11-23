import Development.WeilBound.ThetaLifts.AgreeOfLeaves
import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaEvaluationZeroCone
import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.WeilDomination.ExistsUnitChrWNe
import Development.WeilBound.ThetaLifts.WeilDomination.MatchEx
import Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaBasic
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixXClosed
import Development.WeilBound.ThetaLifts.WeilDomination.DomWeilOf
import Development.WeilBound.ThetaLifts.SmallCones.ThetaExp
import Development.WeilBound.ThetaLifts.CartanFactorisation.InjPure
import Mathlib
import Development.WeilBound.ThetaLifts.CartanFactorisation.PolCountFinal
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtInt
import Development.WeilBound.ThetaLifts.WeilDomination.SwAnisoXOf
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFin
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitTop
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SiegelTransport
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoCoinvariantsOfBernstein
import Development.WeilBound.ThetaLifts.SmallCones.SplitInv
import Development.WeilBound.ThetaLifts.LocalTheory.HypOf
import Development.WeilBound.ThetaLifts.SmallCones.SoZeroAOf
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.FLocBOf
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.BumpAFin
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.DarbouxExt
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.UnramifiedDeterminedBySphericalHolds
import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOfLie
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.SlicePol
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ExistsVol
import Development.WeilBound.ThetaLifts.LocalTheory.LocAOf
import Development.WeilBound.ThetaLifts.LocalTheory.LocBOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.VacIntZ
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.PerpZeroOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.SigReOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SmallAnyOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.EigenKillSet
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.SubMemKer
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.AlphaZeroOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.RealVanishOf
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ConeFacOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.TwoStepOf
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.LocalFieldT2Space
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.PlaContinuous
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ActsOfReads
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.ColOpSingle
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.CuspOfLineOfKeys
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConstFin
import Development.WeilBound.ThetaLifts.Reductions.WeightConstants.ConstOfGood
import Development.WeilBound.ThetaLifts.Reductions.TopPolarZero.PolZero
import Development.WeilBound.ThetaLifts.Reductions.JoinTriOf
import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare
import Development.WeilBound.ThetaLifts.Reductions.ArchLie
import Development.WeilBound.ThetaLifts.Reductions.KReal
import Development.WeilBound.ThetaLifts.Reductions.LocalLift
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilEx

namespace PositivityTheory.ThKR

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

structure SplitFacts : Prop where
  kCoinv : PositivityTheory.KCo.DictSt → GlobalTheory.ThK.KCoinv
  soCoinv : GlobalTheory.ThK.KFin → PositivityTheory.ThKF.SoCoinv
  ramifiedMultiplicityOne : PositivityTheory.ThKG.Loc.RamifiedMultiplicityOne
  finRam : PositivityTheory.ThK.FinRam
  finSplit : PositivityTheory.ThK.FinSplit

def MaxSteps : Prop :=
  ∃ M : Prop, (PositivityTheory.ThKF.LocUPairEx → PositivityTheory.KCo.DictSt → M) ∧
    (PositivityTheory.ThKR.JoinTri → M → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.PolCount →
      PositivityTheory.ThKF.CartanConj → PositivityTheory.ThKF.CartanMove → GlobalTheory.ThK.KCoinv → PositivityTheory.ThKF.ILeft → GlobalTheory.ThK.PolRe) ∧
    (GlobalTheory.ThK.ThetaBasic → GlobalTheory.ThK.WeilConv → GlobalTheory.ThK.SoCont → GlobalTheory.ThK.SqInt → GlobalTheory.ThK.KDecay → GlobalTheory.ThK.KCoinv →
      PositivityTheory.ThKF.ICont → PositivityTheory.ThKF.ArchOp → PositivityTheory.ThKF.ArchLie → PositivityTheory.ThKF.ArchUniq → PositivityTheory.ThKF.RadMax → PositivityTheory.ThKF.AdmTri → M →
      PositivityTheory.ThKR.JoinTri → PositivityTheory.ThKF.SoCoinv → PositivityTheory.ThKF.Kills)

theorem splitFacts_of (h : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : SplitFacts :=
  ⟨PositivityTheory.KCo.kCoinv_of_dict h, PositivityTheory.KCo.so_coinvariants_of_bernstein h, PositivityTheory.ThKG.LocalRamifiedLeviRestriction.ramifiedMultiplicityOne_of_bernstein h, PositivityTheory.ThK.SplitAsm.finite_ramified_of_bernstein h,
    PositivityTheory.ThK.SplitAsm.finite_split_holds h⟩

end PositivityTheory.ThKR
