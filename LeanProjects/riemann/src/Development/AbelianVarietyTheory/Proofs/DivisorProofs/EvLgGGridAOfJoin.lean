import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseExOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoLeMOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExFieldOfKeyFinExKey
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExKeyOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrJetOfTrFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumOfHyp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarrySecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermExistenceFromHowe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DictionarySizeBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridExistenceOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceFromLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferFlip
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralAndArchimedeanBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridExistenceOfPieces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilExistenceOfInputs
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem.Top GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem evLgG_gridA_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) :=
  fun hw hm P hJ ht K WC LM TA FS =>
    GlobalTheory.Mem.LiteralAutomorphy.evLgG_gridA_of_exGrid
      (GlobalTheory.Mem.LiteralAutomorphy.exGrid_of (GlobalTheory.Mem.LiteralAutomorphy.weilEx_of_classicalTheorems P)
        (isEx_of_separates FS (GlobalTheory.RowEx.linB P (GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems P)) (baseEx_of P (GlobalTheory.RowEx.constEx_of hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (GlobalTheory.RowClaim.rowSum_of_hypotheses P))
          (GlobalTheory.NFJetProof.nfJet_holds (GlobalTheory.RowClaim.rowSum_of_hypotheses P) GlobalTheory.NormSum.inp_all (GlobalTheory.DictFree.dictAt_big P GlobalTheory.NormSum.inp_all))
          (GlobalTheory.RowEx.RatioField.nfRatio P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (GlobalTheory.RowEx.nfBot_holds P GlobalTheory.NormSum.inp_all))
        (GlobalTheory.Mem.LiteralAutomorphy.nfSq_of_fieldDat GlobalTheory.NormSum.intSt_and_archSt.1 GlobalTheory.SqTop.fieldDat
          (GlobalTheory.ToricExist.torEx hJ.2.1 GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          GlobalTheory.SqTop.BotSmallProof.botSmall_holds)
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds
        GlobalTheory.Mem.LiteralAutomorphy.trSq_holds keyFin_holds GlobalTheory.Mem.LiteralAutomorphy.gKeyFin)

end GlobalTheory.Mem.LiteralAutomorphy
