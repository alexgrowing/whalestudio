import Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor
import Development.WeilBound.ThetaLifts.CartanFactorisation.ExistsEnlarge
import Development.WeilBound.ThetaLifts.CartanFactorisation.RealTrans
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasFiniteLengthOfSubsingleton
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.HypothesesAtTriple
import Development.WeilBound.ThetaLifts.CartanFactorisation.Cartan
import Development.WeilBound.ThetaLifts.CartanFactorisation.CuspidalClassOfWeilConvergence
import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairU
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.FullOfSoLoc
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.KCoinvOfDict

noncomputable section

namespace PositivityTheory.ThKF

open GlobalTheory.ThK

theorem iLeft (hT : ThetaBasic) : ILeft := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp _ hΦ g =>
  I_left unimodularity_holds hT hp hΦ g

theorem kCoinv (h : KP) : KCoinv := PositivityTheory.KCo.kCoinv_of_dict h.base.bernsteinUnitaryProductIrreducible PositivityTheory.KCo.dictionary_statement

end PositivityTheory.ThKF

end
