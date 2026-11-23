import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaConvergenceOfSiegelSetStatement
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore

namespace GlobalTheory.CompanionTheory.WTC

theorem weilThetaConvergence_of_core (h : PositivityTheory.ThKR.SiegelCore) : GlobalTheory.Published.WeilThetaConvergence :=
  GlobalTheory.T.theta_convergence_of_siegel_set (PositivityTheory.ThKR.siegel_of_core h)

end GlobalTheory.CompanionTheory.WTC
