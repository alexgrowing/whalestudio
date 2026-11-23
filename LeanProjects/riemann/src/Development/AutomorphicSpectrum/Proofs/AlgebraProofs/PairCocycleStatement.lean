import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cocycle : GroundTheory.Heights₂.Heights.NumbersDVR.PairCocycle.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle | exact GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle | (intros; apply GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle <;> assumption)
