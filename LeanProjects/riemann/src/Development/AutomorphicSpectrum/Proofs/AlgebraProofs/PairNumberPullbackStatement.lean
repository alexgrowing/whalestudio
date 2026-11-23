import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_number_pullback : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | exact GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main <;> assumption)
