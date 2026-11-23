import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_left : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main <;> assumption)
