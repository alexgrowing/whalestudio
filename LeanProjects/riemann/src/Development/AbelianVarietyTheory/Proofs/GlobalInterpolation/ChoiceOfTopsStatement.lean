import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.choice_of_tops : Formalism.G0.TileConditionFailureProbBound := by
  first | exact @GlobalTheory.RandomTops.prob_not_good_le | exact GlobalTheory.RandomTops.prob_not_good_le | (intros; apply GlobalTheory.RandomTops.prob_not_good_le <;> assumption)
