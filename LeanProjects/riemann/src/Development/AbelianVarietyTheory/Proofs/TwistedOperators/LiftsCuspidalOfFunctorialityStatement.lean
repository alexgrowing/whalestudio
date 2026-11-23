import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsCuspidalOfFunctoriality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifts_cuspidal_of_functoriality : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | exact GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems | (intros; apply GlobalTheory.PairLift.liftsCuspidal_of_classicalTheorems <;> assumption)
