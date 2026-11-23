import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingFunctionBound
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_function_bound : GlobalTheory.BigTop.Fun.Scale := by
  first | exact @GlobalTheory.BigTop.Fun.existsIntegralMultiple | exact GlobalTheory.BigTop.Fun.existsIntegralMultiple | (intros; apply GlobalTheory.BigTop.Fun.existsIntegralMultiple <;> assumption)
