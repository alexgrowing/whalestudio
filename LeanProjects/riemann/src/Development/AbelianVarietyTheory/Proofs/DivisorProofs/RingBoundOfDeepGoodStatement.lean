import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingBoundOfDeepGood
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_bound_of_deep_good : Hypotheses2 → Gram → DeepGood → Ring := by
  first | exact @GlobalTheory.CovTop.RingStep.ring_of | exact GlobalTheory.CovTop.RingStep.ring_of | (intros; apply GlobalTheory.CovTop.RingStep.ring_of <;> assumption)
