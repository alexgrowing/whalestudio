import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumConstantOfDeepGood
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_constant_of_deep_good : DeepGood → SumC := by
  first | exact @GlobalTheory.CovTop.sumC_of_deepGood | exact GlobalTheory.CovTop.sumC_of_deepGood | (intros; apply GlobalTheory.CovTop.sumC_of_deepGood <;> assumption)
