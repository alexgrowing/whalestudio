import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_existence_statement : Hypotheses2 → DeepEx := by
  first | exact @GlobalTheory.CovTop.DeepExist.deepEx | exact GlobalTheory.CovTop.DeepExist.deepEx | (intros; apply GlobalTheory.CovTop.DeepExist.deepEx <;> assumption)
