import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_bound_statement : Hypotheses2 → Gram := by
  first | exact @GlobalTheory.CovTop.gram_of_hypotheses | exact GlobalTheory.CovTop.gram_of_hypotheses | (intros; apply GlobalTheory.CovTop.gram_of_hypotheses <;> assumption)
