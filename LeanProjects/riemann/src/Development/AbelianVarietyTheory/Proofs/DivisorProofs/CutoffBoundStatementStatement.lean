import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_bound_statement : Hypotheses2 → Cut := by
  first | exact @GlobalTheory.CovTop.cut_of_hypotheses | exact GlobalTheory.CovTop.cut_of_hypotheses | (intros; apply GlobalTheory.CovTop.cut_of_hypotheses <;> assumption)
