import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecursionOfGramBound
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursion_of_gram_bound : Gram → Rec := by
  first | exact @GlobalTheory.CovTop.rec_of_gram | exact GlobalTheory.CovTop.rec_of_gram | (intros; apply GlobalTheory.CovTop.rec_of_gram <;> assumption)
