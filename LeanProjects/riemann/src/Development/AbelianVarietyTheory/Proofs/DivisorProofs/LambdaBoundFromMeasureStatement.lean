import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_bound_from_measure : Hypotheses2 → Gram → Meas → abelian₂ := by
  first | exact @GlobalTheory.CovTop.LamAll.lam | exact GlobalTheory.CovTop.LamAll.lam | (intros; apply GlobalTheory.CovTop.LamAll.lam <;> assumption)
