import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianOfQuoted
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_riemann_roch_abelian_of_quoted : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → GlobalTheory.Published.ArithRiemannRochAbelian := by
  first | exact @GlobalTheory.AbelianRR.main | exact GlobalTheory.AbelianRR.main | (intros; apply GlobalTheory.AbelianRR.main <;> assumption)
