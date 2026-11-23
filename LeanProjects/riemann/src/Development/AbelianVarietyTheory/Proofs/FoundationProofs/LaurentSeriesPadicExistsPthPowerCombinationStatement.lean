import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentSeriesPadic_exists_pthPower_combination : ∀ (p : ℕ) [Fact p.Prime] (f : Lau p), ∃ (g : Fin p → Lau p) (h : Lau p), f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  first | exact @GlobalTheory.K5.LauZ.exists_pow_comb | exact GlobalTheory.K5.LauZ.exists_pow_comb | (intros; apply GlobalTheory.K5.LauZ.exists_pow_comb <;> assumption)
