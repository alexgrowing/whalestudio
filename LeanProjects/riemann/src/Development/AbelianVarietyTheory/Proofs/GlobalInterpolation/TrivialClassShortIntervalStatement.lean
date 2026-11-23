import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  first | exact @GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | exact GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | (intros; apply GlobalTheory.Hk.ShortInt.trivialClass_shortInterval <;> assumption)
