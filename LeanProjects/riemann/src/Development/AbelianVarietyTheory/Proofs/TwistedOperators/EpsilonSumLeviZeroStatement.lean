import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsilonSumLeviZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_sum_levi_zero : ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)) (S : Finset (SV k)), IsLevi 𝔞 → S ∈ parF 𝔞 ∅ → aP S ≠ 𝔞 → ∀ l ∈ generic k, ∑ P ∈ parP 𝔞 S, eps P S l = 0 := by
  first | exact @GlobalTheory.Chamber.sum_eps_eq_zero | exact GlobalTheory.Chamber.sum_eps_eq_zero | (intros; apply GlobalTheory.Chamber.sum_eps_eq_zero <;> assumption)
