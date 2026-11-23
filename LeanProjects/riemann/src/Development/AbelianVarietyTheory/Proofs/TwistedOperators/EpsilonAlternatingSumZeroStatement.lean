import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsilonAlternatingSumZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_alternating_sum_zero : ∀ (k : ℕ) (P S : Finset (SV k)), IsPar P → S ⊆ P → S ≠ P → ∀ l ∈ generic k, ∑ R ∈ between P S, (-1 : ℂ) ^ (P \ R).card * epsHat P R l * eps R S l = 0 := by
  first | exact @GlobalTheory.Chamber.langlands_fourier_sum | exact GlobalTheory.Chamber.langlands_fourier_sum | (intros; apply GlobalTheory.Chamber.langlands_fourier_sum <;> assumption)
