import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLe
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_level_tail_mul_log_primes_le : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  first | exact @GlobalTheory.TailPrimeSum.main | exact GlobalTheory.TailPrimeSum.main | (intros; apply GlobalTheory.TailPrimeSum.main <;> assumption)
