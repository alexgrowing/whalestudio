import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedSpanIsPrimeAndNotMem
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerDistinguished_span_isPrime_and_not_mem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → ¬ IsUnit x → IsAdicComplete (Ideal.span {x}) O → ∀ (e : ℕ) (w E' : WittVector l O), 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → (Ideal.span {E'}).IsPrime ∧ ((l : ℕ) : WittVector l O) ∉ Ideal.span {E'} := by
  first | exact @GlobalTheory.teichmuller_distinguished_span_isPrime | exact GlobalTheory.teichmuller_distinguished_span_isPrime | (intros; apply GlobalTheory.teichmuller_distinguished_span_isPrime <;> assumption)
