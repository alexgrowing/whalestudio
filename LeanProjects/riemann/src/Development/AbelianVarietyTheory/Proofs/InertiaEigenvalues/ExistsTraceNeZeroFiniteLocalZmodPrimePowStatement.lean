import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNeZeroFiniteLocalZmodPrimePow
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_ne_zero_finite_local_zmod_prime_pow : ∀ (l b e : ℕ) [Fact l.Prime] (B : Type) [CommRing B] [Finite B] [Algebra (ZMod (l ^ b)) B] (π : B), 0 < e → (∀ x : B, ¬ IsUnit x ↔ π ∣ x) → Ideal.span {((l : ℕ) : B)} = Ideal.span {π ^ e} → Nat.card B = Nat.card (B ⧸ Ideal.span {π}) ^ (b * e) → ¬ l ^ b ∣ e → ∃ c : B, Algebra.trace (ZMod (l ^ b)) B c ≠ 0 := by
  first | exact @GlobalTheory.LocalTraceNonzero.exists_trace_ne_zero | exact GlobalTheory.LocalTraceNonzero.exists_trace_ne_zero | (intros; apply GlobalTheory.LocalTraceNonzero.exists_trace_ne_zero <;> assumption)
