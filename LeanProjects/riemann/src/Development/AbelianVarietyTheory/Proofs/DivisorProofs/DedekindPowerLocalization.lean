import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLocalContinuousCongruenceSection
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_power_localization : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B), f ≠ 0 → ∀ (P : Ideal B), P.IsMaximal → ∃ N : ℕ, ∀ b ∈ P ^ N, ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (exact GlobalTheory.dedekind_pow_maximal_mul_mem_span) | (intros; apply GlobalTheory.dedekind_pow_maximal_mul_mem_span <;> assumption)
