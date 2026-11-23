import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomApplyEqPowOfPowPowEqSelf
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_apply_eq_pow_prime_pow : ∀ {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (τ : k →+* k) (N : ℕ), 0 < N → ∀ (z : k), z ^ p ^ N = z → ∃ e : ℕ, τ z = z ^ p ^ e := by
  first | exact @GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self | exact GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self | (intros; apply GlobalTheory.ringHom_apply_eq_pow_of_pow_pow_eq_self <;> assumption)
