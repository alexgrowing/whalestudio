import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowDivPrimeZpowIntegralClosureUnit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_div_prime_zpow_integralClosure_unit : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, x ≠ 0 → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ IsInt p (x ^ b / (p : Ω) ^ a) ∧
    IsInt p ((p : Ω) ^ a / x ^ b) := by
  first | exact @GlobalTheory.K5.exists_pow_div_p_zpow_isInt | exact GlobalTheory.K5.exists_pow_div_p_zpow_isInt | (intros; apply GlobalTheory.K5.exists_pow_div_p_zpow_isInt <;> assumption)
