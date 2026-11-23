import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDoma

noncomputable section

namespace GlobalTheory.K5

variable (p : ℕ) [Fact p.Prime]

theorem natCast_dvd_iff_evalₐ_one (x : O0 p) :
    (p : O0 p) ∣ x ↔ AdicCompletion.evalₐ (pI p) 1 x = 0 := by
  rw [GlobalTheory.ValCompletion.evalₐ_eq_zero_iff rfl, pow_one, map_natCast]

theorem prime_natCast_completedLaurentRing : Prime (p : O0 p) := by
  haveI : (pI p ^ 1).IsPrime := by
    rw [pow_one]; exact (Ideal.span_singleton_prime (Basic.prime_lau p).ne_zero).2 (Basic.prime_lau p)
  refine ⟨?_, Basic.not_isUnit_p p, ?_⟩
  · exact_mod_cast (Nat.Prime.ne_zero Fact.out : p ≠ 0)
  · intro a b h
    rw [natCast_dvd_iff_evalₐ_one, map_mul] at h
    rw [natCast_dvd_iff_evalₐ_one, natCast_dvd_iff_evalₐ_one]
    exact mul_eq_zero.1 h

theorem prime_natCast_completedLaurentRing_of_prime : ∀ (p : ℕ) [Fact p.Prime], Prime (p : O0 p) := fun p _ => prime_natCast_completedLaurentRing p

end GlobalTheory.K5
