import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealPowNatCastDvdFiniteIntegersAlgebra
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra : ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [IsLocalRing A] (a : A), a ∈ IsLocalRing.maximalIdeal A → ∃ N : ℕ, (p : A) ∣ a ^ N := by
  first | exact @GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | exact GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers | (intros; apply GlobalTheory.maxIdeal_pow_dvd_natCast_of_integers <;> assumption)
