import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzero
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_sum_normSq_eq_one_single_nonzero : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l → ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ), ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 → ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  first | (exact @GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (exact GlobalTheory.cyclo_sum_mul_star_eq_one_single) | (intros; apply GlobalTheory.cyclo_sum_mul_star_eq_one_single <;> assumption)
