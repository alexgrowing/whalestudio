import Mathlib

open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
