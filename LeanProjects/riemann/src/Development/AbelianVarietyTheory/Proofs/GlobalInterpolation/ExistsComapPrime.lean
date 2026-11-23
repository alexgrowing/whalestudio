import Mathlib

namespace GlobalTheory.ComapPrimeExistence

open NumberField IsDedekindDomain

theorem exists_comap_prime {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (φ : E →+* K) (w : HeightOneSpectrum (RingOfIntegers K)) :
    ∃ Q : HeightOneSpectrum (RingOfIntegers E), ∀ r : RingOfIntegers E,
      r ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingHom φ : RingOfIntegers E → RingOfIntegers K) r ∈ w.asIdeal := by
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom φ), Ideal.comap_isPrime _ _, ?_⟩,
    fun r => Ideal.mem_comap⟩
  intro h
  have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : RingOfIntegers E) ∈
      w.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hmem
  exact hn (Nat.cast_eq_zero.mp hmem)

end GlobalTheory.ComapPrimeExistence
