import Mathlib

namespace GlobalTheory.HeightOnePrimeMembership

open NumberField

theorem exists_heightOne_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers E),
      (p : RingOfIntegers E) ∈ w.asIdeal := by
  have hnu : ¬ IsUnit (p : RingOfIntegers E) := by
    intro hu
    have h1 : IsUnit (Algebra.norm ℤ (p : RingOfIntegers E)) := hu.map _
    have h2 : (p : RingOfIntegers E) = algebraMap ℤ (RingOfIntegers E) (p : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have hpos : Module.finrank ℤ (RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (p : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h3
  have hne : Ideal.span {(p : RingOfIntegers E)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (p : RingOfIntegers E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hp0 : (p : RingOfIntegers E) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro hb
  rw [hb] at hmem
  exact hp0 (by simpa using hmem)

end GlobalTheory.HeightOnePrimeMembership
