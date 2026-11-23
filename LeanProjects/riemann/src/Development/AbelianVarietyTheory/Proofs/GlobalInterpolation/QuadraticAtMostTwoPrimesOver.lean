import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quadratic_at_most_two_primes_over (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (q : ℕ) (hq : q.Prime)
    (P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K))
    (h₁ : ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal) (h₂ : ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal)
    (h₃ : ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal) : P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have hN : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
    simp
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := fun P hP =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hqd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      q ∣ Ideal.absNorm P.asIdeal := by
    intro P hP
    have h1 : Ideal.absNorm P.asIdeal ∣ q ^ 2 := hN ▸ map_dvd Ideal.absNorm (hd P hP)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).mp h1
    rcases i with _ | i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hi
      exact P.isPrime.ne_top hi
    · rw [hi]; exact dvd_pow_self q (Nat.succ_ne_zero i)
  have hc : ∀ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q → IsCoprime P.asIdeal Q.asIdeal := by
    intro P Q h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact P.isMaximal.coprime_of_ne Q.isMaximal (fun e => h (HeightOneSpectrum.ext e))
  have hprod : P₁.asIdeal * P₂.asIdeal * P₃.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} :=
    IsCoprime.mul_dvd (IsCoprime.mul_left (hc _ _ h13) (hc _ _ h23))
      (IsCoprime.mul_dvd (hc _ _ h12) (hd _ h₁) (hd _ h₂)) (hd _ h₃)
  have h4 := map_dvd Ideal.absNorm hprod
  rw [hN, map_mul, map_mul] at h4
  have h5 : q * q * q ∣ q ^ 2 :=
    (mul_dvd_mul (mul_dvd_mul (hqd _ h₁) (hqd _ h₂)) (hqd _ h₃)).trans h4
  have h6 : q ^ 3 ∣ q ^ 2 := by rwa [show q ^ 3 = q * q * q by ring]
  have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h6
  omega

end GlobalTheory
