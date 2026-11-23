import Mathlib

namespace GlobalTheory.IsolatedTheoremFour

open IsDedekindDomain

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  intro K _ _ l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  exact ⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩

end GlobalTheory.IsolatedTheoremFour
