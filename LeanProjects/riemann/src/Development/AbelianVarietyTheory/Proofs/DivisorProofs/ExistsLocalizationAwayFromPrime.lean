import Mathlib
open NumberField

namespace GlobalTheory

theorem exists_subring_pid_localization_coprime :
    ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∃ R : Subring F, IsPrincipalIdealRing R ∧
    ∀ x : F, x ∈ R ↔ ∃ s : ℕ, s.Coprime p ∧ IsIntegral ℤ ((s : F) * x) := by
  intro F _ _ p hp
  haveI hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  let S : Submonoid (𝓞 F) := Algebra.algebraMapSubmonoid (𝓞 F) (Ideal.span {(p : ℤ)}).primeCompl
  have hS : S ≤ nonZeroDivisors (𝓞 F) := by
    rintro _ ⟨n, hn, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    have hn0 : n ≠ 0 := by rintro rfl; exact hn (Ideal.zero_mem _)
    simpa using hn0
  let R := Localization.subalgebra.ofField F S hS
  haveI : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 F) hS R
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simp [hp.ne_zero]
  have hR : IsPrincipalIdealRing R :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 F) (Ideal.span {(p : ℤ)}) hp0 (Sₚ := R)
  refine ⟨R.toSubring, hR, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨a, _, ⟨n, hn, rfl⟩, rfl⟩
    have hnd : ¬ (p : ℤ) ∣ n := fun hd => hn (Ideal.mem_span_singleton.2 hd)
    have hn0 : n ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
    have hn0' : (n : F) ≠ 0 := by exact_mod_cast hn0
    refine ⟨n.natAbs, Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      fun h => hnd (Int.natCast_dvd.2 h)), ?_⟩
    have ha : IsIntegral ℤ (algebraMap (𝓞 F) F a) := RingOfIntegers.isIntegral_coe a
    have hc : algebraMap (𝓞 F) F (algebraMap ℤ (𝓞 F) n) = (n : F) := by simp
    rw [hc]
    rcases Int.natAbs_eq n with h | h
    · have e : ((n.natAbs : ℕ) : F) = (n : F) := by
        conv_rhs => rw [h]
        exact (Int.cast_natCast n.natAbs).symm
      have : ((n.natAbs : ℕ) : F) * (algebraMap (𝓞 F) F a * (n : F)⁻¹) = algebraMap (𝓞 F) F a := by
        rw [e]; field_simp
      rw [this]; exact ha
    · have e : ((n.natAbs : ℕ) : F) = -(n : F) := by
        conv_rhs => rw [h]
        rw [Int.cast_neg, Int.cast_natCast, neg_neg]
      have : ((n.natAbs : ℕ) : F) * (algebraMap (𝓞 F) F a * (n : F)⁻¹) = -algebraMap (𝓞 F) F a := by
        rw [e]; field_simp
      rw [this]; exact ha.neg
  · rintro ⟨s, hs, hx⟩
    have hnd : ¬ p ∣ s := (Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm
    have hs0 : s ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
    have hs0' : (s : F) ≠ 0 := by exact_mod_cast hs0
    refine ⟨⟨(s : F) * x, hx⟩, algebraMap ℤ (𝓞 F) (s : ℤ), ⟨(s : ℤ), ?_, rfl⟩, ?_⟩
    · intro h
      exact hnd (Int.natCast_dvd_natCast.1 (Ideal.mem_span_singleton.1 h))
    · have hc : algebraMap (𝓞 F) F (algebraMap ℤ (𝓞 F) (s : ℤ)) = (s : F) := by simp
      rw [hc]
      change x = (s : F) * x * (s : F)⁻¹
      field_simp

end GlobalTheory
