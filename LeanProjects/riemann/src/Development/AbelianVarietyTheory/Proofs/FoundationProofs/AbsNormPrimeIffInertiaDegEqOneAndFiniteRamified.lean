import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified :
    ∀ (E : Type) [Field E] [NumberField E],
      (∀ P : HeightOneSpectrum (𝓞 E),
        (Ideal.absNorm P.asIdeal).Prime ↔ P.asIdeal.inertiaDeg ℤ = 1) ∧
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by
  intro E _ _
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ := by
    intro P
    haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
    exact ⟨Nat.absNorm_under_prime P.asIdeal,
      (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm⟩
  refine ⟨fun P => ?_, ?_⟩
  · obtain ⟨hq, hN⟩ := key P
    rw [hN]
    constructor
    · intro hpow
      have hf0 : P.asIdeal.inertiaDeg ℤ ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hpow
        exact Nat.not_prime_one hpow
      rcases hpow.eq_one_or_self_of_dvd _ (dvd_pow_self _ hf0) with h1 | h1
      · exact absurd h1 hq.one_lt.ne'
      · exact Nat.pow_right_injective hq.two_le (by simpa using h1.symm)
    · intro h1
      rw [h1, pow_one]
      exact hq
  · set d := (discr E).natAbs with hd_def
    have hd : 0 < d := Int.natAbs_pos.mpr (discr_ne_zero E)
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 E) (d ^ Module.finrank ℤ (𝓞 E))).preimage
      (fun P _ Q _ h => HeightOneSpectrum.ext h)).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hP ⊢
    obtain ⟨hq, -⟩ := key P
    set q := Ideal.absNorm (P.asIdeal.under ℤ) with hq_def
    have hmem := Int.absNorm_under_mem P.asIdeal
    rw [← hq_def] at hmem
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hqd : (q : ℤ) ∣ discr E := by
      by_contra hnd
      have hun := (not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) hqZ).mp hnd
      have hlies : P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
        (Ideal.liesOver_span_iff P.isPrime.ne_top hqZ).mpr (by simpa using hmem)
      exact hP (hun.ramificationIdx_eq_one hlies)
    have hqle : q ≤ d := Nat.le_of_dvd hd (by simpa using Int.natAbs_dvd_natAbs.mpr hqd)
    have hdvd : Ideal.absNorm P.asIdeal ∣ q ^ Module.finrank ℤ (𝓞 E) := by
      have hle : Ideal.span {((q : ℤ) : 𝓞 E)} ≤ P.asIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        simpa using hmem
      have hnorm : Algebra.norm ℤ ((q : ℤ) : 𝓞 E) = (q : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
        rw [← eq_intCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h
    calc Ideal.absNorm P.asIdeal ≤ q ^ Module.finrank ℤ (𝓞 E) :=
          Nat.le_of_dvd (pow_pos hq.pos _) hdvd
      _ ≤ d ^ Module.finrank ℤ (𝓞 E) := Nat.pow_le_pow_left hqle _

end GlobalTheory
