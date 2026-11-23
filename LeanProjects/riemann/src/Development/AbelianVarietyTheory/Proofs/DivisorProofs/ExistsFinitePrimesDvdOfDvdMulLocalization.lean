import Mathlib

namespace GlobalTheory

theorem localizedModule_mk_quotient_eq_zero_iff_dvd {R : Type} [CommRing R] (M : Submonoid R)
    (s c : R) :
    LocalizedModule.mkLinearMap M (R ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ c) = 0 ↔
      algebraMap R (Localization M) s ∣ algebraMap R (Localization M) c := by
  rw [IsLocalizedModule.eq_zero_iff M, ← Ideal.mem_span_singleton, ← Set.image_singleton,
    ← Ideal.map_span, IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  have key : ∀ m : R, m • (Ideal.Quotient.mk (Ideal.span {s}) c) = 0 ↔
      m * c ∈ Ideal.span {s} := by
    intro m
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    rfl
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, m.2, (key m).1 hm⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨⟨m, hm⟩, (key m).2 h⟩

theorem exists_finite_primes_dvd_of_dvd_mul_localization :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : R), s ≠ 0 → ∃ S : Set (PrimeSpectrum R), S.Finite ∧ ∀ (P : PrimeSpectrum R) (τ g : Localization.AtPrime P.asIdeal), (∀ Q ∈ S, Q ≤ P → τ ∉ Q.asIdeal.map (algebraMap R (Localization.AtPrime P.asIdeal))) → algebraMap R _ s ∣ g * τ → algebraMap R _ s ∣ g := by
  intro R _ _ _ s _
  refine ⟨PrimeSpectrum.asIdeal ⁻¹' associatedPrimes R (R ⧸ Ideal.span {s}),
    (associatedPrimes.finite R _).preimage (fun _ _ _ _ h => PrimeSpectrum.ext h), ?_⟩
  intro P τ g hτ hd
  obtain ⟨a, v, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl τ
  obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl g
  have hab : algebraMap R (Localization.AtPrime P.asIdeal) s ∣ algebraMap R _ (a * b) := by
    rw [← IsLocalization.mk'_mul] at hd
    have h := hd.mul_right (algebraMap R _ ((u * v : P.asIdeal.primeCompl) : R))
    rwa [IsLocalization.mk'_spec, mul_comm b a] at h
  by_contra hg
  have hb : ¬ algebraMap R (Localization.AtPrime P.asIdeal) s ∣ algebraMap R _ b := by
    intro h
    apply hg
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact h.mul_right _
  have hx := mt (localizedModule_mk_quotient_eq_zero_iff_dvd P.asIdeal.primeCompl s b).1 hb
  have hax := (localizedModule_mk_quotient_eq_zero_iff_dvd P.asIdeal.primeCompl s (a * b)).2 hab
  obtain ⟨q, hq, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing (Localization P.asIdeal.primeCompl) _ hx
  have hqp : q.IsPrime := hq.isPrime
  have haq : algebraMap R (Localization P.asIdeal.primeCompl) a ∈ q := by
    apply hle
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, algebraMap_smul, ← map_smul, ← hax,
      map_mul]
    rfl
  have hQ : q.comap (algebraMap R (Localization P.asIdeal.primeCompl)) ∈
      associatedPrimes R (R ⧸ Ideal.span {s}) :=
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      P.asIdeal.primeCompl (LocalizedModule.mkLinearMap P.asIdeal.primeCompl _) q hq
      (IsNoetherian.noetherian _)
  refine hτ ⟨q.comap (algebraMap R (Localization P.asIdeal.primeCompl)), hqp.comap _⟩ hQ ?_ ?_
  · intro r hr
    by_contra hrP
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem q hr
      (IsLocalization.map_units (Localization P.asIdeal.primeCompl)
        (⟨r, hrP⟩ : P.asIdeal.primeCompl)))
  · rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haq)

end GlobalTheory
