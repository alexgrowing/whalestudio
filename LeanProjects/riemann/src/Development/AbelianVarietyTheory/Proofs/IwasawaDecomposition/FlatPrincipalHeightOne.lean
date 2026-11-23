import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemAssociatedOfMapEq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
open IsLocalRing

namespace GlobalTheory.PrincipalDescent

theorem exists_not_mem_dvd_of_algebraMap_dvd {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime]
    {x y : R}
    (hd : algebraMap R (Localization.AtPrime P) y ∣ algebraMap R (Localization.AtPrime P) x) :
    ∃ s ∉ P, y ∣ s * x := by
  obtain ⟨z, hz⟩ := hd
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj P.primeCompl z
  have e : algebraMap R (Localization.AtPrime P) (x * t) =
      algebraMap R (Localization.AtPrime P) (y * r) := by
    rw [map_mul, map_mul, hz, ← hrt, mul_assoc]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl _).mp e
  refine ⟨c * t, P.primeCompl.mul_mem c.2 t.2, ⟨c * r, ?_⟩⟩
  linear_combination hc

theorem algebraMap_dvd_of_mem_map_span {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime]
    {x y : R} (hx : algebraMap R (Localization.AtPrime P) x ∈
      (Ideal.span {y}).map (algebraMap R (Localization.AtPrime P))) :
    algebraMap R (Localization.AtPrime P) y ∣ algebraMap R (Localization.AtPrime P) x := by
  rwa [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hx

end GlobalTheory.PrincipalDescent

namespace GlobalTheory.PrincipalDescent

theorem exists_dvd_dvd_of_height_eq_one {A R : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (φ : A →+* R) (hfl : φ.Flat) (hloc : IsLocalHom φ) (h : R)
    (hh : h ≠ 0)
    (h1 : ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ = ⊥ → h ∉ Q)
    (h2 : ∀ q : Ideal A, q ≠ ⊥ → ∃ n : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 →
      Q.comap φ = q → (Ideal.span {h}).map (algebraMap R (Localization.AtPrime Q)) =
        (q ^ n).map ((algebraMap R (Localization.AtPrime Q)).comp φ))
    (Q : Ideal R) [hQ : Q.IsPrime] (hQ1 : Q.height = 1) :
    ∃ a : A, h ∣ φ a ∧ ∃ s ∉ Q, φ a ∣ s * h := by
  classical
  have hinj : Function.Injective φ := GlobalTheory.CdvrExt.injective_of_flat_local φ hfl
  have hqP : (Q.comap φ).IsPrime := Ideal.comap_isPrime φ Q

  have hdiv : ∀ (p : Ideal A) (n : ℕ) (P : Ideal R) [P.IsPrime],
      (Ideal.span {h}).map (algebraMap R (Localization.AtPrime P)) =
        (p ^ n).map ((algebraMap R (Localization.AtPrime P)).comp φ) →
      ∀ c ∈ p ^ n, ∃ s ∉ P, h ∣ s * φ c := by
    intro p n P _ hn c hc
    refine exists_not_mem_dvd_of_algebraMap_dvd P (algebraMap_dvd_of_mem_map_span P ?_)
    have := Ideal.mem_map_of_mem ((algebraMap R (Localization.AtPrime P)).comp φ) hc
    rwa [← hn] at this

  have hnotle : ∀ (P : Ideal R) [P.IsPrime], P.comap φ ≠ ⊥ → P.comap φ ≤ Q.comap φ →
      P.comap φ = Q.comap φ := by
    intro P _ hne hle
    by_contra hne'
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hfl
    haveI : Q.LiesOver (Q.comap φ) := ⟨rfl⟩
    obtain ⟨P', hP'Q, hP', hlo⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := P.comap φ) Q (lt_of_le_of_ne hle hne')
    have hlt := Ideal.height_strict_mono_of_isPrime hP'Q
    rw [hQ1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at hlt
    apply hne
    rw [hlo.over, hlt]
    ext x
    simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun hx => hinj (by rw [map_zero]; exact hx), fun hx => by rw [hx, map_zero]⟩

  obtain ⟨g, hg1, s₁, hs₁, hg2⟩ : ∃ g : A, (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
      P.comap φ = Q.comap φ → ∃ s ∉ P, h ∣ s * φ g) ∧ ∃ s₁ ∉ Q, φ g ∣ s₁ * h := by
    by_cases hq : Q.comap φ = ⊥
    · refine ⟨1, fun P _ hP hPq => ⟨h, h1 P hP (hPq.trans hq), by simp⟩, 1, ?_, by simp⟩
      exact fun h0 => hQ.ne_top ((Ideal.eq_top_iff_one _).mpr h0)
    · obtain ⟨n, hn⟩ := h2 _ hq
      have hh' : algebraMap R (Localization.AtPrime Q) h ≠ 0 :=
        IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ Q.primeCompl_le_nonZeroDivisors
          (mem_nonZeroDivisors_of_ne_zero hh)
      obtain ⟨g, hg, hga⟩ := GlobalTheory.DivDescent.exists_mem_associated_of_map_eq
        ((algebraMap R (Localization.AtPrime Q)).comp φ) (Q.comap φ ^ n) hh'
        (by rw [← hn Q hQ1 rfl, Ideal.map_span, Set.image_singleton])
      refine ⟨g, fun P _ hP hPq => hdiv _ n P (hn P hP hPq) g hg, ?_⟩
      exact exists_not_mem_dvd_of_algebraMap_dvd Q hga.dvd

  have hc : ∀ P : PrimeSpectrum R, ∃ c : A, c ∉ Q.comap φ ∧ (P.asIdeal.height = 1 →
      h ∈ P.asIdeal → P.asIdeal.comap φ ≠ Q.comap φ → ∃ s ∉ P.asIdeal, h ∣ s * φ c) := by
    intro P
    by_cases hb : P.asIdeal.height = 1 ∧ h ∈ P.asIdeal ∧ P.asIdeal.comap φ ≠ Q.comap φ
    · obtain ⟨hP, hhP, hPq⟩ := hb
      have hne : P.asIdeal.comap φ ≠ ⊥ := fun e => h1 P.asIdeal hP e hhP
      obtain ⟨n, hn⟩ := h2 _ hne
      obtain ⟨b, hbP, hbq⟩ : ∃ b ∈ P.asIdeal.comap φ, b ∉ Q.comap φ := by
        by_contra! H
        exact hPq (hnotle P.asIdeal hne H)
      refine ⟨b ^ n, fun hm => hbq (hqP.mem_of_pow_mem n hm), fun _ _ _ =>
        hdiv _ n P.asIdeal (hn P.asIdeal hP rfl) _ (Ideal.pow_mem_pow hbP n)⟩
    · exact ⟨1, fun h0 => hqP.ne_top ((Ideal.eq_top_iff_one _).mpr h0),
        fun hP hhP hPq => absurd ⟨hP, hhP, hPq⟩ hb⟩
  choose c hcq hcd using hc
  set T := (GlobalTheory.finite_height_eq_one_mem hh).toFinset
  set b := ∏ P ∈ T, c P with hb
  have hbq : b ∉ Q.comap φ := by
    rw [hb, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨P, -, hP⟩
    exact hcq P hP
  refine ⟨g * b, ?_, φ b * s₁, fun hm => (hQ.mem_or_mem hm).elim hbq hs₁, ?_⟩
  · refine GlobalTheory.dvd_of_forall_height_eq_one hh fun P _ hP hhP => ?_
    by_cases hPq : P.comap φ = Q.comap φ
    · obtain ⟨s, hs, hsd⟩ := hg1 P hP hPq
      refine ⟨s, hs, hsd.trans ?_⟩
      rw [map_mul]
      exact mul_dvd_mul_left s (dvd_mul_right _ _)
    · have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈ T := by
        rw [Set.Finite.mem_toFinset]
        exact ⟨hP, hhP⟩
      obtain ⟨s, hs, hsd⟩ := hcd ⟨P, inferInstance⟩ hP hhP hPq
      refine ⟨s, hs, hsd.trans (mul_dvd_mul_left s ?_)⟩
      rw [map_mul]
      exact (map_dvd φ (Finset.dvd_prod_of_mem c hmem)).trans (dvd_mul_left _ _)
  · rw [map_mul, mul_comm (φ g), mul_assoc]
    exact mul_dvd_mul_left _ hg2

end GlobalTheory.PrincipalDescent
