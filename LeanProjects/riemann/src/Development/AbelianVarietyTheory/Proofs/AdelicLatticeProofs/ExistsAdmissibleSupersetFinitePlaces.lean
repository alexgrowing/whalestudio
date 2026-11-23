import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem intValuation_of_span_eq_mul {R : Type} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) (I : Ideal R) (hI : I ≠ 0) (hv : ¬ v.asIdeal ∣ I) (x : R)
    (hx0 : x ≠ 0) (hx : v.asIdeal * I = Ideal.span {x}) :
    v.intValuation x = WithZero.exp (-1) := by
  have hvd : v.asIdeal ∣ Ideal.span {x} := ⟨I, hx.symm⟩
  have hsq : ¬ v.asIdeal ^ 2 ∣ Ideal.span {x} := by
    rintro ⟨J, hJ⟩
    apply hv
    rw [← hx, pow_two, mul_assoc] at hJ
    exact ⟨J, mul_left_cancel₀ v.ne_bot hJ⟩
  have h1 : v.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_dvd x 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => hsq ((v.intValuation_le_pow_iff_dvd x 2).1 h)
  have hne : v.intValuation x ≠ 0 := v.intValuation_ne_zero x hx0
  rw [← WithZero.exp_log hne] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

theorem exists_admissible_superset_finite_places : ∀ (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))), ∃ S, S₀ ⊆ S ∧ admitted F S := by
  intro F _ _ S₀
  classical
  choose J hJ using fun c : ClassGroup (𝓞 F) => ClassGroup.mk0_surjective c
  have h2 : (2 : 𝓞 F) ≠ 0 := two_ne_zero
  have hprod : (∏ c : ClassGroup (𝓞 F), (J c : Ideal (𝓞 F))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro c _
    exact nonZeroDivisors.coe_ne_zero (J c)
  have hs : Ideal.span {(2 : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h2
  obtain ⟨M, hM, hM2, hMJ⟩ : ∃ M : Ideal (𝓞 F), M ≠ 0 ∧ Ideal.span {(2 : 𝓞 F)} ∣ M ∧
      ∀ c, (J c : Ideal (𝓞 F)) ∣ M :=
    ⟨_, mul_ne_zero hs hprod, dvd_mul_right _ _,
      fun c => dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ c)) _⟩
  obtain ⟨S, hS0, hSM⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u.asIdeal ∣ M → u ∈ S :=
    ⟨S₀ ∪ (Ideal.finite_factors hM).toFinset, Finset.subset_union_left,
      fun u h => Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)⟩
  have hout : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ¬ u.asIdeal ∣ M :=
    fun u hu h => hu (hSM u h)
  have houtJ : ∀ u : HeightOneSpectrum (𝓞 F), u ∉ S → ∀ c, ¬ u.asIdeal ∣ (J c : Ideal (𝓞 F)) :=
    fun u hu c h => hout u hu (h.trans (hMJ c))
  refine ⟨S, hS0, ?_⟩
  intro v hv
  refine ⟨?_, ?_⟩
  · have h2 : ¬ v.asIdeal ∣ Ideal.span {(2 : 𝓞 F)} := fun h => hout v hv (h.trans hM2)
    have key : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun hm => h2 (Ideal.dvd_span_singleton.2 hm)
    rwa [map_ofNat] at key
  · let P : nonZeroDivisors (Ideal (𝓞 F)) := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
    let c : ClassGroup (𝓞 F) := (ClassGroup.mk0 P)⁻¹
    have hprod : ClassGroup.mk0 (P * J c) = 1 := by
      rw [map_mul, hJ c, mul_inv_cancel]
    have hprin : (v.asIdeal * (J c : Ideal (𝓞 F))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (P * J c).2).1 hprod
    obtain ⟨y, hy⟩ := hprin.principal
    have hy' : v.asIdeal * (J c : Ideal (𝓞 F)) = Ideal.span {y} := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
      exact (mul_ne_zero v.ne_bot (nonZeroDivisors.coe_ne_zero (J c))) hy'
    refine ⟨algebraMap (𝓞 F) F y, ?_, ?_⟩
    · rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_of_span_eq_mul v _ (nonZeroDivisors.coe_ne_zero _) (houtJ v hv c) y hy0 hy'
    · intro w hw hwv
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hyw
      have hdvd : w.asIdeal ∣ v.asIdeal * (J c : Ideal (𝓞 F)) := by
        rw [hy']
        exact Ideal.dvd_span_singleton.2 hyw
      rcases (Ideal.prime_of_isPrime w.ne_bot w.isPrime).dvd_or_dvd hdvd with h | h
      · apply hwv
        have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd h
        exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
      · exact houtJ w hw c h

end GlobalTheory.QNorm
