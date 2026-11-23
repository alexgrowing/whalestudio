import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.LidxAntisymm

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem length_quot_pow (P : HeightOneSpectrum R) (k : ℕ) :
    Module.length R (R ⧸ P.asIdeal ^ k) = k := by
  haveI := P.isMaximal
  let Rₚ := Localization.AtPrime P.asIdeal
  haveI : IsDiscreteValuationRing Rₚ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot Rₚ
  let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow P.asIdeal Rₚ k
  rw [e.toLinearEquiv.length_eq]
  have hs1 : Function.Surjective (algebraMap R (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) := by
    intro q
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm q)
    refine ⟨r, ?_⟩
    have h1 : e (Ideal.Quotient.mk _ r) = q := by rw [hr]; simp
    rw [← h1, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
    rfl
  have hs2 : Function.Surjective (algebraMap Rₚ (Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ k)) :=
    Ideal.Quotient.mk_surjective
  rw [Module.length_eq_of_surjective hs1, ← Module.length_eq_of_surjective hs2,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

variable (K) in

abbrev cI (J : Ideal R) : Submodule R K := ((J : FractionalIdeal (nonZeroDivisors R) K) : Submodule R K)

theorem mem_cI {J : Ideal R} {x : K} : x ∈ cI K J ↔ ∃ y ∈ J, algebraMap R K y = x := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal]

theorem algebraMap_mem_cI {J : Ideal R} {y : R} : algebraMap R K y ∈ cI K J ↔ y ∈ J := by
  rw [mem_cI]
  constructor
  · rintro ⟨z, hz, he⟩
    rwa [← (IsFractionRing.injective R K) he]
  · intro h; exact ⟨y, h, rfl⟩

theorem smul_algebraMap (s y : R) : s • algebraMap R K y = algebraMap R K (s * y) := by
  rw [Algebra.smul_def, map_mul]

theorem relativeLength_localized_pow (P : HeightOneSpectrum R) (k : ℕ) :
    relative₂ (localization₂ P.asIdeal (cI K (P.asIdeal ^ k))) (localization₂ P.asIdeal (1 : Submodule R K)) = k := by
  haveI := P.isMaximal
  set p := P.asIdeal
  set Z := localization₂ p (1 : Submodule R K)
  set X := localization₂ p (cI K (p ^ k))
  have hZ : ∀ r : R, Algebra.linearMap R K r ∈ Z := fun r =>
    le_locP p _ (Submodule.mem_one.mpr ⟨r, rfl⟩)
  let φ : R →ₗ[R] Z := LinearMap.codRestrict Z (Algebra.linearMap R K) hZ
  let ψ : R →ₗ[R] (Z ⧸ X.comap Z.subtype) := (X.comap Z.subtype).mkQ.comp φ

  have hunit : ∀ t : R, t ∉ p → ∃ t' : R, t * t' - 1 ∈ p ^ k := by
    intro t ht
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) ht)
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨t', ?_⟩
    rw [← Ideal.Quotient.eq, map_mul, hb, map_one]
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H z =>
      obtain ⟨y, hy⟩ := z
      obtain ⟨t, ht, hty⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hty
      obtain ⟨t', ht'⟩ := hunit t ht
      refine ⟨r * t', ?_⟩
      simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, φ,
        LinearMap.codRestrict_apply, Algebra.linearMap_apply]
      refine ⟨t, ht, ?_⟩
      rw [smul_sub, ← hr, smul_algebraMap, ← map_sub, algebraMap_mem_cI]
      have : t * (r * t') - r = r * (t * t' - 1) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ ht'
  have hker : LinearMap.ker ψ = p ^ k := by
    ext r
    simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, φ,
      LinearMap.codRestrict_apply, Algebra.linearMap_apply]
    constructor
    · rintro ⟨s, hs, hsr⟩
      rw [smul_algebraMap, algebraMap_mem_cI] at hsr
      have hu := Ideal.Quotient.isUnit_mk_pow_of_notMem p (n := k) hs
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hsr ⊢
      rw [map_mul] at hsr
      exact (hu.mul_right_eq_zero).mp hsr
    · intro hr
      exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, algebraMap_mem_cI]; exact hr⟩
  have e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)
  unfold relative₂
  rw [← e.length_eq, length_quot_pow]

theorem localization_cI_eq (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    localization₂ P.asIdeal (cI K J) =
      localization₂ P.asIdeal (cI K (P.asIdeal ^ (Associates.mk P.asIdeal).count (Associates.mk J).factors)) := by
  set k := (Associates.mk P.asIdeal).count (Associates.mk J).factors
  have hdvd : P.asIdeal ^ k ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) P.associates_irreducible]
  obtain ⟨J', hJ'⟩ := hdvd
  have hJ'0 : J' ≠ 0 := by rintro rfl; exact hJ (by simpa using hJ')
  have hpk0 : P.asIdeal ^ k ≠ 0 := pow_ne_zero _ P.ne_bot

  have hc : FractionalIdeal.count K P (J' : FractionalIdeal (nonZeroDivisors R) K) = 0 := by
    have h1 := FractionalIdeal.count_coe K P hJ
    rw [hJ', FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_mul K P
      (FractionalIdeal.coeIdeal_ne_zero.mpr hpk0) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0),
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at h1
    rw [← hJ'] at h1
    change (k : ℤ) + _ = (k : ℤ) at h1
    linarith
  have hnot : ¬ J' ≤ P.asIdeal := by
    intro hle
    have h2 := FractionalIdeal.count_mono K P (FractionalIdeal.coeIdeal_ne_zero.mpr hJ'0)
      (FractionalIdeal.coeIdeal_le_coeIdeal K |>.mpr hle)
    rw [hc, FractionalIdeal.count_self] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨s, hsJ', hsP⟩ := Set.not_subset.mp hnot
  apply le_antisymm
  · apply localization_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_cI.mp hx
    rw [algebraMap_mem_cI]
    rw [hJ'] at hy
    exact (Ideal.mul_le_inf.trans inf_le_left : P.asIdeal ^ k * J' ≤ P.asIdeal ^ k) hy
  · rintro x ⟨t, ht, htx⟩
    obtain ⟨y, hy, hyx⟩ := mem_cI.mp htx
    refine ⟨s * t, ?_, ?_⟩
    · intro hst
      rcases Ideal.IsPrime.mem_or_mem (inferInstance) hst with h | h
      · exact hsP h
      · exact ht h
    · rw [mul_smul, ← hyx, smul_algebraMap, algebraMap_mem_cI, hJ']
      have := Ideal.mul_mem_mul hy hsJ'
      rwa [mul_comm y s] at this

theorem relativeLength_localized_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal (cI K J)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      (Associates.mk P.asIdeal).count (Associates.mk J).factors := by
  rw [localization_cI_eq P hJ, relativeLength_localized_pow]

end PI.IsoDetW.Loc
