import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_under_eq_of_mem_associatedPrimes_of_surjective {A A' M : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] (hs : Function.Surjective (algebraMap A A')) {q : Ideal A}
    (hq : q ∈ associatedPrimes A M) : ∃ q' ∈ associatedPrimes A' M, q'.under A = q := by
  obtain ⟨hp, v, hv⟩ := hq
  set q' : Ideal A' := ((⊥ : Submodule A' M).colon {v}).radical with hq'
  have hunder : q'.under A = q := by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hv]
    simp only [hq', Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot,
      ← map_pow, algebraMap_smul]
  have hmap : q.map (algebraMap A A') = q' := by
    rw [← hunder]
    exact Ideal.map_comap_of_surjective _ hs q'
  have hker : RingHom.ker (algebraMap A A') ≤ q := fun a ha ↦ by
    rw [hv]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← algebraMap_smul A',
      RingHom.mem_ker.1 ha, zero_smul]
  have hprime : q'.IsPrime := hmap ▸ Ideal.map_isPrime_of_surjective hs hker
  exact ⟨q', ⟨hprime, v, rfl⟩, hunder⟩

theorem exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : maximalIdeal S = Ideal.span {t})
    (hreg : IsSMulRegular S t) : ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  have hfac : ∀ y : S, y ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ y = t ^ n * u := by
    intro y hy
    have hinf : (⨅ i : ℕ, maximalIdeal S ^ i) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
    have hex : ∃ n : ℕ, y ∉ maximalIdeal S ^ n := by
      by_contra! h
      exact hy (by simpa [hinf] using (Submodule.mem_iInf _).2 h)
    classical
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ ?_
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
    have h1 : y ∈ maximalIdeal S ^ k := by
      have := Nat.find_min hex (m := k) (by omega)
      simpa using this
    have h2 : y ∉ maximalIdeal S ^ (k + 1) := hk ▸ Nat.find_spec hex
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨u, rfl⟩ := h1
    refine ⟨k, u, ?_, rfl⟩
    by_contra hu
    apply h2
    have hum : u ∈ maximalIdeal S := (mem_maximalIdeal u).2 hu
    rw [ht, Ideal.mem_span_singleton] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨m, u, hu, rfl⟩ := hfac a hne.1
    obtain ⟨n, v, hv, rfl⟩ := hfac b hne.2
    have h0 : t ^ (m + n) • (u * v) = 0 := by
      rw [smul_eq_mul, pow_add]
      linear_combination hab
    have h3 : u * v = 0 := (hreg.pow (m + n)).right_eq_zero_of_smul h0
    exact (hu.mul hv).ne_zero h3
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  refine ⟨hdom, ?_⟩
  have ht0 : t ≠ 0 := fun h ↦ by
    have : IsSMulRegular S (0 : S) := h ▸ hreg
    exact one_ne_zero (this.right_eq_zero_of_smul (zero_smul S (1 : S)))
  have hf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ht]
    simpa using ht0
  refine ((IsDiscreteValuationRing.TFAE S hf).out 4 0).mp ?_
  exact ⟨t, ht⟩

theorem exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 →
      (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) →
      ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) →
        ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro A R _ _ _ _ _ _ _ _ x hx hred P _ hP
  set I : Ideal A := Ideal.span {x} with hI
  have hIR : Ideal.span {algebraMap A R x} = I.map (algebraMap A R) := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  rw [hIR] at hP
  set q : Ideal A := P.under A with hqdef
  have hqp : q.IsPrime := Ideal.IsPrime.under A P

  have hxq : x ∈ q := by
    have h1 := IsAssociatedPrime.annihilator_le hP
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at h1
    exact h1 (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self x))

  have hqA : q ∈ associatedPrimes A (A ⧸ I) := by
    have h0 : q ∈ associatedPrimes A (R ⧸ I.map (algebraMap A R)) :=
      under_mem_associatedPrimes (A := A) hP
    let e : (R ⧸ I.map (algebraMap A R)) ≃ₗ[A] (A ⧸ I) ⊗[A] R :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv.restrictScalars A) ≪≫ₗ
        TensorProduct.comm A R (A ⧸ I)
    rw [LinearEquiv.AssociatedPrimes.eq e] at h0
    obtain ⟨q', hq', hu⟩ := exists_under_eq_of_mem_associatedPrimes_of_surjective (A' := A ⧸ I)
      Ideal.Quotient.mk_surjective h0
    have h2 : q' ∈ associatedPrimes (A ⧸ I) (A ⧸ I) := associatedPrimes_subset_of_flat hq'
    rw [← hu]
    exact under_mem_associatedPrimes (A := A) h2
  have hheight : q.height = 1 := height_eq_one_of_mem_associatedPrimes hx hqA

  have hPq : P ∈ associatedPrimes R (R ⧸ q.map (algebraMap A R)) := by
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv] at hP
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R q).toLinearEquiv]
    exact mem_associatedPrimes_tensor_quotient_under (A := A) hP

  obtain ⟨z, hzP, hz⟩ : ∃ z ∉ P, ∀ p ∈ P, p * z ∈ q.map (algebraMap A R) := by
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hPq
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hmem : ∀ p, p ∈ P ↔ p * z ∈ q.map (algebraMap A R) := fun p ↦ by
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨z, fun hzP ↦ ?_, fun p hp ↦ (hmem p).1 hp⟩
    have := hred q hqp hxq
    have h2 : Ideal.Quotient.mk (q.map (algebraMap A R)) z ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact (hmem z).1 hzP
    have h3 : z ∈ q.map (algebraMap A R) :=
      Ideal.Quotient.eq_zero_iff_mem.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
    exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one P).2 ((hmem 1).2 (by simpa using h3)))

  obtain ⟨t, htq, ht⟩ : ∃ t ∈ q, ∀ b ∈ q, ∃ v ∉ q, ∃ c, v * b = t * c := by
    let B := Localization.AtPrime q
    have hdvr : IsDiscreteValuationRing B := isDiscreteValuationRing_of_height_eq_one q hheight B
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl ϖ
    have hmax : maximalIdeal B = Ideal.span {IsLocalization.mk' B a s} := hϖ.maximalIdeal_eq
    have h1 : IsLocalization.mk' B a s * algebraMap A B s = algebraMap A B a :=
      IsLocalization.mk'_spec B a s
    have haq : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff B q a, ← h1, hmax]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨a, haq, fun b hb ↦ ?_⟩
    have hbB := (IsLocalization.AtPrime.to_map_mem_maximal_iff B q b).2 hb
    rw [hmax, Ideal.mem_span_singleton] at hbB
    obtain ⟨d, hd⟩ := hbB
    obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl d
    have h2 : IsLocalization.mk' B c u * algebraMap A B u = algebraMap A B c :=
      IsLocalization.mk'_spec B c u
    refine ⟨s * u, q.primeCompl.mul_mem s.2 u.2, c, ?_⟩
    apply IsLocalization.injective B q.primeCompl_le_nonZeroDivisors
    simp only [map_mul]
    linear_combination (algebraMap A B s * algebraMap A B u) * hd +
      (IsLocalization.mk' B c u * algebraMap A B u) * h1 + algebraMap A B a * h2

  let S := Localization.AtPrime P
  have hflatRS : Module.Flat R S := IsLocalization.flat S P.primeCompl
  have hflatAS : Module.Flat A S := Module.Flat.trans A R S
  have hnoeth : IsNoetherianRing S := IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have ht0 : t ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, c, hvc⟩ := ht x hxq
    rw [zero_mul] at hvc
    rcases mul_eq_zero.1 hvc with h | h
    · exact hv (h ▸ q.zero_mem)
    · exact hx h
  have hreg : IsSMulRegular S (algebraMap A S t) := (IsSMulRegular.of_ne_zero ht0).of_flat
  have hunitS : ∀ r ∉ P, IsUnit (algebraMap R S r) := fun r hr ↦
    IsLocalization.map_units S (⟨r, hr⟩ : P.primeCompl)
  have hqS : ∀ b ∈ q, algebraMap A S b ∈ Ideal.span {algebraMap A S t} := fun b hb ↦ by
    obtain ⟨v, hv, c, hvc⟩ := ht b hb
    have hu : IsUnit (algebraMap A S v) := by
      rw [IsScalarTower.algebraMap_apply A R S]
      exact hunitS _ hv
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, hvc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hqRS : q.map (algebraMap A R) ≤ (Ideal.span {algebraMap A S t}).comap (algebraMap R S) :=
    Ideal.map_le_iff_le_comap.2 fun b hb ↦ by
      rw [Ideal.mem_comap, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hqS b hb
  have hmaxS : maximalIdeal S = Ideal.span {algebraMap A S t} := by
    refine le_antisymm ?_ ?_
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro p hp
      have h := hqRS (hz p hp)
      rw [Ideal.mem_comap, map_mul] at h
      exact (Ideal.mul_unit_mem_iff_mem _ (hunitS z hzP)).1 h
    · rw [Ideal.span_singleton_le_iff_mem, IsScalarTower.algebraMap_apply A R S,
        IsLocalization.AtPrime.to_map_mem_maximal_iff S P]
      exact htq
  exact exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span hmaxS hreg

end GlobalTheory
