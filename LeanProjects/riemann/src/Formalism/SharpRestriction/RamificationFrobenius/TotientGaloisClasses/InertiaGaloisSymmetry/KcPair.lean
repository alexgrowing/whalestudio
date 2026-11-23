import Mathlib

namespace Formalism.HC.Der

section
open Ideal UniqueFactorizationMonoid

private theorem mulEquiv_ideal_bot_eq_bot {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) : f ⊥ = ⊥ := by
  obtain ⟨J, hJ⟩ := f.surjective ⊥
  calc f ⊥ = f (⊥ * J) := by rw [Ideal.bot_mul]
    _ = f ⊥ * f J := map_mul f _ _
    _ = ⊥ := by rw [hJ, Ideal.mul_bot]

private theorem prime_mulEquiv_ideal_apply {S : Type*} [CommRing S] [IsDedekindDomain S]
    (f : Ideal S ≃* Ideal S) {P : Ideal S} (hP : Prime P) : Prime (f P) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hP.ne_zero
    apply f.injective
    rw [Ideal.zero_eq_bot] at h ⊢
    rw [h, mulEquiv_ideal_bot_eq_bot f]
  · intro hu
    apply hP.not_unit
    rw [isUnit_iff_eq_one] at hu ⊢
    apply f.injective
    rw [hu, map_one]
  · intro a b h
    have h' : P ∣ f.symm a * f.symm b := by
      have := map_dvd f.symm h
      rwa [map_mul, MulEquiv.symm_apply_apply] at this
    rcases hP.dvd_or_dvd h' with h1 | h1
    · left
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this
    · right
      have := map_dvd f h1
      rwa [MulEquiv.apply_symm_apply] at this

private theorem prod_normalizedFactors_ideal_eq_self {S : Type*} [CommRing S] [IsDedekindDomain S]
    {I : Ideal S} (hI : I ≠ ⊥) : (normalizedFactors I).prod = I := by
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  exact associated_iff_eq.mp (prod_normalizedFactors hI0)

theorem kc_nf_map {S : Type*} [CommRing S] [IsDedekindDomain S] (I : Ideal S) (hI : I ≠ ⊥)
    (f : Ideal S ≃* Ideal S) : normalizedFactors (f I) = (normalizedFactors I).map f := by
  calc normalizedFactors (f I) = normalizedFactors ((normalizedFactors I).map f).prod := by
        rw [← map_multiset_prod f, prod_normalizedFactors_ideal_eq_self hI]
    _ = (normalizedFactors I).map f := by
        apply normalizedFactors_prod_of_prime
        intro Q hQ
        obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
        exact prime_mulEquiv_ideal_apply f (prime_of_normalized_factor R hR)

private theorem mem_of_prime_dvd_multiset_prod {S : Type*} [CommRing S] [IsDedekindDomain S]
    {s : Multiset (Ideal S)} (hs : ∀ Q ∈ s, Prime Q) {P : Ideal S} (hP : Prime P)
    (h : P ∣ s.prod) : P ∈ s := by
  obtain ⟨Q, hQ, hPQ⟩ := hP.exists_mem_multiset_dvd h
  rwa [(prime_dvd_prime_iff_eq hP (hs Q hQ)).mp hPQ]

theorem kc_pairing {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (p : Ideal S → Prop)
    (hp : ∀ P ∈ normalizedFactors D, (p (f P) ↔ ¬ p P)) :
    ∃ B : Ideal S, D = B * f B ∧ (∀ P : Ideal S, P.IsPrime → P ∣ B → p P) ∧ B ⊔ f B = ⊤ ∧
      (∀ g : Ideal S ≃* Ideal S, g D = D → (∀ P ∈ normalizedFactors D, (p (g P) ↔ p P)) → g B = B) ∧
      ∀ B' : Ideal S, D = B' * f B' → (∀ P : Ideal S, P.IsPrime → P ∣ B' → p P) → B' = B := by
  classical
  obtain ⟨F, hFdef⟩ : ∃ F, F = normalizedFactors D := ⟨_, rfl⟩
  have hFp : ∀ Q ∈ F, Prime Q := fun Q hQ => prime_of_normalized_factor Q (hFdef ▸ hQ)
  have hpF : ∀ P ∈ F, (p (f P) ↔ ¬ p P) := fun P hP => hp P (hFdef ▸ hP)
  have hinv : ∀ g : Ideal S ≃* Ideal S, g D = D → F.map g = F := by
    intro g hg
    have := kc_nf_map D hD0 g
    rw [hg] at this
    rw [hFdef]
    exact this.symm
  have hFprod : F.prod = D := by rw [hFdef]; exact prod_normalizedFactors_ideal_eq_self hD0
  have hmap : (F.filter p).map f = F.filter (fun P => ¬ p P) := by
    have e1 : F.filter (fun P => ¬ p P) = (F.map f).filter (fun P => ¬ p P) := by
      rw [hinv f hfD]
    have e2 : (F.map f).filter (fun P => ¬ p P) = (F.filter (fun P => ¬ p (f P))).map f := by
      rw [Multiset.filter_map]
      rfl
    have e3 : F.filter (fun P => ¬ p (f P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => by rw [hpF P hP]; exact not_not)
    rw [e1, e2, e3]
  have hsplit : D = (F.filter p).prod * f (F.filter p).prod := by
    rw [map_multiset_prod, hmap, Multiset.prod_filter_mul_prod_filter_not, hFprod]
  have hB0 : (F.filter p).prod ≠ ⊥ := by
    intro h
    apply hD0
    rw [hsplit, h, Ideal.bot_mul]
  have hprime_ne : ∀ {P J : Ideal S}, J ≠ ⊥ → P.IsPrime → P ∣ J → Prime P := by
    intro P J hJ hP hPJ
    refine Ideal.prime_of_isPrime ?_ hP
    rintro rfl
    exact hJ (zero_dvd_iff.mp hPJ)
  have hsupp : ∀ P : Ideal S, P.IsPrime → P ∣ (F.filter p).prod → p P := by
    intro P hP hdvd
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hP hdvd) hdvd
    exact (Multiset.mem_filter.mp hm).2
  refine ⟨(F.filter p).prod, hsplit, hsupp, ?_, ?_, ?_⟩
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hM1 : M ∣ (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_left.trans hle)
    have hM2 : M ∣ f (F.filter p).prod := Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)
    have hpM := hsupp M hM.isPrime hM1
    rw [map_multiset_prod, hmap] at hM2
    have hm := mem_of_prime_dvd_multiset_prod (fun Q hQ => hFp Q (Multiset.mem_of_mem_filter hQ))
      (hprime_ne hB0 hM.isPrime hM1) hM2
    exact (Multiset.mem_filter.mp hm).2 hpM
  · intro g hgD hgp
    have e1 : (F.map g).filter p = (F.filter (fun P => p (g P))).map g := by
      rw [Multiset.filter_map]
      rfl
    have e2 : F.filter (fun P => p (g P)) = F.filter p :=
      Multiset.filter_congr (fun P hP => hgp P (hFdef ▸ hP))
    rw [map_multiset_prod, ← e2, ← e1, hinv g hgD, e2]
  · intro B' hB' hsupp'
    have hB'0 : B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.bot_mul]
    have hfB'0 : f B' ≠ ⊥ := by
      intro h; apply hD0; rw [hB', h, Ideal.mul_bot]
    have hB'0' : B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hB'0
    have hfB'0' : f B' ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hfB'0
    have hF' : F = normalizedFactors B' + (normalizedFactors B').map f := by
      rw [hFdef, hB', normalizedFactors_mul hB'0' hfB'0', kc_nf_map B' hB'0 f]
    have hpB' : ∀ Q ∈ normalizedFactors B', p Q := by
      intro Q hQ
      exact hsupp' Q (Ideal.isPrime_of_prime (prime_of_normalized_factor Q hQ))
        (dvd_of_mem_normalizedFactors hQ)
    have hfilt : F.filter p = normalizedFactors B' := by
      rw [hF', Multiset.filter_add, Multiset.filter_eq_self.mpr hpB',
        Multiset.filter_eq_nil.mpr, add_zero]
      intro Q hQ
      obtain ⟨R, hR, rfl⟩ := Multiset.mem_map.mp hQ
      have hRF : R ∈ F := by rw [hF']; exact Multiset.mem_add.mpr (Or.inl hR)
      exact fun h => ((hpF R hRF).mp h) (hpB' R hR)
    rw [hfilt, prod_normalizedFactors_ideal_eq_self hB'0]

end

open NumberField Ideal

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem kc_not_dvd_different (M E : Type) [Field M] [NumberField M] [Field E] [NumberField E] [Algebra M E] [IsGalois M E]
    (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : P ≠ ⊥ → ∀ σ : E ≃ₐ[M] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : ¬ P ∣ differentIdeal (𝓞 M) (𝓞 E) := by
  by_cases hP : P = ⊥
  · subst hP
    intro hdvd
    apply differentIdeal_ne_bot (A := 𝓞 M) (B := 𝓞 E)
    rw [← Ideal.zero_eq_bot] at hdvd ⊢
    exact zero_dvd_iff.mp hdvd
  · have hp0 : P.under (𝓞 M) ≠ ⊥ := fun h0 => hP (Ideal.eq_bot_of_comap_eq_bot h0)
    haveI hmax : (P.under (𝓞 M)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
    haveI hfin : Finite (P.under (𝓞 M)).ResidueField := by
      haveI : Finite ((𝓞 M) ⧸ P.under (𝓞 M)) := Ideal.finiteQuotientOfFreeOfNeBot _ hp0
      exact Finite.of_surjective _
        (Ideal.bijective_algebraMap_quotient_residueField (P.under (𝓞 M))).2
    rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 M)) P (E ≃ₐ[M] E),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[M] E) (P.under (𝓞 M)) P,
      Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    exact h hP σ hσ

end Formalism.HC.Der
