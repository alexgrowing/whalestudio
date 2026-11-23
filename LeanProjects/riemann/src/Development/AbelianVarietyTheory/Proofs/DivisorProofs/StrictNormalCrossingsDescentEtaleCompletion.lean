import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom

open AlgebraicGeometry IsLocalRing ReciprocityTheory.AnForm.R GlobalTheory.Toroidal

namespace GlobalTheory.SncDescent

theorem eq_of_le_span_singleton {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t : R} (ht : t ∈ maximalIdeal R) {Q : Ideal R} [hQ : Q.IsPrime] (h0 : Q ≠ ⊥)
    (hle : Q ≤ Ideal.span {t}) : Q = Ideal.span {t} := by
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  by_contra htQ
  refine h0 (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) Q
    (IsNoetherian.noetherian _) (fun x hx => ?_) ?_)
  · obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 (hle hx)
    exact Submodule.smul_mem_smul ht ((hQ.mem_or_mem hx).resolve_left htQ)
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

theorem exists_rsp {A : Type} [CommRing A] [IsRegularLocalRing A] {m : ℕ} (p : Fin m → A)
    (hp : ∀ i, p i ∈ maximalIdeal A)
    (hind : ∀ a : Fin m → A, ∑ i, a i * p i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ ∏ i ∈ T, r i = ∏ i, p i := by
  classical
  let τ : Fin m → maximalIdeal A := fun i => ⟨p i, hp i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * p j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  let e := Fintype.equivFin (J ⊕ Fin m)
  refine ⟨_, Sum.elim t p ∘ e.symm, Finset.univ.map ⟨e ∘ Sum.inr, e.injective.comp Sum.inr_injective⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [e.symm.surjective.range_comp, Set.Sum.elim_range]
    exact hs
  · rw [hd, Fintype.card_sum]
  · rw [Finset.prod_map]
    simp

theorem exists_rsp_of_flat {A R : Type} [CommRing A] [IsRegularLocalRing A] [CommRing R] [IsRegularLocalRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) {m : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ∈ maximalIdeal R)
    (hind : ∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R)
    (D : Ideal A) (hD : D.map φ = Ideal.span {∏ i, t i})
    (hinj : ∀ i i', (Ideal.span {t i}).comap φ = (Ideal.span {t i'}).comap φ → i = i') :
    ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  classical
  algebraize [φ]
  have hloc : IsLocalHom (algebraMap A R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : algebraMap A R a ∈ maximalIdeal R := hm ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha
  have hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective A R
  have : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have := isRegularRing_of_isRegularLocalRing A
  have : UniqueFactorizationMonoid A := uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE A
  have hprime : ∀ i, Prime (t i) := fun i => prime_of_not_mem_sq (ht i) fun h => by
    have := hind (Pi.single i 1) (by simpa [Pi.single_apply] using h) i
    simp at this
  have h0 : ∏ i, t i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hprime i).ne_zero
  have hDt : ∀ d ∈ D, ∀ i, t i ∣ φ d := fun d hd i =>
    (Finset.dvd_prod_of_mem t (Finset.mem_univ i)).trans
      (Ideal.mem_span_singleton.1 (hD ▸ Ideal.mem_map_of_mem φ hd))
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => h0 ?_
    rw [h, Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hD
    exact hD
  have key : ∀ i, ∃ p : A, Prime p ∧ (Ideal.span {t i}).comap φ = Ideal.span {p} := fun i => by
    have hP : (Ideal.span {t i}).IsPrime := (Ideal.span_singleton_prime (hprime i).ne_zero).2 (hprime i)
    have hne : (Ideal.span {t i}).comap φ ≠ ⊥ := fun h => hd0 (by
      rw [← Ideal.mem_bot, ← h]
      exact Ideal.mem_span_singleton.2 (hDt d hd i))
    obtain ⟨p, hp, hpp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot inferInstance hne
    refine ⟨p, hpp, ?_⟩
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hpp.ne_zero).2 hpp
    have : (Ideal.span {t i}).LiesOver ((Ideal.span {t i}).comap φ) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Ideal.span {p})
      (q := (Ideal.span {t i}).comap φ) (Ideal.span {t i}) ((Ideal.span_singleton_le_iff_mem _).2 hp)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      have : p ∈ (⊥ : Ideal R).comap φ := hQo.over.le (Ideal.mem_span_singleton_self p)
      exact hpp.ne_zero (hφ (by simpa using this))
    rw [← eq_of_le_span_singleton (ht i) hQ0 hQ]
    exact hQo.over.symm
  choose p hp hP using key
  have htp : ∀ i, t i ∣ φ (p i) := fun i =>
    Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 ((hP i).ge (Ideal.mem_span_singleton_self _)))
  choose u hu using htp
  have hle : D ≤ Ideal.span {∏ i, p i} := fun x hx => by
    rw [Ideal.mem_span_singleton]
    refine Finset.prod_dvd_of_isRelPrime (fun i _ j _ hij => ?_) fun i _ => ?_
    · refine (hp i).irreducible.isRelPrime_iff_not_dvd.2 fun h => hij (hinj i j ?_)
      rw [hP, hP, Ideal.span_singleton_eq_span_singleton]
      exact (hp i).irreducible.associated_of_dvd (hp j).irreducible h
    · rw [← Ideal.mem_span_singleton, ← hP]
      exact Ideal.mem_span_singleton.2 (hDt x hx i)
  have hprod : φ (∏ i, p i) = (∏ i, t i) * ∏ i, u i := by
    simp only [map_prod, hu, Finset.prod_mul_distrib]
  have hU : IsUnit (∏ i, u i) := by
    have := Ideal.map_mono (f := φ) hle
    rw [hD, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton, hprod] at this
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left h0).1 (by simpa using this))
  have hu1 : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) hU
  obtain ⟨n, r, T, hr, hT⟩ := exists_rsp p (fun i => (mem_maximalIdeal _).2 (hp i).not_isUnit) fun a ha i => by
    have h1 := Ideal.mem_map_of_mem φ ha
    rw [Ideal.map_pow, hm, map_sum] at h1
    have h2 := hind (fun j => φ (a j) * u j) (by
      convert h1 using 2 with j
      rw [map_mul, hu]; ring) i
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun h => h2 ((h.map φ).mul (hu1 i))
  refine ⟨n, r, T, hr, ?_⟩
  have h3 : D.map (algebraMap A R) = (Ideal.span {∏ i, p i}).map (algebraMap A R) := by
    change D.map φ = (Ideal.span {∏ i, p i}).map φ
    rw [hD, Ideal.map_span, Set.image_singleton, hprod, Ideal.span_singleton_mul_right_unit hU]
  rw [hT, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R) D, h3, Ideal.comap_map_eq_self_of_faithfullyFlat]

theorem coeff_single_eq_zero {k σ : Type} [Field k] {g : MvPowerSeries σ k}
    (hg : g ∈ maximalIdeal (MvPowerSeries σ k) ^ 2) (s : σ) :
    MvPowerSeries.coeff (Finsupp.single s 1) g = 0 := by
  classical
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) fun a b ha hb => by rw [map_add, ha, hb, add_zero]
  rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot] at ha hb
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ, ha, hb]

theorem exists_rsp_of_isEtaleCompletion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type) [Field k] (m e : ℕ) (φ : A →+* ChartRing k m e) (D : Ideal A), IsEtaleCompletion φ → D.map φ = Ideal.span {∏ i : Fin m, bdParam k m e i} → (∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap φ = (Ideal.span {bdParam k m e i'}).comap φ → i = i') → ∃ (n : ℕ) (r : Fin n → A) (T : Finset (Fin n)), FinalTheorems.Rsp A n r ∧ D = Ideal.span {∏ i ∈ T, r i} := by
  intro A _ _ _ k _ m e φ D hφ hD hinj
  classical
  have hR : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k _
  have hA := (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion φ hφ).1
  refine exists_rsp_of_flat φ hφ.1 hφ.2.1 (bdParam k m e) (fun i => ?_) (fun a ha i => ?_) D hD hinj
  · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff]
    simp
  · have h := coeff_single_eq_zero ha (Sum.inl i)
    rw [map_sum, Finset.sum_eq_single i] at h
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, maximalIdeal_eq_bot, Ideal.mem_bot]
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial] at h
      simpa using h
    · intro j _ hj
      rw [bdParam, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, if_neg]
      simp [Finsupp.single_le_iff, Finsupp.single_apply, hj.symm]
    · simp

end GlobalTheory.SncDescent
