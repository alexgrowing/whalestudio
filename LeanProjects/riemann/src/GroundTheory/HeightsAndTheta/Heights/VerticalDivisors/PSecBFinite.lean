import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecBFinite

section Homog

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_homogeneousComponent (f : R →+* S) (d : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map f (homogeneousComponent d p) = homogeneousComponent d (MvPolynomial.map f p) := by
  ext m
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem isHomogeneous_linForm {n : ℕ} (u : Fin n → R) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousComponent_mul_of_deg_one (c t : MvPolynomial σ R) (ht : t.IsHomogeneous 1) (d : ℕ) :
    homogeneousComponent (d + 1) (c * t) = homogeneousComponent d c * t := by
  have key : ∀ (x : MvPolynomial σ R) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ R) x i : MvPolynomial σ R) =
        homogeneousComponent i x :=
    fun x i => decomposition.decompose'_apply x i
  have h := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule σ R) (a := c)
    (n := d + 1) ((mem_homogeneousSubmodule 1 t).mpr ht) (by omega)
  rw [key, key, Nat.add_sub_cancel] at h
  exact h

theorem isHomogeneous_span_of {s : Set (MvPolynomial σ R)} (h : ∀ x ∈ s, ∃ d, x.IsHomogeneous d) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ R) :=
  Ideal.homogeneous_span _ _ fun x hx =>
    let ⟨d, hd⟩ := h x hx
    ⟨d, (mem_homogeneousSubmodule d x).mpr hd⟩

theorem isHomogeneous_map_of (f : R →+* S) (P : Ideal (MvPolynomial σ R))
    (hP : ∀ p ∈ P, ∀ d, homogeneousComponent d p ∈ P) :
    (P.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ S) := by
  have hspan : P.map (MvPolynomial.map f) =
      Ideal.span {x | ∃ p ∈ P, ∃ d, x = MvPolynomial.map f (homogeneousComponent d p)} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, ← sum_homogeneousComponent p, map_sum]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨p, hp, d, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨p, hp, d, rfl⟩
      exact Ideal.mem_map_of_mem _ (hP p hp d)
  rw [hspan]
  refine isHomogeneous_span_of ?_
  rintro _ ⟨p, -, d, rfl⟩
  exact ⟨d, by rw [map_homogeneousComponent]; exact homogeneousComponent_isHomogeneous _ _⟩

end Homog

theorem finite_of_pow_mem {R : Type*} [CommRing R] {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) R))
    (M : Fin n → ℕ) (q : Fin n → MvPolynomial (Fin n) R) (hq : ∀ j, (q j).totalDegree < M j)
    (hQ : ∀ j, X j ^ M j - q j ∈ Q) : Module.Finite R (MvPolynomial (Fin n) R ⧸ Q) := by
  classical
  let S : Set (MvPolynomial (Fin n) R ⧸ Q) :=
    Set.range fun α : (j : Fin n) → Fin (M j) =>
      Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => (α j : ℕ)) 1)
  have hC : ∀ (r : R) (p : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk Q (C r * p) = r • Ideal.Quotient.mk Q p := by
    intro r p
    rw [← MvPolynomial.smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have key : ∀ d (s : Fin n →₀ ℕ), s.degree ≤ d →
      Ideal.Quotient.mk Q (monomial s 1) ∈ Submodule.span R S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro s hs
    by_cases hsmall : ∀ j, s j < M j
    · refine Submodule.subset_span ⟨fun j => ⟨s j, hsmall j⟩, ?_⟩
      show Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => s j) 1) = _
      rw [Finsupp.equivFunOnFinite_symm_coe]
    · push Not at hsmall
      obtain ⟨j, hj⟩ := hsmall
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single j (M j) :=
        ⟨s - Finsupp.single j (M j), (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)).symm⟩
      have hmk : Ideal.Quotient.mk Q (monomial (s' + Finsupp.single j (M j)) 1) =
          Ideal.Quotient.mk Q (monomial s' 1 * q j) := by
        have hmono : monomial (s' + Finsupp.single j (M j)) (1 : R) = monomial s' 1 * X j ^ M j := by
          rw [X_pow_eq_monomial, monomial_mul, one_mul]
        rw [hmono, Ideal.Quotient.eq, ← mul_sub]
        exact Q.mul_mem_left _ (hQ j)
      rw [hmk, (q j).as_sum, Finset.mul_sum, map_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hprod : monomial s' (1 : R) * monomial m (coeff m (q j)) =
          C (coeff m (q j)) * monomial (s' + m) 1 := by
        rw [monomial_mul, C_mul_monomial, one_mul, mul_one]
      rw [hprod, hC]
      refine Submodule.smul_mem _ _ (ih _ ?_ _ le_rfl)
      have hm' : m.degree ≤ (q j).totalDegree := le_totalDegree hm
      have hqj := hq j
      rw [map_add, Finsupp.degree_single] at hs
      rw [map_add]
      omega
  refine ⟨(Submodule.fg_def).mpr ⟨S, Set.finite_range _, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [← mul_one (coeff s p), ← C_mul_monomial, hC]
  exact Submodule.smul_mem _ _ (key _ s le_rfl)

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl) fun f hf => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) f.coeffs
  have hb0 : (algebraMap (𝓞 K) K b) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  have hrange : C (algebraMap (𝓞 K) K b) * f ∈ Set.range (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    by_cases h0 : coeff m f = 0
    · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
    · obtain ⟨y, hy⟩ := hb _ (coeff_mem_coeffs m h0)
      exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  obtain ⟨g, hg⟩ := hrange
  have hgI : g ∈ integralModel I := by
    show MvPolynomial.map (algebraMap (𝓞 K) K) g ∈ I
    rw [hg]
    exact I.mul_mem_left _ hf
  have : f = C (algebraMap (𝓞 K) K b)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) g := by
    rw [hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgI)

omit [NumberField K] in

theorem homogeneousComponent_mem_integralModel {n : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomogIdeal I) : ∀ p ∈ integralModel I, ∀ d, homogeneousComponent d p ∈ integralModel I := by
  intro p hp d
  show MvPolynomial.map (algebraMap (𝓞 K) K) (homogeneousComponent d p) ∈ I
  rw [map_homogeneousComponent]
  exact hI _ hp d

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem exists_C_mul_mem {σ : Type*} (J : Ideal (MvPolynomial σ (𝓞 K))) (h : MvPolynomial σ (𝓞 K))
    (hh : MvPolynomial.map (algebraMap (𝓞 K) K) h ∈ J.map (MvPolynomial.map (algebraMap (𝓞 K) K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ C d * h ∈ J := by
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors (𝓞 K)).map (C (σ := σ))) (MvPolynomial σ K)).mp hh
  obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.mp hs
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hda : C d * h = a := by
    apply MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
    rw [map_mul, mul_comm]
    exact hx
  rw [hda]
  exact ha

theorem incIdeal_le_map {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    incIdeal I k ≤ (incIdeal (integralModel I) k).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  apply sup_le
  · have hI : I.map (rename (R := K) (Sum.inl : Fin n → Fin n ⊕ (Fin k × Fin n))) =
        ((integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K))).map (rename Sum.inl) := by
      rw [map_integralModel]
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, ← map_rename]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hform : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) =
        MvPolynomial.map (algebraMap (𝓞 K) K) (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) := by
      simp [map_sum]
    show (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) ∈ _
    rw [hform]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

def parIdx (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

theorem parIdx_injective (e n : ℕ) : Function.Injective (parIdx e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parIdx]

def specHom (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) (𝓞 K) →+* MvPolynomial (Fin n) (ParDVR e n v) :=
  eval₂Hom (C.comp (algebraMap (𝓞 K) (ParDVR e n v)))
    (Sum.elim X fun ij => C (parY e n v (parIdx e n ij)))

omit [NumberField K] in
theorem specHom_X_inl (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (j : Fin n) :
    specHom e n v (X (Sum.inl j)) = X j := by
  simp [specHom]

omit [NumberField K] in
theorem specHom_rename_inl (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (p : MvPolynomial (Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inl p) = MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) p := by
  rw [specHom, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inl]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [eval₂_add, hp, hq, map_add]
  | mul_X p i hp => rw [eval₂_mul, hp, eval₂_X, map_mul, map_X]

omit [NumberField K] in
theorem specHom_form (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (i : Fin (e + 1)) :
    specHom e n v (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) =
      linForm fun j => parY e n v (parIdx e n (i, j)) := by
  simp [specHom, linForm, map_sum]

omit [NumberField K] in
theorem specHom_rename_inr (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inr g) =
      C (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, rename_C, specHom, eval₂Hom_C, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
      MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq, C_add]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, C_mul, rename_X, rename_X]
    congr 1
    simp [specHom, parY]

omit [NumberField K] in

theorem incIdeal_le_comap_specHom (e : ℕ) {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    incIdeal (integralModel I) (e + 1) ≤
      (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
        Ideal.span {chartForm (parY e n v)}).comap (specHom e n v) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, specHom_rename_inl]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, specHom_form]
    induction i using Fin.cases with
    | zero =>
      exact Ideal.mem_sup_right (Ideal.subset_span (by simp [chartForm, parIdx]))
    | succ i =>
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, by simp [secForm, parIdx]⟩))

end NumberField

end SecBFinite

attribute [local instance] MvPolynomial.gradedAlgebra in
open SecBFinite in

theorem SecBFinite.proof (hIN : IncidenceNull.Statement) (hCT : ChartTorsion.Statement)
    (hPS : PrimitiveScale.Statement) : SecBFinite.Statement := by
  intro K _ _ n e I f v hI hf
  obtain ⟨c, g, -, hg, m0, hm0⟩ := hPS K v _ f hf.1
  obtain ⟨m, hm⟩ := hIN K n (e + 1) I f hf
  have := hI.isPrime
  have hPprime : (integralModel I).IsPrime := by
    show (I.comap _).IsPrime
    infer_instance
  have hPC : ∀ a : 𝓞 K, C a ∈ integralModel I → a = 0 := by
    intro a ha
    by_contra h0
    have haI : (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) ∈ I := by
      simpa [integralModel] using ha
    have hu : IsUnit (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) :=
      (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr h0)).map C
    exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ haI hu)

  set γ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g) with hγdef
  have hγ : IsUnit γ := by
    rw [hγdef, IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v),
      Ideal.mem_primeCompl_iff]
    intro hmem
    rw [parPrime, MvPolynomial.mem_map_C_iff] at hmem
    have h0 := hmem (m0.mapDomain (parIdx e n))
    rw [coeff_rename_mapDomain _ (parIdx_injective e n)] at h0
    exact hm0 h0
  obtain ⟨w, hw⟩ := hγ

  have hpow : ∀ j, ∃ M, X j ^ (M + 1) ∈ modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
      Ideal.span {chartForm (parY e n v)} := by
    intro j
    have hmapped : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) ∈
        (incIdeal (integralModel I) (e + 1)).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      apply incIdeal_le_map I
      have hmap : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) =
          C c ^ m * (rename Sum.inr f * X (Sum.inl j)) ^ m := by
        rw [map_pow, map_mul, map_rename, hg, map_X, map_mul, rename_C]
        ring
      rw [hmap]
      exact Ideal.mul_mem_left _ _ (hm j)
    obtain ⟨d, hd, hdh⟩ := exists_C_mul_mem _ _ hmapped
    obtain ⟨N, hN⟩ := hCT (𝓞 K) n (e + 1) (integralModel I) hPprime hPC d _ hd hdh j
    have hsp := incIdeal_le_comap_specHom e I v hN
    rw [Ideal.mem_comap, map_mul, map_pow, map_pow, map_mul, specHom_X_inl, specHom_rename_inr,
      ← hγdef, ← hw] at hsp
    refine ⟨N + m, ?_⟩
    set u : ParDVR e n v := ((w : (ParDVR e n v)ˣ) : ParDVR e n v) with hu
    set u' : ParDVR e n v := ((w⁻¹ : (ParDVR e n v)ˣ) : ParDVR e n v) with hu'
    have h1 : (C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u = 1 := by
      rw [← C_mul, hu, hu', Units.inv_mul, C_1]
    have hX : X j ^ (N + m + 1) = (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) := by
      rw [show (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) =
          X j ^ (N + m + 1) * ((C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u) ^ m
          by ring, h1, one_pow, mul_one]
    rw [hX]
    exact Ideal.mul_mem_left _ _ hsp

  have hJ0 : (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v)))).IsHomogeneous
      (homogeneousSubmodule (Fin n) (ParDVR e n v)) := by
    refine (isHomogeneous_map_of _ _ (homogeneousComponent_mem_integralModel hI.isHomog)).sup
      (isHomogeneous_span_of ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨1, isHomogeneous_linForm _⟩
  have hq : ∀ j, ∃ M : ℕ, ∃ q : MvPolynomial (Fin n) (ParDVR e n v), q.totalDegree < M ∧
      X j ^ M - q ∈ secIdeal (modelR e I v) (parY e n v) := by
    intro j
    obtain ⟨M, hM⟩ := hpow j
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hM
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨M + 1, homogeneousComponent M c', ?_, ?_⟩
    · exact lt_of_le_of_lt (homogeneousComponent_isHomogeneous M c').totalDegree_le (Nat.lt_succ_self M)
    · have hXM : homogeneousComponent (M + 1) (X j ^ (M + 1) : MvPolynomial (Fin n) (ParDVR e n v)) =
          X j ^ (M + 1) := homogeneousComponent_eq_self (isHomogeneous_X_pow _ _)
      have h2 := congrArg (homogeneousComponent (M + 1)) hab
      rw [map_add, homogeneousComponent_mul_of_deg_one _ (chartForm (parY e n v)) (isHomogeneous_linForm _), hXM] at h2
      have ha' : homogeneousComponent (M + 1) a ∈
          modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) :=
        homogeneousComponent_mem_of_mem hJ0 ha _
      rw [← h2, show homogeneousComponent (M + 1) a + homogeneousComponent M c' * chartForm (parY e n v) -
          homogeneousComponent M c' = homogeneousComponent (M + 1) a +
            homogeneousComponent M c' * (chartForm (parY e n v) - 1) by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left ha')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  choose M q hqdeg hqmem using hq
  exact finite_of_pow_mem _ M q hqdeg hqmem

end

end GroundTheory.Heights₂.Heights.Vertical
