import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ThDist
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XUniqConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section Tower

variable {M N : ℕ} [NeZero M] [NeZero N] {K K' : Type} [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
  [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] [Algebra K K']

end Tower

section One

variable {M : ℕ} [NeZero M] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]

end One

private theorem algebraMap_sgO_eq_sg_algebraMap (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (t : (ZMod M)ˣ) (x : 𝓞 K) :
    algebraMap (𝓞 K) K (sgO M K t x) = sg M K t (algebraMap (𝓞 K) K x) := by
  unfold sgO
  rfl

private theorem sgO_mul_apply (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a b : (ZMod M)ˣ) (x : 𝓞 K) :
    sgO M K (a * b) x = sgO M K a (sgO M K b x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [algebraMap_sgO_eq_sg_algebraMap, algebraMap_sgO_eq_sg_algebraMap, algebraMap_sgO_eq_sg_algebraMap, map_mul, AlgEquiv.mul_apply]

private theorem sgO_symm_apply_eq_sgO_inv (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a : (ZMod M)ˣ) (x : 𝓞 K) :
    (sgO M K a).symm x = sgO M K a⁻¹ x := by
  rw [RingEquiv.symm_apply_eq, ← sgO_mul_apply, mul_inv_cancel]
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [algebraMap_sgO_eq_sg_algebraMap, map_one, AlgEquiv.one_apply]

private theorem map_sgO_conjI_eq_conjI_mul_inv (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (𝔞 : Ideal (𝓞 K)) (s t : (ZMod M)ˣ) :
    Ideal.map ((sgO M K s : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K) (conjI M K 𝔞 t) = conjI M K 𝔞 (t * s⁻¹) := by
  unfold conjI
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, sgO_symm_apply_eq_sgO_inv, sgO_mul_apply]

private theorem spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)) (X : K)
    (hX : FractionalIdeal.spanSingleton (𝓞 K)⁰ X = ∏ t, ((conjI M K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑t)
    (s : (ZMod M)ˣ) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (sg M K s X) = ∏ t, ((conjI M K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑(t * s) := by
  let f : 𝓞 K →+* 𝓞 K := ((sgO M K s : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K)
  have hf : (𝓞 K)⁰ ≤ Submonoid.comap f (𝓞 K)⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (sgO M K s).injective
  have key : IsLocalization.map K f hf = ((sg M K s : K ≃ₐ[ℚ] K) : K →+* K) := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext x
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    exact algebraMap_sgO_eq_sg_algebraMap M K s x
  have h := congrArg (FractionalIdeal.extendedHom' K hf) hX
  rw [FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_spanSingleton, key, map_prod] at h
  rw [show (sg M K s) X = ((sg M K s : K ≃ₐ[ℚ] K) : K →+* K) X from rfl, h]
  refine Fintype.prod_equiv (Equiv.mulRight s⁻¹) _ _ (fun t => ?_)
  rw [map_zpow₀, FractionalIdeal.extendedHom'_apply, FractionalIdeal.extended_coeIdeal_eq_map,
    Equiv.coe_mulRight, inv_mul_cancel_right]
  beta_reduce
  dsimp only [f]
  rw [map_sgO_conjI_eq_conjI_mul_inv]

private theorem sg_algebraMap_eq_algebraMap_sg_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (x : K) :
    sg (q * M) K' t (algebraMap K K' x) = algebraMap K K' (sg M K (ZMod.unitsMap (dvd_mul_left M q) t) x) := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have h := IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply (q * M) K' K (dvd_mul_left M q) (sg (q * M) K' t)
  have e2 : (sg (q * M) K' t).restrictNormal K = sg M K (ZMod.unitsMap (dvd_mul_left M q) t) := by
    unfold sg at h ⊢
    rw [MulEquiv.apply_symm_apply] at h
    rw [← h, MulEquiv.symm_apply_apply]
  rw [← AlgEquiv.restrictNormal_commutes, e2]

private theorem cyclotomic_rat_algEquiv_apply_comm (N : ℕ) [NeZero N] (K' : Type) [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] (a b : K' ≃ₐ[ℚ] K') (y : K') :
    a (b y) = b (a y) := by
  have hab : a * b = b * a :=
    (IsCyclotomicExtension.Rat.galEquivZMod N K').injective (by rw [map_mul, map_mul, mul_comm])
  rw [← AlgEquiv.mul_apply, hab, AlgEquiv.mul_apply]

private theorem norm_sg_eq_sg_unitsMap_norm (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (y : K') :
    Algebra.norm K (sg (q * M) K' t y) = sg M K (ZMod.unitsMap (dvd_mul_left M q) t) (Algebra.norm K y) := by
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  apply (algebraMap K K').injective
  rw [← sg_algebraMap_eq_algebraMap_sg_unitsMap, Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
  refine Finset.prod_congr rfl fun σ _ => ?_
  exact cyclotomic_rat_algEquiv_apply_comm (q * M) K' (σ.restrictScalars ℚ) (sg (q * M) K' t) y

private theorem algebraMap_norm_eq_prod_sg_ker_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (y : K') :
    algebraMap K K' (Algebra.norm K y) =
      ∏ k ∈ Finset.univ.filter (fun k : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) k = 1), sg (q * M) K' k y := by
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  haveI : IsGalois ℚ K' := IsCyclotomicExtension.isGalois {q * M} ℚ K'
  haveI : IsGalois K K' := IsGalois.tower_top_of_isGalois ℚ K K'
  rw [Algebra.norm_eq_prod_automorphisms]
  refine Finset.prod_bij (fun σ _ => IsCyclotomicExtension.Rat.galEquivZMod (q * M) K' (σ.restrictScalars ℚ))
    ?_ ?_ ?_ ?_
  · intro σ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply (q * M) K' K (dvd_mul_left M q)]
    have h1 : (σ.restrictScalars ℚ).restrictNormal K = 1 := by
      ext x
      apply (algebraMap K K').injective
      rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
      exact σ.commutes x
    rw [h1, map_one]
  · intro σ₁ _ σ₂ _ h
    exact AlgEquiv.restrictScalars_injective ℚ ((IsCyclotomicExtension.Rat.galEquivZMod (q * M) K').injective h)
  · intro k hk
    rw [Finset.mem_filter] at hk
    let σ : K' ≃ₐ[K] K' := AlgEquiv.ofRingEquiv (f := (sg (q * M) K' k).toRingEquiv) (fun x => by
      change sg (q * M) K' k (algebraMap K K' x) = algebraMap K K' x
      rw [sg_algebraMap_eq_algebraMap_sg_unitsMap, hk.2, map_one, AlgEquiv.one_apply])
    refine ⟨σ, Finset.mem_univ _, ?_⟩
    have hσ : σ.restrictScalars ℚ = sg (q * M) K' k := by
      ext x
      rfl
    rw [hσ]
    unfold sg
    exact MulEquiv.apply_symm_apply _ _
  · intro σ _
    change σ y = sg (q * M) K' (IsCyclotomicExtension.Rat.galEquivZMod (q * M) K' (σ.restrictScalars ℚ)) y
    unfold sg
    rw [MulEquiv.symm_apply_apply]
    rfl

private theorem sgO_algebraMap_eq_algebraMap_sgO_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (t : (ZMod (q * M))ˣ) (x : 𝓞 K) :
    sgO (q * M) K' t (algebraMap (𝓞 K) (𝓞 K') x) = algebraMap (𝓞 K) (𝓞 K') (sgO M K (ZMod.unitsMap (dvd_mul_left M q) t) x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
  rw [algebraMap_sgO_eq_sg_algebraMap, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K',
    IsScalarTower.algebraMap_apply (𝓞 K) K K', IsScalarTower.algebraMap_apply (𝓞 K) K K', sg_algebraMap_eq_algebraMap_sg_unitsMap, algebraMap_sgO_eq_sg_algebraMap]

private theorem map_comap_ringEquiv_eq_comap_map_of_semiconj {A B : Type} [CommRing A] [CommRing B] (ι : A →+* B) (e : A ≃+* A) (e' : B ≃+* B)
    (h : ∀ x, ι (e x) = e' (ι x)) (J : Ideal A) :
    Ideal.map ι (Ideal.comap e J) = Ideal.comap e' (Ideal.map ι J) := by
  have h1 : Ideal.comap e J = Ideal.map (e.symm : A →+* A) J := (Ideal.map_comap_of_equiv e.symm).symm
  have h2 : Ideal.comap e' (Ideal.map ι J) = Ideal.map (e'.symm : B →+* B) (Ideal.map ι J) :=
    (Ideal.map_comap_of_equiv e'.symm).symm
  rw [h1, h2, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  change ι (e.symm x) = e'.symm (ι x)
  rw [RingEquiv.eq_symm_apply, ← h, RingEquiv.apply_symm_apply]

private theorem ideal_comap_ringEquiv_prod {B : Type} [CommRing B] (e : B ≃+* B) {ι : Type} (s : Finset ι) (I : ι → Ideal B) :
    Ideal.comap e (∏ i ∈ s, I i) = ∏ i ∈ s, Ideal.comap e (I i) := by
  have h1 : ∀ J : Ideal B, Ideal.comap e J = Ideal.mapHom (e.symm : B →+* B) J := fun J =>
    (Ideal.map_comap_of_equiv e.symm).symm
  simp only [h1]
  exact map_prod (Ideal.mapHom (e.symm : B →+* B)) I s

private theorem ideal_comap_ringEquiv_span_singleton {B : Type} [CommRing B] (e : B ≃+* B) (x : B) :
    Ideal.comap e (Ideal.span {x}) = Ideal.span {e.symm x} := by
  have h1 : Ideal.comap e (Ideal.span {x}) = Ideal.map (e.symm : B →+* B) (Ideal.span {x}) :=
    (Ideal.map_comap_of_equiv e.symm).symm
  rw [h1, Ideal.map_span, Set.image_singleton]
  rfl

private theorem ideal_comap_ringEquiv_pow {B : Type} [CommRing B] (e : B ≃+* B) (J : Ideal B) (n : ℕ) :
    Ideal.comap e (J ^ n) = (Ideal.comap e J) ^ n := by
  have h1 : ∀ I : Ideal B, Ideal.comap e I = Ideal.map (e.symm : B →+* B) I := fun I =>
    (Ideal.map_comap_of_equiv e.symm).symm
  rw [h1, h1, Ideal.map_pow]

private theorem map_relNorm_eq_prod_conjI_ker_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 K')) (Ideal.relNorm (𝓞 K) 𝔞) =
      ∏ k ∈ Finset.univ.filter (fun k : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) k = 1), conjI (q * M) K' 𝔞 k := by
  have hmem : 𝔞 ∈ (Ideal (𝓞 K'))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔞
  have hn0 : orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 K', 𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) = Ideal.span {x} := by
    have h1 : ClassGroup.mk0 ⟨𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩), pow_mem hmem _⟩ = 1 := by
      rw [show (⟨𝔞 ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩), pow_mem hmem _⟩ : (Ideal (𝓞 K'))⁰) =
        ⟨𝔞, hmem⟩ ^ orderOf (ClassGroup.mk0 ⟨𝔞, hmem⟩) from Subtype.ext (by simp), map_pow, pow_orderOf_eq_one]
    obtain ⟨x, hx⟩ := ((ClassGroup.mk0_eq_one_iff _).mp h1).principal
    exact ⟨x, hx⟩
  apply pow_left_injective hn0
  dsimp only
  rw [← Ideal.map_pow, ← map_pow, hx, Ideal.relNorm_singleton, Ideal.map_span, Set.image_singleton,
    ← Finset.prod_pow]
  unfold conjI
  simp_rw [← ideal_comap_ringEquiv_pow, hx, ideal_comap_ringEquiv_span_singleton, sgO_symm_apply_eq_sgO_inv]
  rw [Ideal.prod_span_singleton]
  congr 2
  apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', IsScalarTower.algebraMap_apply (𝓞 K) K K',
    Algebra.algebraMap_intNorm (L := K'), algebraMap_norm_eq_prod_sg_ker_unitsMap M q K K', map_prod]
  simp_rw [algebraMap_sgO_eq_sg_algebraMap]
  refine Finset.prod_nbij' (·⁻¹) (·⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_inv, hk, inv_one]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_inv, hk, inv_one]
  · intro k _
    simp
  · intro k _
    simp
  · intro k _
    simp

private theorem map_conjI_relNorm_eq_prod_conjI_fiber_unitsMap (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) (t : (ZMod M)ˣ) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 K')) (conjI M K (Ideal.relNorm (𝓞 K) 𝔞) t) =
      ∏ t' ∈ Finset.univ.filter (fun t' : (ZMod (q * M))ˣ => ZMod.unitsMap (dvd_mul_left M q) t' = t), conjI (q * M) K' 𝔞 t' := by
  obtain ⟨t₀, rfl⟩ := ZMod.unitsMap_surjective (dvd_mul_left M q) t
  rw [show conjI M K (Ideal.relNorm (𝓞 K) 𝔞) (ZMod.unitsMap (dvd_mul_left M q) t₀) =
      Ideal.comap (sgO M K (ZMod.unitsMap (dvd_mul_left M q) t₀)) (Ideal.relNorm (𝓞 K) 𝔞) from rfl,
    map_comap_ringEquiv_eq_comap_map_of_semiconj (algebraMap (𝓞 K) (𝓞 K')) (sgO M K _) (sgO (q * M) K' t₀)
      (fun x => (sgO_algebraMap_eq_algebraMap_sgO_unitsMap M q K K' t₀ x).symm),
    map_relNorm_eq_prod_conjI_ker_unitsMap M q K K' 𝔞 h𝔞, ideal_comap_ringEquiv_prod]
  refine Finset.prod_nbij' (· * t₀) (· * t₀⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_mul, hk, one_mul]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
    rw [map_mul, hk, map_inv, mul_inv_cancel]
  · intro k _
    simp
  · intro k _
    simp
  · intro k _
    unfold conjI
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, sgO_mul_apply]

private theorem prod_zpow_eq_zpow_sum_of_ne_zero {G : Type} [CommGroupWithZero G] (a : G) (ha : a ≠ 0) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  refine Finset.cons_induction ?_ (fun j s hj ih => ?_) s
  · simp
  · rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ ha]

private theorem fractionalIdeal_spanSingleton_finset_prod {R P : Type} [CommRing R] [CommRing P] [Algebra R P] {S : Submonoid R} [IsLocalization S P] {ι : Type} (s : Finset ι) (f : ι → P) :
    FractionalIdeal.spanSingleton S (∏ i ∈ s, f i) = ∏ i ∈ s, FractionalIdeal.spanSingleton S (f i) := by
  refine Finset.cons_induction ?_ (fun j s hj ih => ?_) s
  · simp [FractionalIdeal.spanSingleton_one]
  · rw [Finset.prod_cons, Finset.prod_cons, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ih]

private theorem isFractionRing_map_ringOfIntegers_eq_algebraMap (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] (x : K) :
    IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K')) x = algebraMap K K' x := by
  have h : (IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 K')) : K →+* K') = algebraMap K K' := by
    apply IsLocalization.ringHom_ext (𝓞 K)⁰
    ext y
    rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.map, IsLocalization.map_eq,
      ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') K', ← IsScalarTower.algebraMap_apply (𝓞 K) K K']
  exact RingHom.congr_fun h x

private theorem fractionalIdeal_coeIdeal_finset_prod {R P : Type} [CommRing R] [CommRing P] [Algebra R P] (S : Submonoid R) {ι : Type} (s : Finset ι) (I : ι → Ideal R) :
    ((∏ i ∈ s, I i : Ideal R) : FractionalIdeal S P) = ∏ i ∈ s, (I i : FractionalIdeal S P) :=
  map_prod (FractionalIdeal.coeIdealHom S P) I s

private theorem prod_fiber_prod_zpow_eq_prod_zpow_comp {G α β : Type} [DivisionCommMonoid G] [Fintype α] [Fintype β] [DecidableEq β] (g : α → β) (F : α → G) (e : β → ℤ) :
    ∏ t, (∏ t' ∈ Finset.univ.filter (fun t' => g t' = t), F t') ^ e t = ∏ t', F t' ^ e (g t') := by
  rw [← Finset.prod_fiberwise Finset.univ g (fun t' => F t' ^ e (g t'))]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl (fun t' ht' => ?_)
  rw [(Finset.mem_filter.mp ht').2]

private theorem coeIdeal_conjI_ne_zero_of_ne_bot (N : ℕ) [NeZero N] (K' : Type) [Field K'] [NumberField K'] [IsCyclotomicExtension {N} ℚ K'] (𝔞 : Ideal (𝓞 K')) (h𝔞 : 𝔞 ≠ ⊥) (t : (ZMod N)ˣ) :
    ((conjI N K' 𝔞 t : Ideal (𝓞 K')) : FractionalIdeal (𝓞 K')⁰ K') ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  unfold conjI
  have h1 : Ideal.comap (sgO N K' t) 𝔞 = Ideal.map ((sgO N K' t).symm : 𝓞 K' →+* 𝓞 K') 𝔞 :=
    (Ideal.map_comap_of_equiv (sgO N K' t).symm).symm
  rw [h1, Ne, Ideal.map_eq_bot_iff_of_injective (f := ((sgO N K' t).symm : 𝓞 K' →+* 𝓞 K')) (sgO N K' t).symm.injective]
  exact h𝔞

theorem UpperTheory.V.ML.xNormDiv :
    ∀ (M q : ℕ) [NeZero M] [NeZero (q * M)] (K K' : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] [Field K'] [NumberField K'] [IsCyclotomicExtension {q * M} ℚ K'] [Algebra K K'], q.Prime → ∀ u : (ZMod M)ˣ, (u : ZMod M) = q → ∀ (b : ℕ), b < q → ∀ (𝔞 : Ideal (𝓞 K')) (X' : K') (X : K), 𝔞 ≠ ⊥ → IsX (q * M) K' b 𝔞 X' → IsX M K b (Ideal.relNorm (𝓞 K) 𝔞) X →
    ∃ ζ : K, ζ ^ (2 * M) = 1 ∧ Algebra.norm K X' = ζ * (X / (sg M K u)⁻¹ X) := by
  intro M q _ _ K K' _ _ _ _ _ _ _ hq u hu b hb 𝔞 X' X h𝔞 hX' hX
  unfold IsX at hX' hX
  have hneg : ZMod.unitsMap (dvd_mul_left M q) (-1) = -1 := by
    ext
    simp [ZMod.unitsMap]
  have hN1 : Algebra.norm K X' * sg M K (-1) (Algebra.norm K X') = 1 := by
    rw [← hneg, ← norm_sg_eq_sg_unitsMap_norm M q K K', ← map_mul, hX'.1, map_one]
  have hY1 : X / (sg M K u)⁻¹ X * sg M K (-1) (X / (sg M K u)⁻¹ X) = 1 := by
    have hc : (sg M K u)⁻¹ (sg M K (-1) X) = sg M K (-1) ((sg M K u)⁻¹ X) :=
      cyclotomic_rat_algEquiv_apply_comm M K (sg M K u)⁻¹ (sg M K (-1)) X
    rw [map_div₀, ← hc, div_mul_div_comm, ← map_mul, hX.1, map_one, div_one]
  have hτX : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((sg M K u)⁻¹ X) =
      ∏ t, ((conjI M K (Ideal.relNorm (𝓞 K) 𝔞) t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b ↑(t * u⁻¹) := by
    rw [← map_inv]
    exact spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod M K b _ X hX.2 u⁻¹
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (Algebra.norm K X') =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (X / (sg M K u)⁻¹ X) := by
    apply FractionalIdeal.extendedHom_injective (𝓞 K) K K' (𝓞 K')
    dsimp only
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, hX.2, hτX, map_div₀, map_prod, map_prod,
      FractionalIdeal.extendedHom_spanSingleton, isFractionRing_map_ringOfIntegers_eq_algebraMap, algebraMap_norm_eq_prod_sg_ker_unitsMap M q K K', fractionalIdeal_spanSingleton_finset_prod]
    simp_rw [map_zpow₀, FractionalIdeal.extendedHom_coeIdeal_eq_map, map_conjI_relNorm_eq_prod_conjI_fiber_unitsMap M q K K' 𝔞 h𝔞,
      fractionalIdeal_coeIdeal_finset_prod, spanSingleton_sg_eq_prod_conjI_pow_th_mul_of_eq_prod (q * M) K' b 𝔞 X' hX'.2]
    rw [prod_fiber_prod_zpow_eq_prod_zpow_comp, prod_fiber_prod_zpow_eq_prod_zpow_comp, Finset.prod_comm, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun t' _ => ?_)
    rw [prod_zpow_eq_zpow_sum_of_ne_zero _ (coeIdeal_conjI_ne_zero_of_ne_bot (q * M) K' 𝔞 h𝔞 t'), ← zpow_sub₀ (coeIdeal_conjI_ne_zero_of_ne_bot (q * M) K' 𝔞 h𝔞 t')]
    congr 1
    rw [mul_comm (ZMod.unitsMap (dvd_mul_left M q) t') u⁻¹,
      ← thDist M q b hq hb u hu (ZMod.unitsMap (dvd_mul_left M q) t')]
    refine Finset.sum_nbij' (t' * ·) (t'⁻¹ * ·) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
      rw [map_mul, hk, mul_one]
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter, Set.mem_setOf_eq] at hk ⊢
      rw [map_mul, hk, map_inv, inv_mul_cancel]
    · intro k _
      simp
    · intro k _
      simp
    · intro k _
      rfl
  have hY0 : X / (sg M K u)⁻¹ X ≠ 0 := by
    intro h
    rw [h, zero_mul] at hY1
    exact zero_ne_one hY1
  have hr1 : Algebra.norm K X' / (X / (sg M K u)⁻¹ X) * sg M K (-1) (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) = 1 := by
    rw [map_div₀ (sg M K (-1)) (Algebra.norm K X'), div_mul_div_comm, hN1, hY1, div_one]
  have hrs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) = 1 := by
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, hspan, div_self]
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hIsXr : IsX M K b ⊤ (Algebra.norm K X' / (X / (sg M K u)⁻¹ X)) := by
    unfold IsX
    refine ⟨hr1, ?_⟩
    rw [hrs]
    simp [conjI, FractionalIdeal.coeIdeal_top]
  have hIsX1 : IsX M K b ⊤ 1 := by
    unfold IsX
    refine ⟨by simp, ?_⟩
    simp [conjI, FractionalIdeal.coeIdeal_top, FractionalIdeal.spanSingleton_one]
  obtain ⟨ζ, hζ, hrζ⟩ := xUniq M K b ⊤ 1 _ top_ne_bot hIsX1 hIsXr
  refine ⟨ζ, hζ, ?_⟩
  rw [mul_one] at hrζ
  rw [← hrζ, div_mul_cancel₀ _ hY0]
