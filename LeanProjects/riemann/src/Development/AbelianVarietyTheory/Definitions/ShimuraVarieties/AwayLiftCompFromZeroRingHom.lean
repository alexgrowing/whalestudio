import Mathlib

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal

universe u

noncomputable section

namespace GlobalTheory

section Quot

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)

def quotGrading (I : Ideal A) : ℕ → Submodule R (A ⧸ I) :=
  fun d => (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap

theorem mk_mem_quotGrading (I : Ideal A) {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I d := ⟨a, ha, rfl⟩

variable [GradedAlgebra 𝒜]

theorem isInternal_quotGrading {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    DirectSum.IsInternal (quotGrading 𝒜 I) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro y ⟨a, ha, rfl⟩ hy
    have hmap : (⨆ (j) (_ : j ≠ i), quotGrading 𝒜 I j) =
        (⨆ (j) (_ : j ≠ i), 𝒜 j).map (Ideal.Quotient.mkₐ R I).toLinearMap := by
      simp only [quotGrading, Submodule.map_iSup]
    rw [hmap] at hy
    obtain ⟨b, hb, hab⟩ := hy
    have hb0 : GradedRing.proj 𝒜 i b = 0 := by
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hb ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add, hx, hy, add_zero])
      intro j x hx
      refine Submodule.iSup_induction _ (motive := fun x => GradedRing.proj 𝒜 i x = 0) hx ?_
        (map_zero _) (fun x y hx hy => by simp only [map_add, hx, hy, add_zero])
      intro hji z hz
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hz hji]
    have hab' : a - b ∈ I := Ideal.Quotient.eq.mp hab.symm
    have h2 : GradedRing.proj 𝒜 i (a - b) ∈ I := hI i hab'
    rw [map_sub, hb0, sub_zero, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 ha] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  · have htop := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top
    change (⨆ d, (𝒜 d).map (Ideal.Quotient.mkₐ R I).toLinearMap) = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective R I)

instance gradedMonoid_quotGrading (I : Ideal A) : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one (Ideal.Quotient.mkₐ R I)⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, map_mul (Ideal.Quotient.mkₐ R I) a b⟩

@[reducible] def quotGradedAlgebra {I : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (quotGrading 𝒜 I) where
  toGradedMonoid := inferInstance
  toDecomposition := (isInternal_quotGrading 𝒜 hI).chooseDecomposition

end Quot

namespace ProjPoint

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]

def awayLift (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) : Away 𝒜 f →+* B :=
  (IsLocalization.Away.lift (S := Localization.Away f) f hf).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

theorem awayLift_mk_mul (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d) (n : ℕ)
    (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayLift 𝒜 φ f hf (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a := by
  have h1 : φ f ^ n = IsLocalization.Away.lift (S := Localization.Away f) f hf
      (algebraMap A _ (f ^ n)) := by
    rw [IsLocalization.Away.lift_eq, map_pow]
  rw [h1, awayLift, RingHom.comp_apply, ← map_mul, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mk'_spec (Localization.Away f) a ⟨f ^ n, _⟩, IsLocalization.Away.lift_eq]

theorem eq_awayLift (φ : A →+* B) {f : A} (hf : IsUnit (φ f)) {d : ℕ} (hd : f ∈ 𝒜 d)
    (g : Away 𝒜 f →+* B)
    (hg : ∀ n a ha, g (Away.mk 𝒜 hd n a ha) * φ f ^ n = φ a) : g = awayLift 𝒜 φ f hf := by
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd x
  apply (hf.pow n).mul_right_cancel
  rw [hg, awayLift_mk_mul]

theorem awayLift_comp_fromZeroRingHom (φ : A →+* B) (f : A) (hf : IsUnit (φ f)) :
    (awayLift 𝒜 φ f hf).comp (fromZeroRingHom 𝒜 _) = φ.comp (algebraMap (𝒜 0) A) := by
  ext a
  change IsLocalization.Away.lift (S := Localization.Away f) f hf
    (algebraMap (Away 𝒜 f) _ (algebraMap (𝒜 0) _ a)) = _
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝒜 0) A,
    IsLocalization.Away.lift_eq]
  rfl

theorem map_irrelevant_comp {φ : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    (irrelevant 𝒜).toIdeal.map (ψ.comp φ) = ⊤ := by
  rw [← Ideal.map_map, hφ, Ideal.map_top]

def ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) : Spec (.of B) ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso (.of B)).inv.hom.comp φ)
    (map_irrelevant_comp 𝒜 hφ _)

theorem ofHom_preimage_basicOpen (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {r : A} {n : ℕ} (hn : 0 < n) (hr : r ∈ 𝒜 n) :
    ofHom 𝒜 φ hφ ⁻¹ᵁ Proj.basicOpen 𝒜 r = PrimeSpectrum.basicOpen (φ r) := by
  rw [ofHom, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hn hr]
  exact basicOpen_eq_of_affine (R := .of B) (φ r)

@[reassoc]
theorem ofHom_toSpecZero (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) :
    ofHom 𝒜 φ hφ ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (𝒜 0) A))) := by
  rw [ofHom, Proj.fromOfGlobalSections_toSpecZero, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  simp

set_option backward.isDefEq.respectTransparency false in

@[reassoc]
theorem SpecMap_ofHom_eq_awayι (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (ψ : B →+* C) {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (ψ (φ f))) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      Spec.map (CommRingCat.ofHom (awayLift 𝒜 (ψ.comp φ) f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  set φ' := (Scheme.ΓSpecIso (.of B)).inv.hom.comp φ with hφ'
  have hφ'' := map_irrelevant_comp 𝒜 hφ (Scheme.ΓSpecIso (.of B)).inv.hom
  have hrange : Set.range (Spec.map (CommRingCat.ofHom ψ)) ⊆
      Set.range ((Spec (.of B)).basicOpen (φ' f)).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ∈ (Spec (.of B)).basicOpen ((Scheme.ΓSpecIso (.of B)).inv (φ f))
    rw [basicOpen_eq_of_affine]
    exact fun h => x.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  let l := IsOpenImmersion.lift _ _ hrange
  have hl : l ≫ _ = _ := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : ((Spec (.of B)).basicOpen (φ' f)).ι ≫ ofHom 𝒜 φ hφ =
      Proj.toBasicOpenOfGlobalSections 𝒜 φ' rfl hn hf ≫ (Proj.basicOpen 𝒜 f).ι := by
    rw [← Proj.fromOfGlobalSections_resLE 𝒜 φ' hφ'' hn hf, Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← hl, Category.assoc, h1, Proj.awayι, Proj.toBasicOpenOfGlobalSections]
  simp only [← Category.assoc]
  congr 2
  let ψ' : Γ(Spec (.of B), ⊤) →+* C := ψ.comp (Scheme.ΓSpecIso (.of B)).hom.hom
  have hψ' : ∀ a, ψ' (φ' a) = ψ (φ a) := by
    intro a
    simp [ψ', φ']
  have hu' : IsUnit (ψ' (φ' f)) := hψ' f ▸ hu
  have h2 : ((l ≫ ((Spec (.of B)).isoOfEq
      ((Spec (.of B)).toSpecΓ_preimage_basicOpen (φ' f))).inv) ≫
      (Spec (.of B)).toSpecΓ ∣_ (PrimeSpectrum.basicOpen (φ' f))) ≫
      (basicOpenIsoSpecAway (φ' f)).hom = Spec.map (CommRingCat.ofHom
        (IsLocalization.Away.lift (S := Localization.Away (φ' f)) (φ' f) hu')) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Spec (.of B), ⊤) (Localization.Away (φ' f)))))]
    simp only [Category.assoc, basicOpenIsoSpecAway, IsOpenImmersion.isoOfRangeEq_hom_fac,
      morphismRestrict_ι, Scheme.isoOfEq_inv_ι_assoc]
    rw [reassoc_of% hl, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ', IsLocalization.Away.lift_eq]
  rw [h2, ← Spec.map_comp]
  congr 2
  rw [← CommRingCat.ofHom_comp, awayLift, ← RingHom.comp_assoc]
  congr 2
  apply IsLocalization.ringHom_ext (M := .powers f)
  ext a
  simp [IsLocalization.Away.lift_eq, hψ']

theorem ofHom_eq_awayι (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (φ f)) :
    ofHom 𝒜 φ hφ = Spec.map (CommRingCat.ofHom (awayLift 𝒜 φ f hu)) ≫ Proj.awayι 𝒜 f hf hn := by
  simpa using SpecMap_ofHom_eq_awayι 𝒜 φ hφ (RingHom.id B) hn hf hu

theorem hom_ext (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) {Y : Scheme.{u}}
    {g₁ g₂ : Spec (.of B) ⟶ Y}
    (h : ∀ (C : Type u) [CommRing C] (ψ : B →+* C) (f : A) (n : ℕ), 0 < n → f ∈ 𝒜 n →
      IsUnit (ψ (φ f)) →
      Spec.map (CommRingCat.ofHom ψ) ≫ g₁ = Spec.map (CommRingCat.ofHom ψ) ≫ g₂) : g₁ = g₂ := by
  let s : {f : A // ∃ n, 0 < n ∧ f ∈ 𝒜 n} → (CommRingCat.of B) := fun f => φ f.1
  have hs : Ideal.span (Set.range s) = ⊤ := by
    rw [_root_.eq_top_iff, ← hφ, Ideal.map_le_iff_le_comap, toIdeal_irrelevant_le]
    intro i hi x hx
    exact Ideal.subset_span ⟨⟨x, i, hi, hx⟩, rfl⟩
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop s hs).openCover.hom_ext _ _ fun i => ?_
  obtain ⟨n, hn, hf⟩ := i.2
  exact h (Localization.Away (φ i.1)) (algebraMap B _) i.1 n hn hf
    (IsLocalization.Away.algebraMap_isUnit _)

@[reassoc]
theorem SpecMap_ofHom (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      ofHom 𝒜 (ψ.comp φ) (map_irrelevant_comp 𝒜 hφ ψ) := by
  refine hom_ext 𝒜 _ (map_irrelevant_comp 𝒜 hφ ψ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    SpecMap_ofHom_eq_awayι 𝒜 φ hφ (χ.comp ψ) hn hf hu]

theorem ofHom_eq_of_scale {φ φ' : A →+* B} (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (hφ' : (irrelevant 𝒜).toIdeal.map φ' = ⊤) (c : B)
    (hc : ∀ n, ∀ a ∈ 𝒜 n, φ' a = c ^ n * φ a) : ofHom 𝒜 φ' hφ' = ofHom 𝒜 φ hφ := by
  refine hom_ext 𝒜 _ hφ' fun D _ χ f n hn hf hu => ?_
  have hu2 := hu
  rw [hc n f hf, map_mul, IsUnit.mul_iff] at hu2
  rw [SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu, SpecMap_ofHom_eq_awayι 𝒜 _ _ χ hn hf hu2.2]
  congr 3
  symm
  refine eq_awayLift 𝒜 _ _ hf _ fun m a ha => ?_
  have := awayLift_mk_mul 𝒜 (χ.comp φ) hu2.2 hf m a ha
  simp only [RingHom.comp_apply] at this ⊢
  generalize awayLift 𝒜 (χ.comp φ) f hu2.2 (Away.mk 𝒜 hf m a ha) = t at this ⊢
  rw [hc _ a ha, hc n f hf, map_mul, map_mul, ← this, mul_pow, smul_eq_mul, map_pow, map_pow]
  ring

section Map

variable {A' τ τ' : Type u} {A₀ : Type u} [CommRing A₀] [CommRing A'] [SetLike τ A₀]
  [AddSubgroupClass τ A₀] [SetLike τ' A'] [AddSubgroupClass τ' A']
  {𝒜₀ : ℕ → τ} {ℬ : ℕ → τ'} [GradedRing 𝒜₀] [GradedRing ℬ]

theorem map_irrelevant_comp_graded (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    {φ : A' →+* B} (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    (irrelevant 𝒜₀).toIdeal.map (φ.comp g.toRingHom) = ⊤ := by
  rw [← Ideal.map_map, _root_.eq_top_iff, ← hφ]
  exact Ideal.map_mono hg

@[reassoc]
theorem ofHom_map (g : 𝒜₀ →+*ᵍ ℬ) (hg : irrelevant ℬ ≤ (irrelevant 𝒜₀).map g)
    (φ : A' →+* B) (hφ : (irrelevant ℬ).toIdeal.map φ = ⊤) :
    ofHom ℬ φ hφ ≫ Proj.map g hg =
      ofHom 𝒜₀ (φ.comp g.toRingHom) (map_irrelevant_comp_graded g hg hφ) := by
  refine hom_ext 𝒜₀ _ (map_irrelevant_comp_graded g hg hφ) fun D _ χ f n hn hf hu => ?_
  rw [SpecMap_ofHom_eq_awayι 𝒜₀ _ _ χ hn hf hu,
    SpecMap_ofHom_eq_awayι_assoc ℬ φ hφ χ hn (g.2 hf) hu]
  erw [Proj.awayι_comp_map g hg hn f hf]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  refine eq_awayLift 𝒜₀ _ _ hf _ fun m a ha => ?_
  rw [RingHom.comp_apply]
  erw [Away.map_mk]
  exact awayLift_mk_mul ℬ (χ.comp φ) hu (g.2 hf) m _ _

end Map

end ProjPoint

end GlobalTheory
