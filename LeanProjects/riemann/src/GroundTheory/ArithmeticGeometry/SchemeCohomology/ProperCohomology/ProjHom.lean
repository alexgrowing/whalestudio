import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
set_option maxSynthPendingDepth 1

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization

namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjHom

variable {X : Scheme.{u}}

lemma specCorr_comp {Y : Scheme.{u}} {R S : CommRingCat.{u}} (a : Y ⟶ Spec S) (φ : R ⟶ S) :
    (Scheme.ΓSpecIso R).inv ≫ (a ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso S).inv ≫ a.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def toSpecAway (x : Γ(X, ⊤)) : (X.basicOpen x).toScheme ⟶ Spec (.of (Localization.Away x)) :=
  ((X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫ X.toSpecΓ ∣_ (PrimeSpectrum.basicOpen x)) ≫
    (basicOpenIsoSpecAway x).hom

lemma toSpecAway_SpecMap (x : Γ(X, ⊤)) :
    toSpecAway x ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x))) =
      (X.basicOpen x).ι ≫ X.toSpecΓ := by
  simp only [toSpecAway, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  have h1 := morphismRestrict_ι X.toSpecΓ (PrimeSpectrum.basicOpen x)
  calc _ = (X.isoOfEq (X.toSpecΓ_preimage_basicOpen x)).inv ≫
        (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen x).ι ≫ X.toSpecΓ := by
          congr 1
    _ = _ := Scheme.isoOfEq_inv_ι_assoc _ _ _

lemma specCorr_toSpecAway (x : Γ(X, ⊤)) :
    CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away x)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (toSpecAway x).appTop = (X.basicOpen x).ι.appTop := by
  rw [← specCorr_comp, toSpecAway_SpecMap, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact Iso.inv_hom_id_assoc _ _

lemma specCorr_toSpecAway_apply (x : Γ(X, ⊤)) (z : Γ(X, ⊤)) :
    ((Scheme.ΓSpecIso _).inv ≫ (toSpecAway x).appTop) (algebraMap Γ(X, ⊤) (Localization.Away x) z) =
      (X.basicOpen x).ι.appTop z := by
  rw [← specCorr_toSpecAway x, ConcreteCategory.comp_apply]
  rfl

def corr (g : X ⟶ Proj 𝒜) (r : A) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r) :
    CommRingCat.of (Away 𝒜 r) ⟶ Γ(V, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (g.resLE _ V h ≫ Proj.basicOpenToSpec 𝒜 r).appTop

variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

lemma corr_fromOfGlobalSections {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r (X.basicOpen (f r))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hd hr).ge (Away.mk 𝒜 hr k a ha) *
      (X.basicOpen (f r)).ι.appTop (f r) ^ k = (X.basicOpen (f r)).ι.appTop (f a) := by
  rw [corr, Proj.fromOfGlobalSections_resLE 𝒜 f hf hd hr, Proj.toBasicOpenOfGlobalSections]
  simp only [Category.assoc, ← Proj.basicOpenIsoSpec_hom 𝒜 r hr hd, Iso.inv_hom_id,
    Category.comp_id]
  simp only [← Category.assoc]
  rw [specCorr_comp]
  change ((CommRingCat.ofHom _ ≫ (Scheme.ΓSpecIso _).inv ≫ (toSpecAway (f r)).appTop) _) * _ = _
  rw [← specCorr_toSpecAway_apply, ← specCorr_toSpecAway_apply, ← map_pow]
  rw [ConcreteCategory.comp_apply (CommRingCat.ofHom _), ← map_mul]
  congr 1
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rw [← map_pow, ← map_pow f]
  exact IsLocalization.mk'_spec (Localization.Away (f r)) (f a) _

lemma corr_fromOfGlobalSections' {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (V : X.Opens)
    (hV : X.basicOpen (f r) = V) (h : V ≤ Proj.fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ Proj.basicOpen 𝒜 r)
    (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r V h (Away.mk 𝒜 hr k a ha) *
      V.ι.appTop (f r) ^ k = V.ι.appTop (f a) := by
  subst hV
  exact corr_fromOfGlobalSections 𝒜 f hf hd hr k a ha

lemma corr_comp {Y : Scheme.{u}} (h : Y ⟶ X) (g : X ⟶ Proj 𝒜) (r : A) {V : X.Opens}
    {W : Y.Opens} (hV : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r) (hW : W ≤ h ⁻¹ᵁ V) :
    corr 𝒜 (h ≫ g) r W (hW.trans ((TopologicalSpace.Opens.map h.base).map (homOfLE hV)).le) =
      corr 𝒜 g r V hV ≫ (h.resLE V W hW).appTop := by
  rw [corr, corr, ← Scheme.Hom.resLE_comp_resLE, Category.assoc, Scheme.Hom.comp_appTop,
    Category.assoc]

set_option backward.isDefEq.respectTransparency false in

lemma isUnit_of_basicOpen_eq_top {Y : Scheme.{u}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) :
    IsUnit s := by
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op s) :=
    Y.toRingedSpace.isUnit_res_basicOpen s
  convert! (Y.presheaf.map (eqToHom h.symm).op).hom.isUnit_map hu
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : (homOfLE (Y.basicOpen_le s)).op ≫ (eqToHom h.symm).op = 𝟙 (op ⊤) :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

lemma isUnit_ι_appTop (x : Γ(X, ⊤)) : IsUnit ((X.basicOpen x).ι.appTop x) := by
  apply isUnit_of_basicOpen_eq_top
  change ((X.basicOpen x).toScheme).basicOpen ((X.basicOpen x).ι.app ⊤ x) = ⊤
  rw [← Scheme.preimage_basicOpen]
  exact Scheme.Opens.ι_preimage_self _

lemma mul_pow_cancel {R : Type*} [CommRing R] {v u w c : R} (hc : IsUnit c) (k d : ℕ)
    (h : v * (c ^ d * u) ^ k = c ^ (k • d) * w) : v * u ^ k = w := by
  apply (hc.pow (k * d)).mul_right_injective
  simp only [smul_eq_mul] at h
  calc c ^ (k * d) * (v * u ^ k) = v * (c ^ d * u) ^ k := by ring
    _ = c ^ (k * d) * w := h

lemma mul_pow_cancel' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {v : S}
    {u u' w w' c : R} (hc : IsUnit c) (k d : ℕ) (hu : u' = c ^ d * u) (hw : w' = c ^ (k • d) * w)
    (h : v * φ u' ^ k = φ w') : v * φ u ^ k = φ w := by
  subst hu hw
  rw [map_mul, map_mul, map_pow, map_pow] at h
  exact mul_pow_cancel (hc.map φ) k d h

lemma transfer {R S : CommRingCat.{u}} (ρ : R ⟶ S) {v x y : R} {x' y' : S} (hx : ρ x = x')
    (hy : ρ y = y') (k : ℕ) (h : v * x ^ k = y) : ρ v * x' ^ k = y' := by
  subst hx hy
  rw [← map_pow, ← map_mul, h]

theorem hom_ext {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) {g g' : X ⟶ Proj 𝒜}
    (V : ι → X.Opens) (hV : ∀ i, g ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = V i)
    (hV' : ∀ i, g' ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = V i)
    (hc : ∀ i, corr 𝒜 g (r i) (V i) (hV i).ge = corr 𝒜 g' (r i) (V i) (hV' i).ge) : g = g' := by
  have hVcov : ⨆ i, V i = ⊤ := by
    simp_rw [← hV]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    rfl
  refine (X.openCoverOfIsOpenCover V hVcov).hom_ext _ _ fun i => ?_
  have h1 : g.resLE _ (V i) (hV i).ge ≫ Proj.basicOpenToSpec 𝒜 (r i) =
      g'.resLE _ (V i) (hV' i).ge ≫ Proj.basicOpenToSpec 𝒜 (r i) := ext_to_Spec (hc i)
  have : IsIso (Proj.basicOpenToSpec 𝒜 (r i)) := by
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 (r i) (hr i) (hd i)]
    infer_instance
  have h2 := (cancel_mono _).1 h1
  change (V i).ι ≫ g = (V i).ι ≫ g'
  rw [← Scheme.Hom.resLE_comp_ι g (hV i).ge, ← Scheme.Hom.resLE_comp_ι g' (hV' i).ge, h2]

variable {𝒜} in

theorem eq_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) (g : X ⟶ Proj 𝒜)
    (hg : ∀ i, g ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) = X.basicOpen (f (r i)))
    (hc : ∀ i k a (ha : a ∈ 𝒜 (k • d i)),
      corr 𝒜 g (r i) _ (hg i).ge (Away.mk 𝒜 (hr i) k a ha) *
        (X.basicOpen (f (r i))).ι.appTop (f (r i)) ^ k =
        (X.basicOpen (f (r i))).ι.appTop (f a)) :
    g = Proj.fromOfGlobalSections 𝒜 f hf := by
  refine hom_ext 𝒜 r d hd hr hcov (fun i => X.basicOpen (f (r i))) hg
    (fun i => Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i)) fun i => ?_
  ext y
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (hr i) y
  exact ((isUnit_ι_appTop (f (r i))).pow k).mul_left_injective
    ((hc i k a ha).trans (corr_fromOfGlobalSections 𝒜 f hf (hd i) (hr i) k a ha).symm)

variable {𝒜} in

theorem comp_fromOfGlobalSections {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤) {Y : Scheme.{u}}
    (h : Y ⟶ X) :
    h ≫ Proj.fromOfGlobalSections 𝒜 f hf = Proj.fromOfGlobalSections 𝒜 (h.appTop.hom.comp f)
      (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
  have hpreX : ∀ i, h ⁻¹ᵁ X.basicOpen (f (r i)) = Y.basicOpen ((h.appTop.hom.comp f) (r i)) :=
    fun i => Scheme.preimage_basicOpen h (f (r i))
  have hpre : ∀ i, (h ≫ Proj.fromOfGlobalSections 𝒜 f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) =
      Y.basicOpen ((h.appTop.hom.comp f) (r i)) := fun i => by
    rw [Scheme.Hom.comp_preimage, Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i),
      hpreX]
  refine eq_fromOfGlobalSections _ _ r d hd hr hcov _ hpre fun i k a ha => ?_
  have hW := (hpreX i).ge
  have hι : ∀ z, (h.resLE _ _ hW).appTop ((X.basicOpen (f (r i))).ι.appTop (f z)) =
      (Y.basicOpen ((h.appTop.hom.comp f) (r i))).ι.appTop ((h.appTop.hom.comp f) z) := fun z => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
    rfl
  rw [corr_comp 𝒜 h _ (r i) (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf (hd i) (hr i)).ge hW,
    ConcreteCategory.comp_apply]
  exact transfer _ (hι _) (hι _) k (corr_fromOfGlobalSections 𝒜 f hf (hd i) (hr i) k a ha)

variable {𝒜} in

theorem fromOfGlobalSections_eq_of_twist {ι : Type*} (r : ι → A) (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (hr : ∀ i, r i ∈ 𝒜 (d i)) (hcov : ⨆ i, Proj.basicOpen 𝒜 (r i) = ⊤)
    (f' : A →+* Γ(X, ⊤)) (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤)
    (c : Γ(X, ⊤)) (hc : IsUnit c) (hff' : ∀ m a, a ∈ 𝒜 m → f' a = c ^ m * f a) :
    Proj.fromOfGlobalSections 𝒜 f' hf' = Proj.fromOfGlobalSections 𝒜 f hf := by
  have hb : ∀ i, X.basicOpen (f' (r i)) = X.basicOpen (f (r i)) := fun i => by
    rw [hff' _ _ (hr i), Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hc.pow _), top_inf_eq]
  refine eq_fromOfGlobalSections _ _ r d hd hr hcov _
    (fun i => (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f' hf' (hd i) (hr i)).trans (hb i))
    fun i k a ha => ?_
  have hle : X.basicOpen (f (r i)) ≤
      Proj.fromOfGlobalSections 𝒜 f' hf' ⁻¹ᵁ Proj.basicOpen 𝒜 (r i) :=
    ((Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f' hf' (hd i) (hr i)).trans (hb i)).ge
  exact mul_pow_cancel' (X.basicOpen (f (r i))).ι.appTop.hom hc k (d i) (hff' _ _ (hr i))
    (hff' _ _ ha) (corr_fromOfGlobalSections' 𝒜 f' hf' (hd i) (hr i) _ (hb i) hle k a ha)

end ProjHom
end
end GroundTheory.Arith.SchemeCoh
