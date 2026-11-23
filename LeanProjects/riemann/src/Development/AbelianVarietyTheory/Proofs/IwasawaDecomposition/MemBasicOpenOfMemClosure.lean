import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace GlobalTheory.BasicOpenLocalExtension

theorem exists_glue {T X Y : Scheme.{0}} [IsReduced Y] [X.IsSeparated] (j : T ⟶ Y) [IsDominant j]
    (g : T ⟶ X) {ι : Type} (V : ι → Y.Opens) (hV : IsOpenCover V) (h : ∀ i, (V i).toScheme ⟶ X)
    (hh : ∀ i, j ∣_ V i ≫ h i = (j ⁻¹ᵁ V i).ι ≫ g) : ∃ π : Y ⟶ X, j ≫ π = g := by
  have key : ∀ i {Q : Scheme.{0}} (a : Q ⟶ T) (b : Q ⟶ (V i).toScheme),
      a ≫ j = b ≫ (V i).ι → b ≫ h i = a ≫ g := by
    intro i Q a b hab
    have H := isPullback_morphismRestrict j (V i)
    have e₁ := H.lift_fst b a hab.symm
    have e₂ := H.lift_snd b a hab.symm
    rw [← e₁, Category.assoc, hh, ← Category.assoc, e₂]
  have compat : ∀ x y : ι, pullback.fst (V x).ι (V y).ι ≫ h x = pullback.snd (V x).ι (V y).ι ≫ h y := by
    intro x y
    let w : pullback (V x).ι (V y).ι ⟶ Y := pullback.fst _ _ ≫ (V x).ι
    have : IsOpenImmersion w := inferInstance
    have : IsReduced (pullback (V x).ι (V y).ι) := isReduced_of_isOpenImmersion w
    have : IsDominant (pullback.snd j w) :=
      IsZariskiLocalAtTarget.of_isPullback (P := @IsDominant) (IsPullback.of_hasPullback j w)
        inferInstance
    refine ext_of_isDominant (pullback.snd j w) ?_
    rw [← Category.assoc, ← Category.assoc, key x (pullback.fst j w), key y (pullback.fst j w)]
    · rw [pullback.condition, Category.assoc]
      exact congrArg _ pullback.condition
    · rw [pullback.condition, Category.assoc]
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  let π : Y ⟶ X := 𝒰.glueMorphisms h compat
  have hπ : ∀ i : ι, (V i).ι ≫ π = h i := fun i ↦ 𝒰.ι_glueMorphisms h compat i
  refine ⟨π, Scheme.Cover.hom_ext (𝒰.pullback₁ j) _ _ fun i : ι ↦ ?_⟩
  change pullback.fst j (V i).ι ≫ _ = pullback.fst j (V i).ι ≫ _
  rw [pullback.condition_assoc, hπ]
  exact key i _ _ pullback.condition

theorem isIso_restrict {X Y : Scheme.{0}} [IsReduced Y] (π : Y ⟶ X) [IsSeparated π] (U : X.Opens)
    (j : U.toScheme ⟶ Y) [IsDominant j] (hj : j ≫ π = U.ι) : IsIso (π ∣_ U) := by
  have H := isPullback_morphismRestrict π U
  let t : U.toScheme ⟶ (π ⁻¹ᵁ U).toScheme := H.lift (𝟙 _) j (by simp [hj])
  have e₁ : t ≫ π ∣_ U = 𝟙 _ := H.lift_fst _ _ _
  have e₂ : t ≫ (π ⁻¹ᵁ U).ι = j := H.lift_snd _ _ _
  have : IsClosedImmersion (t ≫ π ∣_ U) := e₁ ▸ inferInstance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (π ∣_ U)
  have : IsDominant (t ≫ (π ⁻¹ᵁ U).ι) := e₂ ▸ inferInstance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (π ⁻¹ᵁ U).ι
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  have : IsIso (t ≫ π ∣_ U) := e₁ ▸ inferInstance
  exact IsIso.of_isIso_comp_left t _

theorem exists_local_ext {T X Y : Scheme.{0}} (j : T ⟶ Y) (g : T ⟶ X) (V : Y.Opens) (U : X.Opens)
    (hU : IsAffineOpen U) (e : j ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) (hj : Function.Injective (j.app V))
    (H : ∀ a : Γ(X, U), ∃ b : Γ(Y, V), j.app V b = g.appLE U (j ⁻¹ᵁ V) e a) :
    ∃ h : V.toScheme ⟶ X, j ∣_ V ≫ h = (j ⁻¹ᵁ V).ι ≫ g := by
  choose b hb using H
  let σ : Γ(X, U) →+* Γ(Y, V) :=
    { toFun := b
      map_one' := hj (by rw [hb, map_one, map_one])
      map_mul' := fun x y ↦ hj (by rw [map_mul, hb, hb, hb, map_mul])
      map_zero' := hj (by rw [hb, map_zero, map_zero])
      map_add' := fun x y ↦ hj (by rw [map_add, hb, hb, hb, map_add]) }
  have hσ : CommRingCat.ofHom σ ≫ j.app V = g.appLE U (j ⁻¹ᵁ V) e := by
    ext x
    exact hb x
  refine ⟨V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom σ) ≫ hU.fromSpec, ?_⟩
  rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, hσ,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

theorem mem_basicOpen_of_mem_closure {T Z : Scheme.{0}} (γ : T ⟶ Z) (W : Z.Opens) (z : Z)
    (hz : z ∈ closure (Set.range γ)) (hW : z ∈ W) (u v : Γ(Z, W))
    (h : γ.app W v * γ.app W u = 1) : z ∈ Z.basicOpen v := by
  by_contra hv
  rw [Scheme.mem_basicOpen Z v z hW] at hv
  have h1 : z ∈ Z.basicOpen (1 - v * u) := by
    rw [Scheme.mem_basicOpen Z _ z hW, map_sub, map_one, map_mul]
    exact (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left
      fun h ↦ hv (isUnit_of_mul_isUnit_left h)
  obtain ⟨_, h2, t, rfl⟩ := mem_closure_iff.1 hz _ (Z.basicOpen (1 - v * u)).isOpen h1
  have h3 : t ∈ γ ⁻¹ᵁ Z.basicOpen (1 - v * u) := h2
  rw [Scheme.preimage_basicOpen, map_sub, map_one, map_mul, h, sub_self,
    Scheme.basicOpen_zero] at h3
  exact h3

theorem exists_index {S T X Y : Scheme.{0}} (f : X ⟶ S) [UniversallyClosed f] (q : Y ⟶ S)
    (j : T ⟶ Y) [IsDominant j] (g : T ⟶ X) (hq : g ≫ f = j ≫ q) {ι : Type} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hg : ∀ i (W : T.Opens), W ≤ g ⁻¹ᵁ U i) (y : Y) :
    ∃ i, ∀ (V : Y.Opens) (s : Γ(Y, V)) (a : Γ(X, U i)), y ∈ V →
      j.app V s * g.appLE (U i) (j ⁻¹ᵁ V) (hg _ _) a = 1 → y ∈ Y.basicOpen s := by
  let γ : T ⟶ pullback f q := pullback.lift g j hq
  have e₁ : γ ≫ pullback.fst f q = g := pullback.lift_fst _ _ _
  have e₂ : γ ≫ pullback.snd f q = j := pullback.lift_snd _ _ _
  have hcl : IsClosedMap (pullback.snd f q) := (pullback.snd f q).isClosedMap
  have hy : y ∈ (pullback.snd f q) '' closure (Set.range γ) := by
    refine (hcl _ isClosed_closure).closure_subset_iff.2 ?_ (j.denseRange y)
    rintro _ ⟨t, rfl⟩
    exact ⟨γ t, subset_closure ⟨t, rfl⟩, by rw [← Scheme.Hom.comp_apply, e₂]⟩
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨i, hi⟩ := hU.exists_mem (pullback.fst f q z)
  refine ⟨i, fun V s a hV h ↦ ?_⟩
  let W : (pullback f q).Opens := pullback.fst f q ⁻¹ᵁ U i ⊓ pullback.snd f q ⁻¹ᵁ V
  have hle : γ ⁻¹ᵁ W ≤ j ⁻¹ᵁ V := by
    rw [← e₂]
    exact fun t ht ↦ ht.2
  have H := mem_basicOpen_of_mem_closure γ W z hz ⟨hi, hV⟩
    ((pullback.fst f q).appLE (U i) W inf_le_left a)
    ((pullback.snd f q).appLE V W inf_le_right s) (by
      have h' := congrArg (T.presheaf.map (homOfLE hle).op) h
      rw [map_one, map_mul] at h'
      rw [← h']
      congr 1
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
          Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
        simp only [e₂]
      · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
          Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
        simp only [e₁])
  rw [Scheme.basicOpen_appLE] at H
  exact H.2

theorem le_preimage_top {X Y : Scheme.{0}} (f : X ⟶ Y) (U : X.Opens) : U ≤ f ⁻¹ᵁ ⊤ := le_top

theorem exists_extension {S T X Y : Scheme.{0}} [IsReduced T] [X.IsSeparated] (f : X ⟶ S)
    [UniversallyClosed f] (q : Y ⟶ S) (j : T ⟶ Y) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (g : T ⟶ X) (hq : g ≫ f = j ≫ q) {ι : Type} [DecidableEq ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (hg : ∀ i (W : T.Opens), W ≤ g ⁻¹ᵁ U i)
    {κ : ι → Type} (a : ∀ i, κ i → Γ(X, U i)) (o : ∀ i, κ i) (ho : ∀ i, a i (o i) = 1)
    (hgen : ∀ i, Subring.closure
      (Set.range (f.appLE ⊤ (U i) (le_preimage_top f _)) ∪ Set.range (a i)) = ⊤)
    (D : (∀ i, κ i) → Y.Opens) (hD : IsOpenCover D) (s : ∀ J' J, Γ(Y, D J))
    (hs : ∀ J' J, Y.basicOpen (s J' J) ≤ D J')
    (hrel : ∀ J i x, j.app (D J) (s (Function.update J i x) J) *
      g.appLE (U i) (j ⁻¹ᵁ D J) (hg _ _) (a i (J i)) = g.appLE (U i) (j ⁻¹ᵁ D J) (hg _ _) (a i x)) :
    ∃ π : Y ⟶ X, j ≫ π = g := by
  have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced j
  let V : {p : ι × (∀ i, κ i) // p.2 p.1 = o p.1} → Y.Opens := fun p ↦ D p.1.2
  have hV : IsOpenCover V := by
    refine IsOpenCover.mk (top_le_iff.1 fun y _ ↦ ?_)
    obtain ⟨i, hi⟩ := exists_index f q j g hq U hU hg y
    obtain ⟨J, hJ⟩ := hD.exists_mem y
    have h := hi (D J) (s (Function.update J i (o i)) J) (a i (J i)) hJ
      (by rw [hrel, ho, map_one])
    exact Opens.mem_iSup.2 ⟨⟨(i, Function.update J i (o i)), by simp⟩, hs _ _ h⟩
  have H : ∀ p, ∃ h : (V p).toScheme ⟶ X, j ∣_ V p ≫ h = (j ⁻¹ᵁ V p).ι ≫ g := by
    rintro ⟨⟨i, J⟩, hJ⟩
    refine exists_local_ext j g (D J) (U i) (hUa i) (hg _ _) (j.app_injective _) fun b ↦ ?_
    have hb : b ∈ ((j.app (D J)).hom.range).comap (g.appLE (U i) (j ⁻¹ᵁ D J) (hg _ _)).hom := by
      refine (Subring.closure_le.2 ?_ : Subring.closure _ ≤ _) ((hgen i).ge trivial)
      rintro _ (⟨r, rfl⟩ | ⟨x, rfl⟩)
      · refine ⟨q.appLE ⊤ (D J) (le_preimage_top q _) r, ?_⟩
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
          Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        simp only [hq]
      · refine ⟨s (Function.update J i x) J, ?_⟩
        have := hrel J i x
        rwa [show J i = o i from hJ, ho, map_one, mul_one] at this
    exact hb
  choose h hh using H
  exact exists_glue j g V hV h hh

theorem dominant_toImage {T P : Scheme.{0}} (φ : T ⟶ P) [QuasiCompact φ] :
    IsSchemeTheoreticallyDominant φ.toImage := by
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : P.affineOpens ↦ ⟨φ.imageι ⁻¹ᵁ U, U.2.preimage _⟩) ?_ fun U ↦ ?_⟩
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (φ.toImage_app_injective U)

section Proj

open HomogeneousLocalization

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

def ratio {r a : A} (hr : r ∈ 𝒜 1) (ha : a ∈ 𝒜 1) : Γ(Proj 𝒜, Proj.basicOpen 𝒜 r) :=
  Proj.awayToSection 𝒜 r (Away.isLocalizationElem hr ha)

theorem basicOpen_ratio_le {r a : A} (hr : r ∈ 𝒜 1) (ha : a ∈ 𝒜 1) :
    (Proj 𝒜).basicOpen (ratio 𝒜 hr ha) ≤ Proj.basicOpen 𝒜 a := by
  intro y hy
  have hy' : y ∈ Proj.basicOpen 𝒜 r := (Proj 𝒜).basicOpen_le _ hy
  have h1 : (⟨y, hy'⟩ : (Proj.basicOpen 𝒜 r).toScheme) ∈
      (Proj.basicOpen 𝒜 r).ι ⁻¹ᵁ (Proj 𝒜).basicOpen (ratio 𝒜 hr ha) := hy
  rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen] at h1
  have h2 : (⟨y, hy'⟩ : (Proj.basicOpen 𝒜 r).toScheme) ∈
      (Proj.basicOpenIsoSpec 𝒜 r hr one_pos).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen (Away.isLocalizationElem hr ha) := h1
  rw [← Proj.awayι_preimage_basicOpen 𝒜 hr one_pos ha one_pos, ← Scheme.Hom.comp_preimage,
    Proj.awayι, Iso.hom_inv_id_assoc] at h2
  exact h2

theorem appLE_ratio {T : Scheme.{0}} [IsAffine T] (f : A →+* Γ(T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r a : A} (hr : r ∈ 𝒜 1)
    (ha : a ∈ 𝒜 1) :
    (Proj.fromOfGlobalSections 𝒜 f hf).appLE (Proj.basicOpen 𝒜 r) (T.basicOpen (f r))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf one_pos hr).ge (ratio 𝒜 hr ha) *
      algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) (f r) =
        algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) (f a) := by
  have hW : IsAffineOpen (T.basicOpen (f r)) := (isAffineOpen_top T).basicOpen _
  let lam : Localization.Away (f r) →+* Γ(T, T.basicOpen (f r)) :=
    IsLocalization.Away.lift (f r) (g := algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)))
      (IsLocalization.Away.algebraMap_isUnit _)
  have hlam : ∀ x, lam (algebraMap _ _ x) = algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) x :=
    fun x ↦ IsLocalization.Away.lift_eq _ _ x
  have e1 : (T.isoOfEq (T.toSpecΓ_preimage_basicOpen (f r))).inv ≫ T.toSpecΓ ∣_ _ ≫
      (basicOpenIsoSpecAway (f r)).hom =
        (T.basicOpen (f r)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom lam) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away (f r)))))]
    rw [Category.assoc, Category.assoc, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
    refine (congrArg (_ ≫ ·) (morphismRestrict_ι T.toSpecΓ _)).trans ?_
    refine (Scheme.isoOfEq_inv_ι_assoc T _ _).trans ?_
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show lam.comp (algebraMap _ _) = _ from RingHom.ext hlam]
    exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top _).symm
  let ψ : Localization.Away r →+* Localization.Away (f r) :=
    IsLocalization.map (M := .powers r) (T := .powers (f r)) _ f (by
      rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])
  have e2 : (Proj.fromOfGlobalSections 𝒜 f hf).resLE _ _
      (Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos hr).ge ≫
        (Proj.basicOpenIsoSpec 𝒜 r hr one_pos).hom =
      ((T.isoOfEq (T.toSpecΓ_preimage_basicOpen (f r))).inv ≫ T.toSpecΓ ∣_ _ ≫
      (basicOpenIsoSpecAway (f r)).hom) ≫
        Spec.map (CommRingCat.ofHom (ψ.comp (algebraMap (Away 𝒜 r) (Localization.Away r)))) := by
    rw [Proj.fromOfGlobalSections_resLE 𝒜 f hf one_pos hr, Proj.toBasicOpenOfGlobalSections]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [e1, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Category.assoc, ← hW.isoSpec_hom, cancel_epi,
    ← Spec.map_comp, ← Spec.map_comp] at e2
  have e3 := congrArg (fun t ↦ t.hom (Away.isLocalizationElem hr ha)) (Spec.map_injective e2)
  refine (congrArg (· * _) e3).trans ?_
  rw [← hlam, ← hlam]
  change lam (ψ (Away.isLocalizationElem hr ha).val) * _ = _
  rw [← map_mul]
  congr 1
  have e4 : ∀ x, ψ (algebraMap _ _ x) = algebraMap _ _ (f x) := fun x ↦ IsLocalization.map_eq _ x
  rw [← e4, ← e4, ← map_mul]
  congr 1
  rw [Away.val_mk, Localization.mk_eq_mk', mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [mul_comm]

theorem appLE_ratio_mul {T : Scheme.{0}} [IsAffine T] (f : A →+* Γ(T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r a : A} (hr : r ∈ 𝒜 1)
    (ha : a ∈ 𝒜 1) (W : T.Opens)
    (hW : W ≤ Proj.fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ Proj.basicOpen 𝒜 r) {x y : Γ(T, ⊤)}
    (h : f a * x = f r * y) :
    (Proj.fromOfGlobalSections 𝒜 f hf).appLE (Proj.basicOpen 𝒜 r) W hW (ratio 𝒜 hr ha) *
      T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op x =
        T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op y := by
  have hW' : W ≤ T.basicOpen (f r) :=
    hW.trans (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf one_pos hr).le
  have h1 : (Proj.fromOfGlobalSections 𝒜 f hf).appLE (Proj.basicOpen 𝒜 r) (T.basicOpen (f r))
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf one_pos hr).ge (ratio 𝒜 hr ha) *
      algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) x =
        algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) y := by
    apply (IsLocalization.Away.algebraMap_isUnit (S := Γ(T, T.basicOpen (f r))) (f r)).mul_left_cancel
    rw [← map_mul, ← h, map_mul, ← appLE_ratio 𝒜 f hf hr ha]
    ring
  have h2 := congrArg (T.presheaf.map (homOfLE hW').op) h1
  have h3 : ∀ z, T.presheaf.map (homOfLE hW').op (algebraMap Γ(T, ⊤) Γ(T, T.basicOpen (f r)) z) =
      T.presheaf.map (homOfLE le_top : W ⟶ ⊤).op z := fun z ↦ by
    change T.presheaf.map (homOfLE hW').op (T.presheaf.map (homOfLE le_top).op z) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rwa [map_mul, h3, h3, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h2

end Proj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem iSup_basicOpen_X (R : Type) [CommRing R] (N : ℕ) :
    ⨆ n, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X n) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top' _ _ (fun n ↦ ⟨1, MvPolynomial.isHomogeneous_X R n⟩) ?_
  refine top_le_iff.1 fun p _ ↦ ?_
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _
      (⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩ :
        MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
  | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
  | mul_X p n hp => exact mul_mem (hp trivial) (Algebra.subset_adjoin ⟨n, rfl⟩)

theorem exists_generators {S X : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) : ∃ s : Finset Γ(X, U), 1 ∈ s ∧
      Subring.closure (Set.range (f.appLE ⊤ U (le_preimage_top f _)) ∪
        Set.range (fun x : s ↦ x.1)) = ⊤ := by
  classical
  have h := f.finiteType_appLE (isAffineOpen_top S) hU (le_preimage_top f U)
  algebraize [(f.appLE ⊤ U (le_preimage_top f _)).hom]
  obtain ⟨s, hs⟩ := h.out
  refine ⟨insert 1 s, Finset.mem_insert_self _ _, top_le_iff.1 ?_⟩
  have h2 := congrArg Subalgebra.toSubring hs
  rw [Algebra.adjoin_eq_ring_closure] at h2
  refine h2.ge.trans (Subring.closure_mono (Set.union_subset_union subset_rfl fun x hx ↦ ?_))
  exact ⟨⟨x, Finset.mem_insert_of_mem hx⟩, rfl⟩

theorem exists_projective_cover (R : Type) [CommRing R] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Sp R) [IsProper f] :
    ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens),
      IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hx : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x ↦ by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U₀ hU₀ hxU₀ using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U₀ x : Set X))
    (fun x ↦ (U₀ x).isOpen) fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU₀ x⟩
  let U : t → X.Opens := fun i ↦ U₀ i
  have hUa : ∀ i, IsAffineOpen (U i) := fun i ↦ hU₀ i
  have hU : IsOpenCover U := by
    refine IsOpenCover.mk (top_le_iff.1 fun x _ ↦ ?_)
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  have hξ : genericPoint X ∈ ⋂ i, (U i : Set X) := Set.mem_iInter.2 fun i ↦
    ((genericPoint_spec X).mem_open_set_iff (U i).isOpen).2 ⟨i, trivial, hxU₀ i⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hξW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hξ
    (isOpen_iInter_of_finite fun i ↦ (U i).isOpen)
  change X.Opens at W
  have : IsAffine W.toScheme := hW
  have : Nonempty W := ⟨⟨_, hξW⟩⟩
  have hg : ∀ i (V : W.toScheme.Opens), V ≤ W.ι ⁻¹ᵁ U i := fun i V y _ ↦
    Set.mem_iInter.1 (hWU y.2) i
  choose s hs1 hs using fun i ↦ exists_generators f (U i) (hUa i)
  let o : ∀ i, s i := fun i ↦ ⟨1, hs1 i⟩
  obtain ⟨N, ⟨e⟩⟩ : ∃ N, Nonempty ((∀ i, s i) ≃ Fin (N + 1)) := by
    have : Nonempty (∀ i, s i) := ⟨o⟩
    refine ⟨Fintype.card (∀ i, s i) - 1, ⟨Fintype.equivFinOfCardEq ?_⟩⟩
    have := Fintype.card_pos (α := ∀ i, s i)
    omega
  let c : ∀ i, s i → Γ(W.toScheme, ⊤) := fun i x ↦ W.ι.appLE (U i) ⊤ (hg _ _) x.1
  let m : (∀ i, s i) → Γ(W.toScheme, ⊤) := fun J ↦ ∏ i, c i (J i)
  let ρ : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) := (Scheme.ΓSpecIso _).inv ≫ (W.ι ≫ f).appTop
  let F : MvPolynomial (Fin (N + 1)) R →+* Γ(W.toScheme, ⊤) :=
    MvPolynomial.eval₂Hom ρ.hom fun n ↦ m (e.symm n)
  have hFX : ∀ J, F (MvPolynomial.X (e J)) = m J := fun J ↦ by simp [F]
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R
  have hX : ∀ n, MvPolynomial.X n ∈ 𝒜 1 := fun n ↦ MvPolynomial.isHomogeneous_X R n
  have hF : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map F = ⊤ := by
    have h1 : F (MvPolynomial.X (e o)) = 1 := by
      rw [hFX]
      exact Finset.prod_eq_one fun i _ ↦ map_one _
    rw [Ideal.eq_top_iff_one, ← h1]
    refine Ideal.mem_map_of_mem _ ?_
    exact (HomogeneousIdeal.mem_irrelevant_iff _ _).2
      (DirectSum.decompose_of_mem_ne 𝒜 (hX _) one_ne_zero)
  let φ : W.toScheme ⟶ PSpace R N := Proj.fromOfGlobalSections 𝒜 F hF
  have hφ : φ ≫ PSpace.str R N = W.ι ≫ f := by
    rw [PSpace.str, Proj.fromOfGlobalSections_toSpecZero_assoc, spMap, ← Spec.map_comp]
    have : CommRingCat.ofHom (algebraMap R (𝒜 0)) ≫
        CommRingCat.ofHom (F.comp (algebraMap (𝒜 0) _)) = ρ := by
      ext r
      exact MvPolynomial.eval₂Hom_C _ _ r
    rw [this, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp
  have : IsSeparated (PSpace.str R N) := by
    unfold PSpace.str
    infer_instance
  have : QuasiCompact (φ ≫ PSpace.str R N) := inferInstance
  have : QuasiCompact φ := QuasiCompact.of_comp φ (PSpace.str R N)
  have := dominant_toImage φ
  have hq : W.ι ≫ f = φ.toImage ≫ φ.imageι ≫ PSpace.str R N := by
    rw [Scheme.Hom.toImage_imageι_assoc, hφ]
  have : IsReduced φ.image := IsSchemeTheoreticallyDominant.isReduced φ.toImage
  obtain ⟨π, hπ⟩ := exists_extension f (φ.imageι ≫ PSpace.str R N) φ.toImage W.ι hq U hU hUa hg
    (κ := fun i ↦ s i) (fun i x ↦ x.1) o (fun _ ↦ rfl) hs
    (fun J ↦ φ.imageι ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X (e J)))
    (by
      refine IsOpenCover.mk ?_
      rw [← Scheme.Hom.preimage_iSup,
        e.iSup_comp (g := fun n ↦ Proj.basicOpen 𝒜 (MvPolynomial.X n)), iSup_basicOpen_X,
        Scheme.Hom.preimage_top])
    (fun J' J ↦ φ.imageι.app _ (ratio 𝒜 (hX (e J)) (hX (e J'))))
    (fun J' J ↦ by
      rw [← Scheme.preimage_basicOpen]
      exact fun y hy ↦ basicOpen_ratio_le 𝒜 _ _ hy)
    (fun J i x ↦ by
      have h1 : F (MvPolynomial.X (e (Function.update J i x))) * c i (J i) =
          F (MvPolynomial.X (e J)) * c i x := by
        rw [hFX, hFX]
        simp only [m]
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
          ← Finset.mul_prod_erase _ (fun k ↦ c k (J k)) (Finset.mem_univ i), Function.update_self,
          Finset.prod_congr rfl fun k hk ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]]
        ring
      have h2 := appLE_ratio_mul 𝒜 F hF (hX (e J)) (hX (e (Function.update J i x)))
        (φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X (e J)))
        (by rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι]) h1
      have h3 : ∀ (V : W.toScheme.Opens) (y : s i),
          W.toScheme.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (c i y) =
            W.ι.appLE (U i) V (hg _ _) y.1 := fun V y ↦ by
        simp only [c]
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
      rw [h3, h3] at h2
      rw [← h2, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      simp only [Scheme.Hom.toImage_imageι]
      rfl)
  have hπf : φ.imageι ≫ PSpace.str R N = π ≫ f :=
    ext_of_isDominant φ.toImage (by rw [← hq, reassoc_of% hπ])
  have : IsSeparated (π ≫ f) := hπf ▸ inferInstance
  have : IsSeparated π := IsSeparated.of_comp π f
  exact ⟨φ.image, π, W, ⟨N, φ.imageι, inferInstance, hπf⟩, ⟨_, hξW⟩,
    isIso_restrict π W φ.toImage hπ⟩

theorem chow_integral : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0})
    [IsIntegral X] (f : X ⟶ Sp R) [IsProper f],
    ∃ (X' : Scheme.{0}) (π : X' ⟶ X) (U : X.Opens),
      IsProjOver (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) :=
  fun R _ _ X _ f _ ↦ exists_projective_cover R X f

end GlobalTheory.BasicOpenLocalExtension
