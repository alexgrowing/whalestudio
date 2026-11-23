import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private theorem sec_open {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by
  have hgraph := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pullback_lift_diagonal_isPullback s f) inferInstance
  have hiso : ∀ u : S ⟶ S, u = 𝟙 S → IsIso (pullback.snd u f) := by
    rintro _ rfl
    infer_instance
  have := hiso _ hs
  have h : IsOpenImmersion (pullback.lift (𝟙 S) s (by simp) ≫ pullback.snd (s ≫ f) f) := inferInstance
  rwa [pullback.lift_snd] at h

private theorem disj_of_splitOn {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ} (z : Fin m → (X ⟶ Z))
    (h : SplitOn p x z) (a b : Fin m) (hab : a ≠ b) (S : Scheme.{0}) (t : S ⟶ X)
    (ht : t ≫ z a = t ≫ z b) : IsEmpty S := by
  obtain ⟨h, hiso⟩ := h
  have e : (t ≫ Sigma.ι (fun _ : Fin m => X) a) = t ≫ Sigma.ι (fun _ : Fin m => X) b := by
    rw [← cancel_mono (Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p x)]
    simp only [Category.assoc, Sigma.ι_desc]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]; exact ht
    · simp only [Category.assoc, pullback.lift_snd]
  refine ⟨fun s => ?_⟩
  have hd := disjoint_opensRange_sigmaι (fun _ : Fin m => X) a b hab
  have h1 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) a).opensRange := by
    simp
  have h2 : (t ≫ Sigma.ι (fun _ : Fin m => X) a) s ∈ (Sigma.ι (fun _ : Fin m => X) b).opensRange := by
    rw [e]; simp
  have h3 := hd.le_bot ⟨h1, h2⟩
  exact h3

private theorem liftClosed {W P : Scheme.{0}} (ι : W ⟶ P) [IsClosedImmersion ι] (U U' : Type) [CommRing U] [CommRing U']
    (φ : U →+* U') (hφ : Function.Injective φ) (u : Spec (CommRingCat.of U) ⟶ P)
    (v : Spec (CommRingCat.of U') ⟶ W) (h : v ≫ ι = Spec.map (CommRingCat.ofHom φ) ≫ u) :
    ∃ w : Spec (CommRingCat.of U) ⟶ W, w ≫ ι = u := by
  let g := pullback.snd ι u
  have hcl : IsClosedImmersion g := inferInstance
  let v' : Spec (CommRingCat.of U') ⟶ pullback ι u := pullback.lift v (Spec.map (CommRingCat.ofHom φ)) h
  have hv' : v' ≫ g = Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  obtain ⟨hA, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  have hinj : Function.Injective g.appTop.hom := by
    have h0 : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop.hom := by
      have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
      intro a b hab
      have h2 : ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom a =
          ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso _).hom).hom b := by
        simp only [CommRingCat.hom_comp, RingHom.comp_apply]
        rw [hab]
      rw [e] at h2
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of U)).hom).1 (hφ h2)
    rw [← hv'] at h0
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at h0
    exact Function.Injective.of_comp h0
  have hiso : IsIso g.appTop := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, hsurj⟩
  have hg : IsIso g := by
    have e := Scheme.isoSpec_hom_naturality g
    have : IsIso (g ≫ (Spec (CommRingCat.of U)).isoSpec.hom) := by
      rw [← e]; infer_instance
    exact IsIso.of_isIso_comp_right g (Spec (CommRingCat.of U)).isoSpec.hom
  refine ⟨inv g ≫ pullback.fst ι u, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

private theorem closureOf (P : Scheme.{0}) (a : Γ(P, ⊤)) (D D' : P.Opens) (h : D ⊔ D' = P.basicOpen a)
    (h' : D ⊓ D' = ⊥) :
    ∃ (W : Scheme.{0}) (ι : W ⟶ P) (v : D.toScheme ⟶ W), IsClosedImmersion ι ∧ v ≫ ι = D.ι ∧
      ∀ w : W, ι w ∈ P.basicOpen a → ι w ∈ D := by
  have hq : QuasiCompact D.ι := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    rw [D.ι.isOpenEmbedding.isInducing.isCompact_iff]
    change IsCompact (D.ι '' (D.ι ⁻¹' (V : Set P)))
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    have hc : IsCompact ((V : Set P) ∩ P.basicOpen a) := by
      have := (hV.basicOpen (P.presheaf.map (homOfLE le_top).op a)).isCompact
      rwa [Scheme.basicOpen_res] at this
    have hc2 := hc.diff D'.2
    convert hc2 using 1
    ext x
    constructor
    · rintro ⟨hv, hd⟩
      refine ⟨⟨hv, ?_⟩, fun hd' => ?_⟩
      · have : x ∈ D ⊔ D' := Or.inl hd
        rw [h] at this; exact this
      · have : x ∈ D ⊓ D' := ⟨hd, hd'⟩
        rw [h'] at this; exact this
    · rintro ⟨⟨hv, hb⟩, hd'⟩
      have : x ∈ D ⊔ D' := by rw [h]; exact hb
      exact ⟨hv, this.resolve_right hd'⟩
  refine ⟨D.ι.image, D.ι.imageι, D.ι.toImage, inferInstance, D.ι.toImage_imageι, fun w hw => ?_⟩
  have h1 : D.ι.imageι w ∈ closure (Set.range D.ι) := by
    rw [← Scheme.Hom.support_ker]
    have : Set.range D.ι.imageι = D.ι.ker.support := by
      exact Scheme.IdealSheafData.range_subschemeι _
    rw [← this]
    exact ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι] at h1
  have h2 : D.ι.imageι w ∈ D ⊔ D' := by rw [h]; exact hw
  refine h2.resolve_right fun hd' => ?_
  obtain ⟨y, hy, hy'⟩ := mem_closure_iff.1 h1 D' D'.2 hd'
  have : y ∈ D' ⊓ D := ⟨hy, hy'⟩
  rw [inf_comm, h'] at this
  exact this

private theorem natUnit_comp {X S : Scheme.{0}} (t : S ⟶ X) (l : ℕ) (h : IsUnit (l : Γ(X, ⊤))) : IsUnit (l : Γ(S, ⊤)) := by
  have := h.map t.appTop.hom
  simpa using this

private theorem natUnit_mem {X A : Scheme.{0}} (t : X ⟶ A) (l : ℕ) (h : IsUnit (l : Γ(X, ⊤))) (x : X) :
    t x ∈ A.basicOpen (l : Γ(A, ⊤)) := by
  have h1 : X.basicOpen (t.appTop.hom (l : Γ(A, ⊤))) = ⊤ := by
    simpa using Scheme.basicOpen_of_isUnit X h
  have h2 : x ∈ t ⁻¹ᵁ A.basicOpen (l : Γ(A, ⊤)) := by
    rw [Scheme.preimage_basicOpen_top, h1]
    trivial
  exact h2

private theorem eqLocus₀ {Z Y : Scheme.{0}} (p : Z ⟶ Y) [Etale p] [IsSeparated p] (A : Scheme.{0}) (f g : A ⟶ Z)
    (hfg : f ≫ p = g ≫ p) :
    ∃ O O' : A.Opens, O ⊔ O' = ⊤ ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ A), (∀ x, t x ∈ O) ↔ t ≫ f = t ≫ g := by
  let Δ := pullback.diagonal p
  have hΔ : IsOpenImmersion Δ := sec_open (pullback.fst p p) Δ (pullback.diagonal_fst p)
  have hc : IsClosedImmersion Δ := inferInstance
  let c := pullback.lift f g hfg
  have cf : c ≫ pullback.fst p p = f := pullback.lift_fst _ _ _
  have cs : c ≫ pullback.snd p p = g := pullback.lift_snd _ _ _
  have hcl : IsClosed (Set.range Δ) := Δ.isClosedEmbedding.isClosed_range
  let R : (pullback p p).Opens := Δ.opensRange
  let R' : (pullback p p).Opens := ⟨(Set.range Δ)ᶜ, hcl.isOpen_compl⟩
  refine ⟨c ⁻¹ᵁ R, c ⁻¹ᵁ R', ?_, ?_, fun X t => ⟨fun h => ?_, fun h x => ?_⟩⟩
  · rw [eq_top_iff]
    intro x _
    by_cases h : c x ∈ Set.range Δ
    · exact Or.inl h
    · exact Or.inr h
  · rw [eq_bot_iff]
    rintro x ⟨h1, h2⟩
    exact (h2 h1).elim
  · have r : Set.range (t ≫ c) ⊆ Set.range Δ := by
      rintro _ ⟨x, rfl⟩
      exact h x
    have hk := IsOpenImmersion.lift_fac Δ (t ≫ c) r
    generalize IsOpenImmersion.lift Δ (t ≫ c) r = k at hk
    have e1 : k = t ≫ f := by
      have := congrArg (· ≫ pullback.fst p p) hk
      simp only [Category.assoc] at this
      rw [show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p, cf, Category.comp_id] at this
      exact this
    have e2 : k = t ≫ g := by
      have := congrArg (· ≫ pullback.snd p p) hk
      simp only [Category.assoc] at this
      rw [show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p, cs, Category.comp_id] at this
      exact this
    exact e1.symm.trans e2
  · have e : t ≫ c = (t ≫ f) ≫ Δ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cf, show Δ ≫ pullback.fst p p = 𝟙 _ from pullback.diagonal_fst p,
          Category.comp_id]
      · rw [Category.assoc, Category.assoc, cs, show Δ ≫ pullback.snd p p = 𝟙 _ from pullback.diagonal_snd p,
          Category.comp_id, h]
    have : (t ≫ c) x ∈ Set.range Δ := by
      rw [e]
      exact ⟨(t ≫ f) x, by simp⟩
    exact this

private theorem eqLocus (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (A : Scheme.{0}) (f g : A ⟶ T.Z)
    (hfg : f ≫ T.p = g ≫ T.p) :
    ∃ O O' : A.Opens, O ⊔ O' = A.basicOpen (l : Γ(A, ⊤)) ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ A), IsUnit (l : Γ(X, ⊤)) → ((∀ x, t x ∈ O) ↔ t ≫ f = t ≫ g) := by
  let U := Y.basicOpen (l : Γ(Y, ⊤))
  let B := A.basicOpen (l : Γ(A, ⊤))
  have hpre : ∀ h : A ⟶ Y, B ≤ h ⁻¹ᵁ U := by
    intro h
    rw [Scheme.preimage_basicOpen_top]
    simp [B]
  have het : Etale (T.p ∣_ U) := T.et
  have hfin : IsFinite T.p := T.fin
  have hsep : IsSeparated (T.p ∣_ U) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_morphismRestrict T.p U).flip inferInstance
  have hf : B ≤ f ⁻¹ᵁ (T.p ⁻¹ᵁ U) := hpre (f ≫ T.p)
  have hg : B ≤ g ⁻¹ᵁ (T.p ⁻¹ᵁ U) := hpre (g ≫ T.p)
  let f' := f.resLE (T.p ⁻¹ᵁ U) B hf
  let g' := g.resLE (T.p ⁻¹ᵁ U) B hg
  have hf' : f' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
  have hg' : g' ≫ (T.p ⁻¹ᵁ U).ι = B.ι ≫ g := Scheme.Hom.resLE_comp_ι _ _
  have hfg' : f' ≫ (T.p ∣_ U) = g' ≫ (T.p ∣_ U) := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf',
      ← Category.assoc, hg', Category.assoc, Category.assoc, hfg]
  obtain ⟨O₀, O₀', a, b, c⟩ := eqLocus₀ (T.p ∣_ U) B.toScheme f' g' hfg'
  have memI : ∀ (V : B.toScheme.Opens) (x : B.toScheme), B.ι x ∈ B.ι ''ᵁ V ↔ x ∈ V := by
    intro V x
    constructor
    · rintro ⟨y, hy, e⟩
      rwa [← B.ι.isOpenEmbedding.injective e]
    · exact fun h => ⟨x, h, rfl⟩
  refine ⟨B.ι ''ᵁ O₀, B.ι ''ᵁ O₀', ?_, ?_, fun X t hu => ?_⟩
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, _, rfl⟩
        exact x.2
      · rintro _ ⟨x, _, rfl⟩
        exact x.2
    · intro y hy
      let x : B.toScheme := ⟨y, hy⟩
      have hx : x ∈ O₀ ⊔ O₀' := by rw [a]; trivial
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    have h2 := (memI _ x).1 hx'
    have : x ∈ O₀ ⊓ O₀' := ⟨hx, h2⟩
    rw [b] at this
    exact this
  · have r : Set.range t ⊆ Set.range B.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact natUnit_mem t l hu x
    have hk := IsOpenImmersion.lift_fac B.ι t r
    generalize IsOpenImmersion.lift B.ι t r = k at hk
    subst hk
    have e : (∀ x, (k ≫ B.ι) x ∈ B.ι ''ᵁ O₀) ↔ ∀ x, k x ∈ O₀ :=
      forall_congr' fun x => by simpa using memI O₀ (k x)
    rw [e, c X k]
    have ef : (k ≫ B.ι) ≫ f = (k ≫ f') ≫ (T.p ⁻¹ᵁ U).ι := by
      rw [Category.assoc, Category.assoc, hf']
    have eg : (k ≫ B.ι) ≫ g = (k ≫ g') ≫ (T.p ⁻¹ᵁ U).ι := by
      rw [Category.assoc, Category.assoc, hg']
    rw [ef, eg]
    exact (cancel_mono _).symm

private theorem etale_snd (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (X : Scheme.{0}) (x : X ⟶ Y)
    (hl : IsUnit (l : Γ(X, ⊤))) : Etale (pullback.snd T.p x) := by
  let U := Y.basicOpen (l : Γ(Y, ⊤))
  have het : Etale (T.p ∣_ U) := T.et
  have r : Set.range x ⊆ Set.range U.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact natUnit_mem x l hl u
  have hk := IsOpenImmersion.lift_fac U.ι x r
  generalize IsOpenImmersion.lift U.ι x r = x' at hk
  subst hk
  have sq := (IsPullback.of_hasPullback (T.p ∣_ U) x').paste_horiz (isPullback_morphismRestrict T.p U).flip
  have h1 : Etale (pullback.snd (T.p ∣_ U) x') := inferInstance
  have e : pullback.snd T.p (x' ≫ U.ι) = sq.isoPullback.inv ≫ pullback.snd (T.p ∣_ U) x' := by
    rw [Iso.eq_inv_comp]
    exact sq.isoPullback_hom_snd
  rw [e]
  infer_instance

private theorem sec_agree {Q X : Scheme.{0}} (q : Q ⟶ X) [Etale q] (σ τ : X ⟶ Q) (hσ : σ ≫ q = 𝟙 X) (hτ : τ ≫ q = 𝟙 X)
    (u : X) (h : σ u = τ u) : ∃ V : X.Opens, u ∈ V ∧ V.ι ≫ σ = V.ι ≫ τ := by
  have ho : IsOpenImmersion σ := sec_open q σ hσ
  let V : X.Opens := τ ⁻¹ᵁ σ.opensRange
  refine ⟨V, ⟨u, h⟩, ?_⟩
  have r : Set.range (V.ι ≫ τ) ⊆ Set.range σ := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  have hk := IsOpenImmersion.lift_fac σ (V.ι ≫ τ) r
  generalize IsOpenImmersion.lift σ (V.ι ≫ τ) r = k at hk
  have e : k = V.ι := by
    have := congrArg (· ≫ q) hk
    simp only [Category.assoc, hσ, hτ, Category.comp_id] at this
    exact this
  rw [← hk, e]

private theorem finite_sec (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (K : Type) [Field K] (hK : (l : K) ≠ 0)
    (y : Spec (CommRingCat.of K) ⟶ Y) :
    Finite {z : Spec (CommRingCat.of K) ⟶ T.Z // z ≫ T.p = y} := by
  have hu : IsUnit (l : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have := (IsUnit.mk0 _ hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    simpa using this
  have het := etale_snd l Y T _ y hu
  have hfin : IsFinite T.p := T.fin
  let r := pullback.snd T.p y
  have hr : IsFinite r := inferInstance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hsub : ∀ a b : Spec (CommRingCat.of K), a = b := fun a b => Subsingleton.elim a b
  have hF : Finite (pullback T.p y : Scheme.{0}) := by
    have h0 := r.finite_preimage_singleton pt
    have : r ⁻¹' {pt} = Set.univ := Set.eq_univ_of_forall fun a => hsub _ _
    rw [this] at h0
    exact Set.finite_univ_iff.1 h0
  let F : {z : Spec (CommRingCat.of K) ⟶ T.Z // z ≫ T.p = y} → (pullback T.p y : Scheme.{0}) := fun z =>
    pullback.lift z.1 (𝟙 _) (by rw [z.2, Category.id_comp]) pt
  refine Finite.of_injective F fun a b hab => ?_
  obtain ⟨V, hV, e⟩ := sec_agree r _ _ (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) pt hab
  have hVt : V = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rwa [hsub x pt]
  subst hVt
  have e2 := congrArg (· ≫ pullback.fst T.p y) e
  simp only [Category.assoc, pullback.lift_fst] at e2
  have hiso : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  exact Subtype.ext ((cancel_epi _).1 e2)

private theorem exists_geom (Q : Scheme.{0}) (ζ : Q) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K)
    (g : Spec (CommRingCat.of K) ⟶ Q) (pt : Spec (CommRingCat.of K)), g pt = ζ := by
  let κ := Q.residueField ζ
  let K := AlgebraicClosure κ
  refine ⟨K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ K)) ≫ Q.fromSpecResidueField ζ, IsLocalRing.closedPoint K, ?_⟩
  exact Q.fromSpecResidueField_apply ζ _

private theorem splitOn_of_disj (l : ℕ) (Y : Scheme.{0}) (T : Corr l Y) (X : Scheme.{0}) (x : X ⟶ Y)
    (z : Fin T.d → (X ⟶ T.Z)) (hz : ∀ i, z i ≫ T.p = x) (hl : IsUnit (l : Γ(X, ⊤)))
    (hd : ∀ a b, a ≠ b → ∀ (S : Scheme.{0}) (t : S ⟶ X), t ≫ z a = t ≫ z b → IsEmpty S) :
    SplitOn T.p x z := by
  refine ⟨hz, ?_⟩
  have het := etale_snd l Y T X x hl
  let q := pullback.snd T.p x
  let σ : ∀ i, X ⟶ pullback T.p x := fun i => pullback.lift (z i) (𝟙 X) (by rw [hz i, Category.id_comp])
  have hσq : ∀ i, σ i ≫ q = 𝟙 X := fun i => pullback.lift_snd _ _ _
  have hσf : ∀ i, σ i ≫ pullback.fst T.p x = z i := fun i => pullback.lift_fst _ _ _
  have ho : ∀ i, IsOpenImmersion (σ i) := fun i => sec_open q (σ i) (hσq i)
  have hpts : ∀ i (u : X), q (σ i u) = u := fun i u => by
    have := congrArg (fun k : X ⟶ X => k u) (hσq i)
    simpa using this
  have hdis : _root_.Pairwise (Function.onFun Disjoint fun i => Set.range (σ i)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨u, rfl⟩ ⟨v, e⟩
    have huv : v = u := by
      have := congrArg q e
      rwa [hpts, hpts] at this
    subst huv
    obtain ⟨V, hV, e2⟩ := sec_agree q (σ b) (σ a) (hσq b) (hσq a) v e
    have e3 := congrArg (· ≫ pullback.fst T.p x) e2
    simp only [Category.assoc, hσf] at e3
    exact (hd a b hab V.toScheme V.ι e3.symm).false ⟨v, hV⟩
  have hopen : IsOpenImmersion (Sigma.desc σ) := isOpenImmersion_sigmaDesc _ σ hdis
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ (TopologicalSpace.Opens.ext ?_)
  refine Set.eq_univ_of_forall fun ζ => ?_
  obtain ⟨K, _, _, g, pt, hg⟩ := exists_geom _ ζ
  let e := g ≫ q
  have hK : (l : K) ≠ 0 := by
    have h1 := natUnit_comp e l hl
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    have h3 : IsUnit (l : K) := by simpa using h2
    exact h3.ne_zero
  have hfin := finite_sec l Y T K hK (e ≫ x)
  have hcard := T.deg K hK (e ≫ x)
  let F : Fin T.d → {w : Spec (CommRingCat.of K) ⟶ T.Z // w ≫ T.p = e ≫ x} := fun i =>
    ⟨e ≫ z i, by rw [Category.assoc, hz i]⟩
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    exact (hd a b hne _ e (congrArg Subtype.val hab)).false pt
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard]; simp)
  obtain ⟨i, hi⟩ := hbij.2 ⟨g ≫ pullback.fst T.p x, by
    rw [Category.assoc, pullback.condition, ← Category.assoc]⟩
  have hi' : e ≫ z i = g ≫ pullback.fst T.p x := congrArg Subtype.val hi
  have hgi : g = e ≫ σ i := by
    apply pullback.hom_ext
    · rw [Category.assoc, hσf, hi']
    · rw [Category.assoc]
      change g ≫ q = e ≫ σ i ≫ q
      rw [hσq, Category.comp_id]
  refine ⟨Sigma.ι (fun _ : Fin T.d => X) i (e pt), ?_⟩
  rw [← hg, hgi]
  have : Sigma.ι (fun _ : Fin T.d => X) i ≫ Sigma.desc σ = σ i := Sigma.ι_desc _ _
  simp only [Scheme.Hom.comp_apply]
  rw [← Scheme.Hom.comp_apply, this]

private theorem natUnit_away (l : ℕ) (U : Type) [CommRing U] :
    IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := by
  have h : IsUnit (l : Localization.Away (l : U)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : U)) (l : U)
    simpa using this
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (l : U)))).inv.hom
  simpa using this

private theorem away_inj (l : ℕ) (U : Type) [CommRing U] (h : (l : U) ∈ nonZeroDivisors U) :
    Function.Injective (algebraMap U (Localization.Away (l : U))) :=
  IsLocalization.injective _ (Submonoid.powers_le.2 h)

theorem wEx : WEx := by
  intro l Y J _ T
  let I := Σ j, Fin (T j).d
  let Zi : I → Scheme.{0} := fun i => (T i.1).Z
  let pi : ∀ i, Zi i ⟶ Y := fun i => (T i.1).p
  let P : Scheme.{0} := widePullback Y Zi pi
  let c : ∀ i, P ⟶ Zi i := WidePullback.π pi
  let π₀ : P ⟶ Y := WidePullback.base pi
  have hc : ∀ i, c i ≫ pi i = π₀ := WidePullback.π_arrow pi
  let Q := {q : Σ j, Fin (T j).d × Fin (T j).d // q.2.1 ≠ q.2.2}
  have hE : ∀ q : Q, ∃ O O' : P.Opens, O ⊔ O' = P.basicOpen (l : Γ(P, ⊤)) ∧ O ⊓ O' = ⊥ ∧
      ∀ (X : Scheme.{0}) (t : X ⟶ P), IsUnit (l : Γ(X, ⊤)) →
        ((∀ x, t x ∈ O) ↔ t ≫ c ⟨q.1.1, q.1.2.1⟩ = t ≫ c ⟨q.1.1, q.1.2.2⟩) := fun q =>
    eqLocus l Y (T q.1.1) P (c ⟨q.1.1, q.1.2.1⟩) (c ⟨q.1.1, q.1.2.2⟩)
      ((hc ⟨q.1.1, q.1.2.1⟩).trans (hc ⟨q.1.1, q.1.2.2⟩).symm)
  choose O O' h1 h2 h3 using hE
  let B := P.basicOpen (l : Γ(P, ⊤))
  have hOB : ∀ q, O q ≤ B := fun q => le_sup_left.trans_eq (h1 q)
  have hOB' : ∀ q, O' q ≤ B := fun q => le_sup_right.trans_eq (h1 q)
  let D : P.Opens := ⟨(B : Set P) ∩ ⋂ q, (O' q : Set P), B.2.inter (isOpen_iInter_of_finite fun q => (O' q).2)⟩
  let D' : P.Opens := ⨆ q, O q
  have memD : ∀ x, x ∈ D ↔ x ∈ B ∧ ∀ q, x ∉ O q := by
    intro x
    constructor
    · rintro ⟨hb, hq⟩
      refine ⟨hb, fun q hx => ?_⟩
      have : x ∈ O q ⊓ O' q := ⟨hx, Set.mem_iInter.1 hq q⟩
      rw [h2 q] at this
      exact this
    · rintro ⟨hb, hq⟩
      refine ⟨hb, Set.mem_iInter.2 fun q => ?_⟩
      have : x ∈ O q ⊔ O' q := by rw [h1 q]; exact hb
      exact this.resolve_left (hq q)
  have hDD : D ⊔ D' = B := by
    apply le_antisymm
    · refine sup_le (fun x hx => ((memD x).1 hx).1) (iSup_le hOB)
    · intro x hx
      by_cases h : ∀ q, x ∉ O q
      · exact Or.inl ((memD x).2 ⟨hx, h⟩)
      · push_neg at h
        obtain ⟨q, hq⟩ := h
        exact Or.inr ((le_iSup O q) hq)
  have hDD' : D ⊓ D' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    obtain ⟨q, hq⟩ := (Opens.mem_iSup).1 hx'
    exact ((memD x).1 hx).2 q hq
  obtain ⟨W, ι, vD, hcl, hvD, hWD⟩ := closureOf P (l : Γ(P, ⊤)) D D' hDD hDD'
  refine ⟨⟨W, ι ≫ π₀, fun j i => ι ≫ c ⟨j, i⟩, ?_, ?_, ?_⟩⟩
  · intro j i
    rw [Category.assoc]
    exact congrArg (ι ≫ ·) (hc ⟨j, i⟩)
  · intro X w hu j
    refine splitOn_of_disj l Y (T j) X _ _ (fun i => ?_) hu ?_
    · rw [Category.assoc, Category.assoc]
      exact congrArg (fun k => w ≫ ι ≫ k) (hc ⟨j, i⟩)
    · intro a b hab S t ht
      by_contra hS
      obtain ⟨pt⟩ := not_isEmpty_iff.1 hS
      let q : Q := ⟨⟨j, a, b⟩, hab⟩
      have hu' : IsUnit (l : Γ(S, ⊤)) := natUnit_comp t l hu
      have key := (h3 q S (t ≫ w ≫ ι) hu').2 (by simpa [Category.assoc] using ht) pt
      have hb : ι (w (t pt)) ∈ B := by
        have := natUnit_mem (w ≫ ι) l hu (t pt)
        simpa using this
      have hD := hWD _ hb
      refine ((memD _).1 hD).2 q ?_
      simpa using key
  · intro U _ hl y z hz hsp
    let u : Spec (CommRingCat.of U) ⟶ P := WidePullback.lift y (fun i => z i.1 i.2) (fun i => hz i.1 i.2)
    have hu₀ : u ≫ π₀ = y := WidePullback.lift_base _ _ _ _
    have huc : ∀ i, u ≫ c i = z i.1 i.2 := fun i => WidePullback.lift_π _ _ _ _ _
    let a := awayPt l U
    have hau : IsUnit (l : Γ(Spec (CommRingCat.of (Localization.Away (l : U))), ⊤)) := natUnit_away l U
    have hrange : ∀ x, (a ≫ u) x ∈ D := by
      intro x
      refine (memD _).2 ⟨natUnit_mem _ l hau x, fun q hq => ?_⟩
      let V : (Spec (CommRingCat.of (Localization.Away (l : U)))).Opens := (a ≫ u) ⁻¹ᵁ O q
      have hV : ∀ v, (V.ι ≫ a ≫ u) v ∈ O q := by
        intro v
        exact v.2
      have e := (h3 q V.toScheme (V.ι ≫ a ≫ u) (natUnit_comp V.ι l hau)).1 hV
      have e' : V.ι ≫ a ≫ z q.1.1 q.1.2.1 = V.ι ≫ a ≫ z q.1.1 q.1.2.2 := by
        have e1 := huc ⟨q.1.1, q.1.2.1⟩
        have e2 := huc ⟨q.1.1, q.1.2.2⟩
        simp only [Category.assoc] at e
        rw [e1, e2] at e
        exact e
      have := disj_of_splitOn _ _ _ (hsp q.1.1) _ _ q.2 V.toScheme V.ι (by simpa [Category.assoc] using e')
      exact this.false ⟨x, hq⟩
    have hr : Set.range (a ≫ u) ⊆ Set.range D.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hrange x
    let v₀ := IsOpenImmersion.lift D.ι (a ≫ u) hr
    have hv₀ : v₀ ≫ D.ι = a ≫ u := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w, hw⟩ := liftClosed ι U (Localization.Away (l : U)) (algebraMap U _) (away_inj l U hl) u (v₀ ≫ vD)
      (by rw [Category.assoc, hvD, hv₀])
    refine ⟨w, ⟨?_, fun j i => ?_⟩, ?_⟩
    · rw [← Category.assoc, hw, hu₀]
    · rw [← Category.assoc, hw]
      exact huc ⟨j, i⟩
    · rintro w' ⟨e1, e2⟩
      rw [← cancel_mono ι, hw]
      refine WidePullback.hom_ext pi _ _ (fun i => ?_) ?_
      · have := e2 i.1 i.2
        rw [Category.assoc]
        exact this.trans (huc i).symm
      · rw [Category.assoc]
        exact e1.trans hu₀.symm

end UpperTheory.Ru.crystallineComparison
