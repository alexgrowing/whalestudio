import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientGluing

variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}

theorem isOpenImmersion_desc {T T' Y Y' : Scheme.{0}} {σ : G →* Aut T} {σ' : G →* Aut T'}
    {q : T ⟶ Y} {q' : T' ⟶ Y'} (h : IsAffineQuotient σ q) (h' : IsAffineQuotient σ' q')
    (m : T ⟶ T') [IsOpenImmersion m] (hm : ∀ g, (σ g).hom ≫ m = m ≫ (σ' g).hom)
    (k : Y ⟶ Y') (hk : q ≫ k = m ≫ q') : IsOpenImmersion k := by
  obtain ⟨W, hW⟩ := h'.exists_preimage_eq (U := m.opensRange) (fun g ↦ by
    rintro _ ⟨x, rfl⟩
    exact ⟨(σ g).hom x, congr($(hm g) x)⟩)
  have hr : Set.range (m ≫ q') ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    have : m x ∈ q' ⁻¹ᵁ W := hW ▸ ⟨x, rfl⟩
    exact ⟨⟨q' (m x), this⟩, rfl⟩
  let l : T ⟶ W := IsOpenImmersion.lift W.ι (m ≫ q') hr
  have hl : l ≫ W.ι = m ≫ q' := IsOpenImmersion.lift_fac _ _ _
  have H : IsPullback l m W.ι q' :=
    IsOpenImmersion.isPullback _ _ _ _ hl.symm (by rw [Scheme.Opens.opensRange_ι, hW])
  have hq : IsAffineQuotient σ l := h'.of_isPullback H.flip hm fun g ↦ by
    rw [← cancel_mono W.ι, Category.assoc, hl, reassoc_of% hm, h'.comp_eq]
  have : k = (h.uniqueIso hq).hom ≫ W.ι := h.hom_ext (by simp [hk, hl])
  rw [this]
  infer_instance

omit [Finite G] in

theorem app_of_chart {T Y Y' : Scheme.{0}} {ρ : G →* Aut X} {σ : G →* Aut T}
    {q : T ⟶ Y'} (h : IsAffineQuotient σ q) (π : X ⟶ Y) (i : T ⟶ X) [IsOpenImmersion i]
    (hi : ∀ g, (σ g).hom ≫ i = i ≫ (ρ g).hom) (κ : Y' ⟶ Y) [IsOpenImmersion κ]
    (hκ : i ≫ π = q ≫ κ) (W : Y.Opens) (hW : W ≤ κ.opensRange) (hW' : π ⁻¹ᵁ W ≤ i.opensRange) :
    Function.Injective (π.app W) ∧
      ∀ s : Γ(X, π ⁻¹ᵁ W), IsInvariantSection ρ _ s → s ∈ Set.range (π.app W) := by
  have e : q ⁻¹ᵁ κ ⁻¹ᵁ W = i ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hκ]
  have h1 : IsIso (κ.app W) := κ.isIso_app W hW
  have h2 : IsIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le) := by
    have := i.isIso_app _ hW'
    have : IsIso (homOfLE e.le) := homOfLE_isIso_of_eq _ e
    rw [Scheme.Hom.appLE]
    infer_instance
  have sq : π.app W ≫ i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le = κ.app W ≫ q.app _ := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, hκ]
  have sq' (r : Γ(Y, W)) : i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le (π.app W r) =
      q.app _ (κ.app W r) := by
    rw [← CommRingCat.comp_apply, sq, CommRingCat.comp_apply]
  have b1 := ConcreteCategory.bijective_of_isIso (κ.app W)
  have b2 := ConcreteCategory.bijective_of_isIso (i.appLE (π ⁻¹ᵁ W) (q ⁻¹ᵁ κ ⁻¹ᵁ W) e.le)
  refine ⟨fun a b hab ↦ b1.1 (h.app_injective _ ?_), fun s hs ↦ ?_⟩
  · rw [← sq', ← sq', hab]
  · obtain ⟨t, ht⟩ := h.mem_range_app (κ ⁻¹ᵁ W) _ (hs.appLE i hi (h.preimage_le _) e.le)
    obtain ⟨r, rfl⟩ := b1.2 t
    exact ⟨r, b2.1 ((sq' r).trans ht)⟩

set_option backward.isDefEq.respectTransparency false in

theorem exists_of_charts (ρ : G →* Aut X) (𝒰 : Set X.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U : 𝒰, x ∈ U.1)
    (T : 𝒰 → Scheme.{0}) (i : ∀ U, T U ⟶ X) [∀ U, IsOpenImmersion (i U)]
    (hr : ∀ U, (i U).opensRange = U.1) (haff : ∀ U : 𝒰, IsAffineOpen U.1)
    (σ : ∀ U, G →* Aut (T U)) (hσ : ∀ U g, (σ U g).hom ≫ i U = i U ≫ (ρ g).hom)
    (Y : 𝒰 → Scheme.{0}) [∀ U, IsAffine (Y U)] (q : ∀ U, T U ⟶ Y U)
    (hq : ∀ U, IsAffineQuotient (σ U) (q U)) :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  have hmem (U : 𝒰) (x : T U) : i U x ∈ U.1 := hr U ▸ ⟨x, rfl⟩
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, i U y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective (i U) := (i U).isOpenEmbedding.injective
  have hσ' (U : 𝒰) (g : G) (x : T U) : i U ((σ U g).hom x) = (ρ g).hom (i U x) :=
    congr($(hσ U g) x)
  have hqσ (U : 𝒰) (g : G) (x : T U) : q U ((σ U g).hom x) = q U x :=
    congr($((hq U).comp_eq g) x)
  let m {U V : 𝒰} (h : U.1 ≤ V.1) : T U ⟶ T V := IsOpenImmersion.lift (i V) (i U) (by
    rintro _ ⟨x, rfl⟩
    exact hex V _ (h (hmem U x)))
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : m h ≫ i V = i U := IsOpenImmersion.lift_fac _ _ _
  clear_value m
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : T U) : i V (m h x) = i U x := congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (m h) := by
    have : IsOpenImmersion (m h ≫ i V) := by rw [hm]; infer_instance
    exact .of_comp _ (i V)
  have hmσ {U V : 𝒰} (h : U.1 ≤ V.1) (g : G) : (σ U g).hom ≫ m h = m h ≫ (σ V g).hom := by
    rw [← cancel_mono (i V), Category.assoc, Category.assoc, hm, hσ, hσ, reassoc_of% hm]
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := (hq U).desc (m (show U.1 ≤ V.1 from f.le) ≫ q V) fun g ↦ by
        rw [reassoc_of% hmσ, (hq V).comp_eq]
      map_id U := (hq U).hom_ext (by
        have : m (le_refl U.1) = 𝟙 _ := by rw [← cancel_mono (i U), hm, Category.id_comp]
        rw [IsAffineQuotient.comp_desc, this, Category.id_comp, Category.comp_id])
      map_comp {U V W} f g := (hq U).hom_ext (by
        have : m (show U.1 ≤ W.1 from (f ≫ g).le) =
            m (show U.1 ≤ V.1 from f.le) ≫ m (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono (i W), Category.assoc, hm, hm, hm]
        rw [IsAffineQuotient.comp_desc, IsAffineQuotient.comp_desc_assoc, Category.assoc,
          IsAffineQuotient.comp_desc, this, Category.assoc]) }
  let e (U : 𝒰) : T U ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) : e U ≫ F.map f = m (show U.1 ≤ V.1 from f.le) ≫ e V :=
    (hq U).comp_desc _ fun g ↦ by rw [reassoc_of% hmσ, (hq V).comp_eq]
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : T U) :
      F.map f (e U x) = e V (m (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    have := hmo (show U.1 ≤ V.1 from f.le)
    isOpenImmersion_desc (hq U) (hq V) _ (hmσ _) _ (hnat f)
  have hsurj (U : 𝒰) : Function.Surjective (e U) := (hq U).surjective.surj
  have hfib (U : 𝒰) (x y : T U) (h : e U x = e U y) : ∃ g, (ρ g).hom (i U x) = i U y := by
    obtain ⟨g, rfl⟩ := ((hq U).apply_eq_iff x y).mp h
    exact ⟨g, (hσ' U g x).symm⟩
  have key {U V : 𝒰} (x : T U) (y : T V) (h : i U x = i V y) :
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U x) (h ▸ hmem V y)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ z, ?_, ?_⟩
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz]
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz, h]
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := hsurj U x
    obtain ⟨y, rfl⟩ := hsurj V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    obtain ⟨k, hk⟩ := hfib _ _ _ h'
    rw [hm', hm', ← hσ'] at hk
    have := key _ _ hk
    rwa [show e U ((σ U k).hom x) = e U x from hqσ U k x] at this
  have key2 {U V : 𝒰} (x : T U) (y : T V)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : i V y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj W z
    rw [hnat'] at h2
    obtain ⟨k, hk⟩ := hfib _ _ _ h2
    rw [hm', ← hσ'] at hk
    exact hk ▸ (show W.1 ≤ U.1 from f.le) (hmem W _)
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 T i (fun x ↦ by
    obtain ⟨U, hU⟩ := hc x
    exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : i U (pullback.fst (i U) (i V) x) = i V (pullback.snd (i U) (i V) x) :=
      congr($(pullback.condition (f := i U) (g := i V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : T ⟨W, hW⟩ ⟶ pullback (i U) (i V) :=
      pullback.lift (m h1) (m h2) ((hm h1).trans (hm h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = m h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = m h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst (i U) (i V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm', hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst (i U) (i V) ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd (i U) (i V) ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : i U ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : T U) : j (i U x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, .of_cover (fun g ↦ 𝒱.hom_ext _ _ fun U ↦ ?_) fun y ↦ ?_⟩
  · change i U ≫ _ = i U ≫ _
    have : (σ U g).hom ≫ e U = e U := (hq U).comp_eq g
    rw [← reassoc_of% hσ, hj, reassoc_of% this]
  · obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    have : IsAffine (F.obj U) := inferInstanceAs (IsAffine (Y U))
    refine ⟨(colimit.ι F U).opensRange, isAffineOpen_opensRange _, ⟨x, rfl⟩,
      by rw [hpre]; exact haff U, ?_⟩
    exact app_of_chart (hq U) j (i U) (hσ U) (colimit.ι F U) (hj U) _ le_rfl
      (by rw [hpre, hr])

theorem exists_isAffineQuotient (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  let 𝒰 : Set X.Opens := {U | IsAffineOpen U ∧ ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U}
  refine exists_of_charts ρ 𝒰 (fun U hU V hV x hxU hxV ↦ ?_) (fun x ↦ ?_)
    (fun U ↦ Spec Γ(X, U.1)) (fun U ↦ U.2.1.fromSpec) (fun U ↦ U.2.1.opensRange_fromSpec)
    (fun U ↦ U.2.1)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; specAction G Γ(X, U.1))
    (fun U ↦ specAction_fromSpec ρ U.2.1 U.2.2)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; Spec (.of (FixedPoints.subring Γ(X, U.1) G)))
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2
      Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1))))
    (fun U ↦ ?_)
  · obtain ⟨t, ht, hx, hle⟩ := exists_isInvariantSection_basicOpen_le hU.1 hU.2 hxU V
      (fun g ↦ hV.2 g hxV)
    exact ⟨_, ⟨hU.1.basicOpen t, ht.basicOpen_le⟩, hx, X.basicOpen_le t, hle⟩
  · obtain ⟨V, h1, h2, h3⟩ := exists_stable_isAffineOpen ρ x
    exact ⟨⟨V, h1, h2⟩, h3⟩
  · let := sectionsAction ρ U.1 U.2.2
    exact isAffineQuotient_spec (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1)

end QuotientGluing

theorem exists_quotient_of_finite_group : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) [X.IsSeparated] (ρ : Γ →* Aut X), (∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, (ρ g).hom x ∈ U) → ∃ (X' : Scheme.{0}) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) := by
  intro Γ _ _ X _ ρ h
  have : OrbitsInAffineOpens ρ := ⟨h⟩
  obtain ⟨X', π, hπ⟩ := QuotientGluing.exists_isAffineQuotient ρ
  exact ⟨X', π, hπ.isAffineHom, hπ.comp_eq, fun V ↦ ⟨hπ.app_injective V, fun f hf ↦
    hπ.mem_range_app V f fun g ↦ ⟨hπ.preimage_le V g, hf g _⟩⟩⟩

end GlobalTheory
