import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThickGlue

set_option backward.isDefEq.respectTransparency false in

theorem exists_glue (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ (W : B₀.Opens) (x : B₀), x ∈ U → x ∈ W → ∃ V ∈ 𝒰, x ∈ V ∧ V ≤ U ∧ V ≤ W)
    (hcov : sSup 𝒰 = ⊤) (F : 𝒰 ⥤ Scheme.{0})
    (hF : ∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f))
    (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U)
    (he : ∀ U, IsClosedImmersion (e U)) (hs : ∀ U, Surjective (e U))
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j)
      (κ : ∀ U, F.obj U ⟶ B) (_ : ∀ U, IsOpenImmersion (κ U)),
      (∀ U, U.1.ι ≫ j = e U ≫ κ U) ∧ (∀ U, j ⁻¹ᵁ (κ U).opensRange = U.1) ∧
      ∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ κ V = κ U := by
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := (e U).surjective x
    obtain ⟨y, rfl⟩ := (e V).surjective y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    have h'' := congrArg Subtype.val (hinj _ h')
    exact key x y (by simpa using h'')
  have key2 : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hc : ∀ x : B₀, ∃ U : 𝒰, x ∈ U.1 := by
    intro x
    have : x ∈ sSup 𝒰 := by rw [hcov]; trivial
    obtain ⟨U, hU, hx⟩ := TopologicalSpace.Opens.mem_sSup.mp this
    exact ⟨⟨U, hU⟩, hx⟩
  let 𝒱 : B₀.OpenCover := B₀.openCoverOfIsOpenCover (fun U : 𝒰 ↦ U.1) (by
    rw [TopologicalSpace.IsOpenCover, ← hcov, sSup_eq_iSup'])
  let j : B₀ ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : W.toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (B₀.homOfLE h1) (B₀.homOfLE h2) ((B₀.homOfLE_ι h1).trans (B₀.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = B₀.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = B₀.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f U) (𝒱.f V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2, reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) h1),
        reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) h2), colimit.w, colimit.w])
  have hj : ∀ U : 𝒰, U.1.ι ≫ j = e U ≫ colimit.ι F U := fun U ↦ 𝒱.ι_glueMorphisms _ _ U
  have hj' : ∀ (U : 𝒰) (x : U.1.toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U, j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV⟩ := hc x
      have := key2 y ⟨x, hV⟩ (hy.trans (hj' V ⟨x, hV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨colimit F, j, ?_, ⟨?_⟩, colimit.ι F, inferInstance, hj, hpre, fun f ↦ colimit.w F f⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) U.1.ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩

noncomputable def specDiagram {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens)
    (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) : 𝒰 ⥤ Scheme.{0} where
  obj U := Spec (𝒜.obj (Opposite.op U.1))
  map {U V} f := Spec.map (𝒜.map (homOfLE (show U.1 ≤ V.1 from f.le)).op)
  map_id U := by
    rw [← Spec.map_id, ← 𝒜.map_id]; rfl
  map_comp f g := by
    rw [← Spec.map_comp, ← 𝒜.map_comp]; rfl

noncomputable def toSpec {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) (U : B₀.Opens) : U.toScheme ⟶ Spec (𝒜.obj (Opposite.op U)) :=
  U.toSpecΓ ≫ Spec.map (p.app (Opposite.op U))

theorem toSpec_naturality {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U V : B₀.Opens} (h : U ≤ V) :
    B₀.homOfLE h ≫ toSpec p V = toSpec p U ≫ Spec.map (𝒜.map (homOfLE h).op) := by
  simp only [toSpec, Category.assoc]
  rw [← Spec.map_comp, p.naturality, Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]

theorem isClosedImmersion_toSpec {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U : B₀.Opens} (hU : IsAffineOpen U)
    (h : Function.Surjective (p.app (Opposite.op U)).hom) : IsClosedImmersion (toSpec p U) := by
  have := IsClosedImmersion.spec_of_surjective _ h
  rw [toSpec, ← hU.isoSpec_hom]
  infer_instance

theorem surjective_toSpec {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U : B₀.Opens} (hU : IsAffineOpen U)
    (h : Function.Surjective (p.app (Opposite.op U)).hom)
    (h' : IsNilpotent (RingHom.ker (p.app (Opposite.op U)).hom)) : Surjective (toSpec p U) := by
  have : Surjective (Spec.map (p.app (Opposite.op U))) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap (p.app (Opposite.op U)).hom)
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ h,
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rwa [hn] at this
  rw [toSpec, ← hU.isoSpec_hom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in

theorem exists_scheme_of_thickenings : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → (∀ U ∈ 𝒰, ∀ f : Γ(B₀, U), B₀.basicOpen f ∈ 𝒰) → sSup 𝒰 = ⊤ → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (Opposite.op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (Opposite.op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (Opposite.op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (Opposite.op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (Opposite.op (B₀.basicOpen ((π.app (Opposite.op U)).hom a))))) → ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j) (φ : ∀ V : B.Opens, j ⁻¹ᵁ V ∈ 𝒰 → (Γ(B, V) ≅ 𝒜.obj (Opposite.op (j ⁻¹ᵁ V)))), (∀ V h, IsAffineOpen V ∧ (φ V h).hom ≫ π.app _ = j.app V) ∧ ∀ V V' h h' (hle : V' ≤ V), B.presheaf.map (homOfLE hle).op ≫ (φ V' h').hom = (φ V h).hom ≫ 𝒜.map (homOfLE (Scheme.Hom.preimage_mono j hle)).op := by
  intro B₀ 𝒰 haff hbo hcov 𝒜 p hp hloc
  have hloc' : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (Opposite.op U)) (W : B₀.Opens)
      (_ : W = B₀.basicOpen ((p.app (Opposite.op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    rintro U hU a W rfl h
    letI := (𝒜.map (homOfLE h).op).hom.toAlgebra
    haveI := hloc U hU a
    exact IsOpenImmersion.of_isLocalization
      (S := 𝒜.obj (Opposite.op (B₀.basicOpen ((p.app (Opposite.op U)).hom a)))) a
  have hci : ∀ U ∈ 𝒰, IsClosedImmersion (toSpec p U) := fun U hU ↦
    isClosedImmersion_toSpec p (haff U hU) (hp U hU).1
  have hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U) := fun U hU ↦
    surjective_toSpec p (haff U hU) (hp U hU).1 (hp U hU).2
  have hnat : ∀ {U V : B₀.Opens} (h : U ≤ V) (x : U.toScheme),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U x) = toSpec p V (B₀.homOfLE h x) :=
    fun h x ↦ congr($(toSpec_naturality p h) x).symm
  have hopen : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V,
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    intro U hU V hV h
    have := hci V hV
    have := hsu U hU
    apply IsOpenImmersion.of_forall_source_exists
    · intro x y hxy
      obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨y, rfl⟩ := (toSpec p U).surjective y
      rw [hnat, hnat] at hxy
      rw [(B₀.homOfLE h).isOpenEmbedding.injective
        ((toSpec p V).isClosedEmbedding.injective hxy)]
    · intro x
      obtain ⟨x, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨f, hf, hxf⟩ := (haff V hV).exists_basicOpen_le (V := U) ⟨x.1, x.2⟩ (h x.2)
      obtain ⟨a, rfl⟩ := (hp V hV).1 f
      have h1 := hloc' U hU ((𝒜.map (homOfLE h).op).hom a) _ (by
        have := congr($(p.naturality (homOfLE h).op).hom a)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        rw [this, Scheme.basicOpen_res]
        exact (inf_eq_right.mpr hf).symm) hf
      refine ⟨_, _, h1, ⟨toSpec p _ ⟨x.1, hxf⟩, ?_⟩, ?_⟩
      · rw [hnat]
        congr 1
        exact Subtype.ext (Scheme.homOfLE_apply _ _)
      · rw [← Spec.map_comp, ← 𝒜.map_comp]
        exact hloc' V hV a _ rfl (hf.trans h)
  obtain ⟨B, j, hj1, hj2, κ, hκ, h1, h2, h3⟩ := exists_glue B₀ 𝒰
    (fun U hU W x hxU hxW ↦ by
      obtain ⟨f, hf, hxf⟩ := (haff U hU).exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
      exact ⟨_, hbo U hU f, hxf, B₀.basicOpen_le f, hf⟩) hcov (specDiagram 𝒰 𝒜)
    (fun {U V} f ↦ hopen _ U.2 _ V.2 f.le) (fun U ↦ toSpec p U.1) (fun U ↦ hci _ U.2)
    (fun U ↦ hsu _ U.2) (fun h ↦ toSpec_naturality p h)
  have hV : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), (κ ⟨_, h⟩).opensRange = V := by
    intro V h
    ext b
    obtain ⟨b, rfl⟩ := j.surjective b
    exact SetLike.ext_iff.mp (h2 ⟨_, h⟩) b
  have hle : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), ⊤ ≤ (κ ⟨_, h⟩) ⁻¹ᵁ V := by
    intro V h x _
    have : κ ⟨_, h⟩ x ∈ (κ ⟨_, h⟩).opensRange := ⟨x, rfl⟩
    rwa [hV V h] at this
  have hiso : ∀ (V : B.Opens) (h : j ⁻¹ᵁ V ∈ 𝒰), IsIso ((κ ⟨_, h⟩).appLE V ⊤ (hle V h)) := by
    intro V h
    have := (κ ⟨_, h⟩).isIso_app V (hV V h).ge
    have : IsIso (homOfLE (hle V h)) := homOfLE_isIso_of_eq _ (top_le_iff.mp (hle V h)).symm
    rw [Scheme.Hom.appLE]
    infer_instance
  refine ⟨B, j, hj1, hj2, fun V h ↦ asIso ((κ ⟨_, h⟩).appLE V ⊤ (hle V h)) ≪≫
    Scheme.ΓSpecIso _, fun V h ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [← hV V h]
    have : IsAffine ((specDiagram 𝒰 𝒜).obj ⟨_, h⟩) := inferInstanceAs (IsAffine (Spec _))
    exact isAffineOpen_opensRange _
  · have e1 : (j ⁻¹ᵁ V).ι ≫ j = (j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩ := by
      simpa [toSpec] using h1 ⟨_, h⟩
    have hle' : ⊤ ≤ ((j ⁻¹ᵁ V).ι ≫ j) ⁻¹ᵁ V := fun x _ ↦ x.2
    have e2 : ((j ⁻¹ᵁ V).ι ≫ j).appLE V ⊤ hle' =
      ((j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩).appLE V ⊤ (e1 ▸ hle') := by
      congr 1
    rw [← cancel_mono (j ⁻¹ᵁ V).topIso.inv]
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
    refine Eq.trans ?_ (e2.symm.trans ?_)
    · simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    · rw [← Scheme.Hom.appLE_comp_appLE (j ⁻¹ᵁ V).ι j V (j ⁻¹ᵁ V) ⊤ le_rfl (fun x _ ↦ x.2),
        ← Scheme.Hom.app_eq_appLE]
      congr 1
      simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
      congr 1
  · intro V V' h h' hVV
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    have e1 := h3 (U := ⟨_, h'⟩) (V := ⟨_, h⟩) (homOfLE (Scheme.Hom.preimage_mono j hVV))
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.map_appLE_assoc, ← Category.assoc]
    congr 1
    simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact e1.symm

end GlobalTheory.ThickGlue
