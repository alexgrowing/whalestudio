import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGroupQuotientPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.TorusQuotientGlue

set_option backward.isDefEq.respectTransparency false in

theorem exists_glue (Y : Scheme.{0}) (𝒰 : Set Y.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : Y, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : Y, ∃ U : 𝒰, x ∈ U.1) (F : 𝒰 ⥤ Scheme.{0})
    (hF : ∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f))
    (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U) (hs : ∀ U, Surjective (e U))
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      Y.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h)))
    (hsat : ∀ {U V : 𝒰} (f : U ⟶ V) (x : V.1.toScheme) (z : F.obj U), F.map f z = e V x → x.1 ∈ U.1)
    {S : Scheme.{0}} (g : Y ⟶ S) (s : ∀ U, F.obj U ⟶ S) (hs₁ : ∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ s V = s U)
    (hs₂ : ∀ U, e U ≫ s U = U.1.ι ≫ g) :
    ∃ (B : Scheme.{0}) (j : Y ⟶ B) (σ : B ⟶ S) (κ : ∀ U, F.obj U ⟶ B) (_ : ∀ U, IsOpenImmersion (κ U)),
      j ≫ σ = g ∧ (∀ U, U.1.ι ≫ j = e U ≫ κ U) ∧ (∀ U, j ⁻¹ᵁ (κ U).opensRange = U.1) ∧
      ∀ b : B, ∃ U, b ∈ (κ U).opensRange := by
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (Y.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have hnat'' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : Y) (h : x ∈ U.1) (h' : x ∈ V.1),
      F.map f (e U ⟨x, h⟩) = e V ⟨x, h'⟩ := by
    intro U V f x h h'
    rw [hnat']; congr 1; apply Subtype.ext; simp
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨⟨x, hx⟩, rfl⟩ := (e U).surjective x
    have h' : F.map f (e U ⟨x, hx⟩) = F.map g y := h
    rw [hnat'' f x hx (f.le hx)] at h'
    have hxV : x ∈ V.1 := hsat g _ y h'.symm
    obtain ⟨T, hT, hxT, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 x hx hxV
    refine ⟨⟨T, hT⟩, homOfLE h1, homOfLE h2, e ⟨T, hT⟩ ⟨x, hxT⟩, hnat'' _ x hxT hx, ?_⟩
    refine (hnat'' (homOfLE (show (⟨T, hT⟩ : 𝒰) ≤ V from h2)) x hxT hxV).trans ?_
    exact (F.map g).isOpenEmbedding.injective ((hnat'' g x hxV _).trans h')
  have key2 : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : F.obj V),
      colimit.ι F U (e U x) = colimit.ι F V y → x.1 ∈ V.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    exact g.le (hsat f x z h1)
  have hcov : TopologicalSpace.IsOpenCover (fun U : 𝒰 ↦ U.1) :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  let 𝒱 : Y.OpenCover := Y.openCoverOfIsOpenCover (fun U : 𝒰 ↦ U.1) hcov
  let j : Y ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : W.toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (Y.homOfLE h1) (Y.homOfLE h2) ((Y.homOfLE_ι h1).trans (Y.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = Y.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = Y.homOfLE h2 := pullback.lift_snd _ _ _
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
  let c : Cocone F := ⟨S, ⟨s, fun U V f => (hs₁ f).trans (Category.comp_id _).symm⟩⟩
  refine ⟨colimit F, j, colimit.desc F c, colimit.ι F, inferInstance, ?_, hj, fun U => ?_, fun b => ?_⟩
  · refine 𝒱.hom_ext _ _ fun U => ?_
    change U.1.ι ≫ _ = U.1.ι ≫ _
    rw [reassoc_of% (hj U), colimit.ι_desc, hs₂]
  · ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨V, hV⟩ := hc x
      exact key2 ⟨x, hV⟩ y (hy.trans (hj' V ⟨x, hV⟩)).symm
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  · obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    exact ⟨U, x, rfl⟩

open ThickGlue in
set_option backward.isDefEq.respectTransparency false in

theorem exists_scheme (Y : Scheme.{0}) (𝒰 : Set Y.Opens) (hc : ∀ x : Y, ∃ U : 𝒰, x ∈ U.1)
    (𝒜 : Y.Opensᵒᵖ ⥤ CommRingCat.{0}) (p : 𝒜 ⟶ Y.presheaf)
    (hbo : ∀ U ∈ 𝒰, ∀ a : 𝒜.obj (op U), Y.basicOpen ((p.app (op U)).hom a) ∈ 𝒰)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : Y, x ∈ U → x ∈ V → ∃ a : 𝒜.obj (op U),
      x ∈ Y.basicOpen ((p.app (op U)).hom a) ∧ Y.basicOpen ((p.app (op U)).hom a) ≤ V)
    (hsu : ∀ U ∈ 𝒰, Surjective (toSpec p U))
    (hloc : ∀ U ∈ 𝒰, ∀ (a : 𝒜.obj (op U)) (W : Y.Opens) (_ : W = Y.basicOpen ((p.app (op U)).hom a)) (h : W ≤ U),
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)))
    {S : Scheme.{0}} [IsAffine S] (g : Y ⟶ S) (β : ∀ U, Γ(S, ⊤) ⟶ 𝒜.obj (op U))
    (hβ : ∀ (U V : Y.Opens) (h : U ≤ V), β V ≫ 𝒜.map (homOfLE h).op = β U)
    (hβ' : ∀ U, β U ≫ p.app (op U) = g.appLE ⊤ U le_top) :
    ∃ (B : Scheme.{0}) (j : Y ⟶ B) (σ : B ⟶ S), j ≫ σ = g ∧ ∀ b : B, ∃ (V : B.Opens), b ∈ V ∧ IsAffineOpen V ∧
      j ⁻¹ᵁ V ∈ 𝒰 ∧ ∃ φ : Γ(B, V) ≅ 𝒜.obj (op (j ⁻¹ᵁ V)), φ.hom ≫ p.app _ = j.app V := by
  have hnat : ∀ {U V : Y.Opens} (h : U ≤ V) (x : Y) (hx : x ∈ U) (hx' : x ∈ V),
      Spec.map (𝒜.map (homOfLE h).op) (toSpec p U ⟨x, hx⟩) = toSpec p V ⟨x, hx'⟩ := fun {U V} h x hx hx' => by
    refine Eq.trans congr($(toSpec_naturality p h) ⟨x, hx⟩).symm ?_
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subtype.ext (Scheme.homOfLE_apply _ _)
  have hfib : ∀ (V : Y.Opens) (a : 𝒜.obj (op V)) (x : V.toScheme),
      x.1 ∈ Y.basicOpen ((p.app (op V)).hom a) ↔ toSpec p V x ∈ PrimeSpectrum.basicOpen a := fun V a x =>
    (SetLike.ext_iff.1 (Scheme.Opens.toSpecΓ_preimage_basicOpen V ((p.app (op V)).hom a)) x).symm
  have hres : ∀ {U V : Y.Opens} (h : U ≤ V) (a : 𝒜.obj (op V)), Y.basicOpen ((p.app (op V)).hom a) ≤ U →
      Y.basicOpen ((p.app (op V)).hom a) = Y.basicOpen ((p.app (op U)).hom ((𝒜.map (homOfLE h).op).hom a)) :=
    fun {U V} h a hf => by
      have := congr($(p.naturality (homOfLE h).op).hom a)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [this, Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hf).symm
  have hopen : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ h : U ≤ V,
      IsOpenImmersion (Spec.map (𝒜.map (homOfLE h).op)) := by
    intro U hU V hV h
    have := hsu U hU
    apply IsOpenImmersion.of_forall_source_exists
    · intro x y hxy
      obtain ⟨⟨x, hx⟩, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨⟨y, hy⟩, rfl⟩ := (toSpec p U).surjective y
      rw [hnat h x hx (h hx), hnat h y hy (h hy)] at hxy
      obtain ⟨a, hxa, ha⟩ := hbas V hV U hU x (h hx) hx
      have hya : y ∈ Y.basicOpen ((p.app (op V)).hom a) :=
        (hfib V a ⟨y, h hy⟩).2 (hxy ▸ (hfib V a ⟨x, h hx⟩).1 hxa)
      have := hloc V hV a _ rfl (ha.trans h)
      rw [← hnat (ha.trans h) x hxa, ← hnat (ha.trans h) y hya] at hxy
      rw [← hnat ha x hxa, ← hnat ha y hya, (Spec.map _).isOpenEmbedding.injective hxy]
    · intro x
      obtain ⟨⟨x, hx⟩, rfl⟩ := (toSpec p U).surjective x
      obtain ⟨a, hxa, ha⟩ := hbas V hV U hU x (h hx) hx
      refine ⟨_, _, hloc U hU _ _ (hres h a ha) ha, ⟨toSpec p _ ⟨x, hxa⟩, hnat _ _ _ _⟩, ?_⟩
      rw [← Spec.map_comp, ← 𝒜.map_comp]
      exact hloc V hV a _ rfl (ha.trans h)
  obtain ⟨B, j, σ, κ, hκ, h0, h1, h2, h3⟩ := exists_glue Y 𝒰
    (fun U hU V hV x hxU hxV ↦ by
      obtain ⟨a, hxa, ha⟩ := hbas U hU V hV x hxU hxV
      exact ⟨_, hbo U hU a, hxa, Y.basicOpen_le _, ha⟩) hc (specDiagram 𝒰 𝒜)
    (fun {U V} f ↦ hopen _ U.2 _ V.2 f.le) (fun U ↦ toSpec p U.1)
    (fun U ↦ hsu _ U.2) (fun h ↦ toSpec_naturality p h)
    (fun {U V} f x z hz => by
      have := hsu _ U.2
      obtain ⟨⟨y, hy⟩, rfl⟩ := (toSpec p U.1).surjective z
      have e := (hnat f.le y hy (f.le hy)).symm.trans hz
      obtain ⟨a, hya, ha⟩ := hbas _ V.2 _ U.2 y (f.le hy) hy
      exact ha ((hfib _ a x).2 (e ▸ (hfib _ a ⟨y, f.le hy⟩).1 hya)))
    g (fun U => Spec.map (β U.1) ≫ (isAffineOpen_top S).fromSpec)
    (fun {U V} f => by
      change Spec.map _ ≫ _ = _
      rw [← Spec.map_comp_assoc, hβ])
    (fun U => by
      rw [toSpec, Category.assoc, ← Spec.map_comp_assoc, hβ', Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
        IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι])
  refine ⟨B, j, σ, h0, fun b => ?_⟩
  obtain ⟨⟨U, h⟩, hb⟩ := h3 b
  have : IsAffine ((specDiagram 𝒰 𝒜).obj ⟨U, h⟩) := inferInstanceAs (IsAffine (Spec _))
  have hU : j ⁻¹ᵁ (κ ⟨U, h⟩).opensRange = U := h2 ⟨U, h⟩
  refine ⟨_, hb, isAffineOpen_opensRange _, hU.symm ▸ h, ?_⟩
  generalize hV : (κ ⟨U, h⟩).opensRange = V at hU
  subst hU
  have hle : ⊤ ≤ (κ ⟨_, h⟩) ⁻¹ᵁ V := by
    intro x _
    have : κ ⟨_, h⟩ x ∈ (κ ⟨_, h⟩).opensRange := ⟨x, rfl⟩
    rwa [hV] at this
  have hiso : IsIso ((κ ⟨_, h⟩).appLE V ⊤ hle) := by
    have := (κ ⟨_, h⟩).isIso_app V hV.ge
    have : IsIso (homOfLE hle) := homOfLE_isIso_of_eq _ (top_le_iff.mp hle).symm
    rw [Scheme.Hom.appLE]
    infer_instance
  refine ⟨asIso ((κ ⟨_, h⟩).appLE V ⊤ hle) ≪≫ Scheme.ΓSpecIso _, ?_⟩
  have e1 : (j ⁻¹ᵁ V).ι ≫ j = (j ⁻¹ᵁ V).toSpecΓ ≫ Spec.map (p.app _) ≫ κ ⟨_, h⟩ := by
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

open GlobalTheory.UU GlobalTheory.TorusGrading GlobalTheory.TorusQuotientLift GlobalTheory.AffineThickening

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G}

theorem mem_of_act_mem [IsMonHom i] {W : G.left.Opens}
    (hW : (snd (splitTorus S X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ W)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} (hz : z ∈ ((t ≫ i) * g).left ⁻¹ᵁ W) :
    z ∈ g.left ⁻¹ᵁ W := by
  let O := ((t ≫ i) * g).left ⁻¹ᵁ W
  let c : Over.mk (O.ι ≫ Z.hom) ⟶ Z := Over.homMk O.ι rfl
  have h := top_le_act hW (c ≫ t)⁻¹ (g := c ≫ ((t ≫ i) * g)) (fun y _ => y.2)
  rw [GrpObj.inv_comp, MonObj.comp_mul, Category.assoc, inv_mul_cancel_left] at h
  exact h (x := ⟨z, hz⟩) trivial

theorem basicOpen_le_of_sum [Module.Free ℤ X] [Module.Finite ℤ X] [IsMonHom i] {V W : G.left.Opens}
    (hV : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (hW : (snd (splitTorus S X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ W)
    {s : Finset X} {a : X → Γ(G.left, V)} (ha : ∀ χ, IsWt i V (a χ) χ)
    (hs : G.left.basicOpen (∑ χ ∈ s, a χ) ≤ W) {χ : X} (hχ : χ ∈ s) : G.left.basicOpen (a χ) ≤ W := by
  intro y hy
  by_contra hyW
  let Z : Over S := Over.mk (G.left.fromSpecResidueField y ≫ G.hom)
  let g₀ : Z ⟶ G := Over.homMk (G.left.fromSpecResidueField y) rfl
  have hg : ∀ z, g₀.left z = y := fun z => G.left.fromSpecResidueField_apply y z
  have h₀ : ⊤ ≤ g₀.left ⁻¹ᵁ V := fun z _ => by
    change g₀.left z ∈ V
    rw [hg]; exact G.left.basicOpen_le _ hy
  have hr : IsReduced (splitTorus S X ⊗ Z).left := by
    have : IsReduced Z.left := inferInstanceAs (IsReduced (Spec _))
    have : Smooth (snd (splitTorus S X) Z).left :=
      smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) (H1.torus_dim S X).smooth
    exact GlobalTheory.isReduced_of_smooth_of_isReduced (snd (splitTorus S X) Z).left
  have key : (g₀.left.appLE V ⊤ h₀).hom (a χ) = 0 := by
    refine eq_zero_of_sum_chV Z s (fun χ => (g₀.left.appLE V ⊤ h₀).hom (a χ)) ?_ χ hχ
    generalize fst (splitTorus S X) Z = p
    generalize snd (splitTorus S X) Z = q
    have k := top_le_comp_left q h₀
    have : (((p ≫ i) * (q ≫ g₀)).left.appLE V ⊤ (top_le_act hV p k)).hom (∑ χ ∈ s, a χ) = 0 := by
      rw [← basicOpen_eq_bot_iff, eq_bot_iff, Scheme.basicOpen_appLE]
      intro z hz
      have h₁ : (q ≫ g₀).left z ∈ W := mem_of_act_mem hW p (q ≫ g₀) (hs hz.2)
      rw [Over.comp_left, Scheme.Hom.comp_apply, hg] at h₁
      exact hyW h₁
    rw [map_sum] at this
    refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) this
    rw [ha χ _ p (q ≫ g₀) _ k, ← chV_val, val_comp q h₀ k]
  have h₂ := congrArg Z.left.basicOpen key
  rw [Scheme.basicOpen_appLE, Scheme.basicOpen_zero] at h₂
  obtain ⟨z⟩ : Nonempty Z.left := inferInstanceAs (Nonempty (Spec _))
  exact h₂.le (x := z) ⟨trivial, by
    change g₀.left z ∈ G.left.basicOpen (a χ)
    rw [hg]; exact hy⟩

theorem exists_invariant [Module.Free ℤ X] [Module.Finite ℤ X] [hi : IsMonHom i] {V W : G.left.Opens}
    (hV : GoodOpen i V)
    (hW : (snd (splitTorus S X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ W)
    {x : G.left} (hxV : x ∈ V) (hxW : x ∈ W) :
    ∃ a : wtZero i V, x ∈ G.left.basicOpen a.1 ∧ G.left.basicOpen a.1 ≤ W := by
  obtain ⟨h₁, h₂, u, hu⟩ := hV
  obtain ⟨f, hf, hx⟩ := h₁.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxV
  obtain ⟨d, hd, rfl⟩ := (functions_graded_by_weights S G X i hi V h₁ h₂).1 f
  have hx' := (G.left.mem_basicOpen _ x hxV).1 hx
  rw [Finsupp.sum, map_sum] at hx'
  obtain ⟨χ, hχ, h⟩ := IsLocalRing.exists_of_isUnit_sum hx'
  have hw : IsWt i V (d χ * ((u (Multiplicative.ofAdd χ))⁻¹).val) 0 := by
    simpa only [add_neg_cancel] using (hd χ).mul (IsWt.inv (hu χ))
  have e : G.left.basicOpen (d χ * ((u (Multiplicative.ofAdd χ))⁻¹).val) = G.left.basicOpen (d χ) := by
    rw [Scheme.basicOpen_mul, G.left.basicOpen_of_isUnit (Units.isUnit _), inf_eq_left]
    exact G.left.basicOpen_le _
  exact ⟨⟨_, hw⟩, e.ge ((G.left.mem_basicOpen _ x hxV).2 h), e.le.trans (basicOpen_le_of_sum h₂ hW hd hf hχ)⟩

theorem goodOpen_basicOpen {V : G.left.Opens} (hV : GoodOpen i V) {a : Γ(G.left, V)} (ha : IsWt i V a 0) :
    GoodOpen i (G.left.basicOpen a) := by
  obtain ⟨h₁, h₂, u, hu⟩ := hV
  refine ⟨h₁.basicOpen a, ?_, (Units.map (AffineThickening.rs (G.left.basicOpen_le a)).toMonoidHom).comp u,
    fun χ => IsWt.res (hu χ) _⟩
  let U := (snd (splitTorus S X) G).left ⁻¹ᵁ G.left.basicOpen a
  let c : Over.mk (U.ι ≫ (splitTorus S X ⊗ G).hom) ⟶ splitTorus S X ⊗ G := Over.homMk U.ι rfl
  have h : ⊤ ≤ (c ≫ snd _ _).left ⁻¹ᵁ G.left.basicOpen a := fun y _ => y.2
  have k := h.trans ((c ≫ snd _ _).left.preimage_mono (G.left.basicOpen_le a))
  have e := congrArg (Scheme.basicOpen _) (ha _ (c ≫ fst _ _) (c ≫ snd _ _) (top_le_act h₂ _ k) k)
  rw [← chV_val, chV_zero, Units.val_one, _root_.one_mul, Scheme.basicOpen_appLE, Scheme.basicOpen_appLE] at e
  have h' := ((le_inf le_rfl h).trans e.ge).trans inf_le_right
  rw [Category.assoc, ← MonObj.comp_mul] at h'
  exact fun y hy => h' (x := ⟨y, hy⟩) trivial

def invPresheaf (i : splitTorus S X ⟶ G) : G.left.Opensᵒᵖ ⥤ CommRingCat.{0} :=
  subPresheaf (wtZero i) (fun _ _ h _ ha => IsWt.res ha h) id monotone_id

def invIncl (i : splitTorus S X ⟶ G) : invPresheaf i ⟶ G.left.presheaf where
  app U := CommRingCat.ofHom (wtZero i U.unop).subtype
  naturality _ _ _ := rfl

theorem graded_of_goodOpen [hi : IsMonHom i] {V : G.left.Opens} (hV : GoodOpen i V) : Graded i V :=
  functions_graded_by_weights S G X i hi V hV.1 hV.2.1

theorem surjective_toSpec [IsMonHom i] {U : G.left.Opens} (hU : GoodOpen i U) :
    Surjective (ThickGlue.toSpec (invIncl i) U) := by
  have h : Function.Surjective (PrimeSpectrum.comap (wtZero i U).subtype) := fun x => by
    refine (PrimeSpectrum.mem_range_comap_iff (wtZero i U).subtype (p := x)).2
      (le_antisymm (fun a ha => ?_) Ideal.le_comap_map)
    have := (graded_of_goodOpen hU).mem_map (A := wtZero i U) x.asIdeal (RingHom.id _) a ha
    rwa [Ideal.map_id] at this
  have : Surjective (Spec.map ((invIncl i).app (op U))) := ⟨h⟩
  rw [ThickGlue.toSpec, ← hU.1.isoSpec_hom]
  infer_instance

theorem isOpenImmersion_basicOpen [IsMonHom i] {U : G.left.Opens} (hU : GoodOpen i U) (a : wtZero i U)
    (W : G.left.Opens) (e : W = G.left.basicOpen a.1) (h : W ≤ U) :
    IsOpenImmersion (Spec.map ((invPresheaf i).map (homOfLE h).op)) := by
  have hW : GoodOpen i W := by
    rw [e]
    exact goodOpen_basicOpen hU a.2
  have key : ∀ {R T : Type} [CommRing R] [CommRing T] (f : R →+* T) (r : R),
      (letI := f.toAlgebra; IsLocalization.Away r T) → IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) :=
    fun {R T} _ _ f r hr => by
      letI := f.toAlgebra
      exact IsOpenImmersion.of_isLocalization (S := T) r
  exact key _ a ((graded_of_goodOpen hU).isLocalization hU.1 a W h e (graded_of_goodOpen hW))

def invConst (i : splitTorus S X ⟶ G) (U : G.left.Opens) : Γ(S, ⊤) ⟶ (invPresheaf i).obj (op U) :=
  CommRingCat.ofHom (R := Γ(S, ⊤)) (S := wtZero i U) ((G.hom.appLE ⊤ U le_top).hom.codRestrict _ fun c =>
    isWt_appLE_of_invariant G.hom (fun Z t g => by rw [Over.w, Over.w]) ⊤ le_top c)

theorem invConst_map (U V : G.left.Opens) (h : U ≤ V) :
    invConst i V ≫ (invPresheaf i).map (homOfLE h).op = invConst i U :=
  CommRingCat.hom_ext (RingHom.ext fun c =>
    Subtype.ext congr($(G.hom.appLE_map (U := ⊤) le_top (homOfLE h).op).hom c))

theorem exists_quotient [IsAffine S] [Module.Free ℤ X] [Module.Finite ℤ X] [hi : IsMonHom i]
    (hc : ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) :
    ∃ (B : Over S) (q : G ⟶ B), ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      GoodOpen i (q.left ⁻¹ᵁ V) ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧
      Function.Injective (q.left.app V).hom := by
  obtain ⟨B, j, σ, h, H⟩ := exists_scheme G.left {V | GoodOpen i V}
    (fun x => by obtain ⟨V, h, h'⟩ := hc x; exact ⟨⟨V, h'⟩, h⟩) (invPresheaf i) (invIncl i)
    (fun U hU a => goodOpen_basicOpen hU a.2)
    (fun U hU V hV x hx hx' => exists_invariant hU hV.2.1 hx hx')
    (fun U hU => surjective_toSpec hU) (fun U hU => isOpenImmersion_basicOpen hU)
    G.hom (invConst i) invConst_map (fun U => rfl)
  refine ⟨Over.mk σ, Over.homMk j h, fun b => ?_⟩
  obtain ⟨V, hb, hV, hg, φ, hφ⟩ := H b
  have hb' := ConcreteCategory.bijective_of_isIso φ.hom
  have e : ∀ c, (j.app V).hom c = (show wtZero i (j ⁻¹ᵁ V) from φ.hom.hom c).1 := fun c => congr($(hφ).hom c).symm
  refine ⟨V, hb, hV, hg, ?_⟩
  change (∀ a : Γ(G.left, j ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (j.app V).hom c = a) ∧ Function.Injective (j.app V).hom
  refine ⟨fun a => ⟨fun ha => ?_, ?_⟩, fun c c' hc => hb'.1 (Subtype.ext ((e c).symm.trans (hc.trans (e c'))))⟩
  · obtain ⟨c, hc⟩ := hb'.2 (⟨a, ha⟩ : wtZero i _)
    exact ⟨c, (e c).trans (congrArg Subtype.val hc)⟩
  · rintro ⟨c, rfl⟩
    rw [e]
    exact (φ.hom.hom c).2

theorem isSeparated_of_unit (B : Over S) [GrpObj B] [IsClosedImmersion (η[B]).left] : IsSeparated B.hom := by
  have h : IsPullback (lift (𝟙 B) (𝟙 B)) (toUnit B) ((fst B B)⁻¹ * snd B B) η[B] := by
    refine IsPullback.of_isLimit' ⟨by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, inv_mul_cancel]; rfl⟩
      (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst _ _) (fun s => ?_) (fun s => toUnit_unique _ _)
        (fun s m h₁ _ => by rw [← h₁, Category.assoc, lift_fst, Category.comp_id]))
    have e := s.condition
    rw [MonObj.comp_mul, GrpObj.comp_inv, toUnit_unique s.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at e
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using e
  have h' : IsClosedImmersion (lift (𝟙 B) (𝟙 B)).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (h.map (Over.forget S)).flip ‹_›
  exact ⟨h'⟩

theorem geometricallyConnected_of_comp {Y Z : Scheme.{0}} (p : Y ⟶ Z) (f : Z ⟶ S)
    [Surjective p] [h : GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : ConnectedSpace ↥(pullback p a) :=
    h.geometrically_connectedSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact (pullback.snd p a).surjective.connectedSpace (pullback.snd p a).continuous

theorem main : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) → ∃ (B : Over (Sp k)) (_ : GrpObj B) (q : G ⟶ B), IsQuot i q ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  intro k _ G _ ⟨hcomm, hsm, _, hqc, hgc⟩ X _ _ _ i hi hc
  obtain ⟨B, q, H⟩ := exists_quotient hc
  have haff : IsAffineHom q.left := isAffineHom_of_forall_exists_isAffineOpen _ fun b => by
    obtain ⟨V, hb, hV, hg, -⟩ := H b
    exact ⟨V, hb, hV, hg.1⟩
  obtain ⟨hm, hf, hs, hsB, hfib⟩ := GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B i q hi haff fun b => by
    obtain ⟨V, hb, hV, hg, h₁, h₂⟩ := H b
    exact ⟨V, hb, hV, h₁, h₂, hg.2⟩
  obtain ⟨_, hcB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G _ B i q hi hm hf hs inferInstance hfib
  have hsB := hsB hsm
  have hw : q.left ≫ B.hom = G.hom := Over.w q
  have : IsClosedImmersion (η[B]).left := isClosedImmersion_of_comp_eq_id (Y := Sp k) B.hom _ (Over.w _)
  have hgB : GeometricallyConnected B.hom := by
    have : GeometricallyConnected (q.left ≫ B.hom) := hw ▸ hgc
    exact geometricallyConnected_of_comp q.left B.hom
  have hqB : QuasiCompact B.hom := by
    have : CompactSpace G.left := (quasiCompact_iff_compactSpace G.hom).1 hqc
    have : CompactSpace B.left := q.left.surjective.compactSpace q.left.continuous
    exact (quasiCompact_iff_compactSpace B.hom).2 this
  refine ⟨B, _, q, ⟨hi, hq, hf, hs, haff, hker, hcB, hsB, isSeparated_of_unit B, hqB, hgB⟩, fun g dG => ?_⟩
  have : ConnectedSpace B.left := GroupConn.connectedSpace_of_section B.hom (η[B]).left (Over.w _)
  obtain ⟨y⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨a, dB⟩ := exists_dim_of_preconnected B.hom (eSec B y)
  refine ⟨a, dB, ?_⟩
  have : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback i q hker).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) (H1.torus_dim _ X).smooth
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hker.map (Over.forget _)) d₁ (H1.torus_dim _ X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + a) (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

end GlobalTheory.TorusQuotientGlue
end
