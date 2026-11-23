import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationAwayOfFlatLift
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftGlue

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in

theorem exists_glue_desc (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ (W : B₀.Opens) (x : B₀), x ∈ U → x ∈ W → ∃ V ∈ 𝒰, x ∈ V ∧ V ≤ U ∧ V ≤ W)
    (hcov : sSup 𝒰 = ⊤) (F : 𝒰 ⥤ Scheme.{0})
    (hF : ∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f))
    (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U)
    (he : ∀ U, IsClosedImmersion (e U)) (hs : ∀ U, Surjective (e U))
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j)
      (κ : ∀ U, F.obj U ⟶ B) (_ : ∀ U, IsOpenImmersion (κ U)),
      (∀ U, U.1.ι ≫ j = e U ≫ κ U) ∧
      (∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ κ V = κ U) ∧
      ∀ (T : Scheme.{0}) (t : ∀ U, F.obj U ⟶ T), (∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ t V = t U) →
        ∃ s : B ⟶ T, ∀ U, κ U ≫ s = t U := by
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
  refine ⟨colimit F, j, ?_, ⟨?_⟩, colimit.ι F, inferInstance, hj, fun f ↦ colimit.w F f,
    fun T t ht ↦ ⟨colimit.desc F ⟨T, ⟨fun U ↦ t U, fun U V f ↦ (ht f).trans (Category.comp_id _).symm⟩⟩,
      fun U ↦ colimit.ι_desc _ _⟩⟩
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

noncomputable section

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

def diag (S : Sys I π s₀) : X₀.affineOpens ⥤ Scheme.{0} where
  obj U := Sp (S.F.obj (Opposite.op U))
  map f := spMap (mp S.F f.op : S.F.obj _ →+* S.F.obj _)
  map_id U := by
    rw [op_id, ← Spec.map_id]
    congr 1
    ext b
    exact mp_id S.F _ b
  map_comp f g := by
    rw [op_comp, ← Spec.map_comp]
    congr 1
    ext b
    exact mp_comp S.F _ _ b

def emb (S : Sys I π s₀) (U : X₀.affineOpens) : U.1.toScheme ⟶ (diag S).obj U :=
  U.1.toSpecΓ ≫ spMap (S.p (Opposite.op U))

theorem emb_closed (S : Sys I π s₀) (U : X₀.affineOpens) : IsClosedImmersion (emb S U) := by
  have h1 := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (S.p (Opposite.op U))) (S.surj _)
  have hU : IsAffineOpen U.1 := U.2
  have h0 : IsIso U.1.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have key : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsClosedImmersion g],
      IsClosedImmersion (f ≫ g) := fun _ _ ↦ inferInstance
  exact @key _ _ _ _ _ h0 h1

theorem emb_surj (S : Sys I π s₀) (hI : I ^ 2 = 0) (U : X₀.affineOpens) : Surjective (emb S U) := by
  have : Surjective (spMap (S.p (Opposite.op U))) := by
    constructor
    change Function.Surjective (PrimeSpectrum.comap (S.p (Opposite.op U)))
    rw [← Set.range_eq_univ, range_comap_of_surjective _ _ (S.surj _),
      PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro x hx
    refine ⟨2, ?_⟩
    have h2 := Ideal.pow_mem_pow hx 2
    have hk : RingHom.ker (S.p (Opposite.op U)) = I.map (algebraMap R (S.F.obj (Opposite.op U))) :=
      Ideal.ext fun b ↦ (RingHom.mem_ker).trans (S.ker _ b)
    rwa [hk, map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have hU : IsAffineOpen U.1 := U.2
  have h0 : IsIso U.1.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have key : ∀ {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [Surjective g],
      Surjective (f ≫ g) := fun _ _ ↦ inferInstance
  exact @key _ _ _ _ _ h0 this

theorem emb_nat (S : Sys I π s₀) {U V : X₀.affineOpens} (h : U.1 ≤ V.1) :
    X₀.homOfLE h ≫ emb S V = emb S U ≫ (diag S).map (homOfLE (show U ≤ V from h)) := by
  simp only [emb, diag, spMap]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp, Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext b
  exact (S.nat (homOfLE (show U ≤ V from h)).op b).symm

end

noncomputable section

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

theorem emb_apply (S : Sys I π s₀) {U V : X₀.affineOpens} (h : U.1 ≤ V.1) (z : U.1.toScheme) :
    (diag S).map (homOfLE (show U ≤ V from h)) (emb S U z) = emb S V (X₀.homOfLE h z) := by
  rw [← Scheme.Hom.comp_apply, ← emb_nat, Scheme.Hom.comp_apply]

theorem loc_open (S : Sys I π s₀) (hI : I ^ 2 = 0) (V W : X₀.affineOpens) (a : S.F.obj (Opposite.op V))
    (hW : W.1 = X₀.basicOpen (S.p (Opposite.op V) a)) (hle : W ≤ V) :
    IsOpenImmersion ((diag S).map (homOfLE hle)) := by
  obtain ⟨W, hW'⟩ := W
  simp only at hW
  subst hW
  have hV : IsAffineOpen V.1 := V.2
  letI : Algebra (S.F.obj (Opposite.op V)) (S.F.obj (Opposite.op ⟨_, hW'⟩)) :=
    (mp S.F (homOfLE hle).op : S.F.obj (Opposite.op V) →+* S.F.obj (Opposite.op ⟨_, hW'⟩)).toAlgebra
  haveI : IsScalarTower R (S.F.obj (Opposite.op V)) (S.F.obj (Opposite.op ⟨_, hW'⟩)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp S.F (homOfLE hle).op).commutes r).symm
  letI : Algebra (Sec s₀ V.1) (Sec s₀ (X₀.basicOpen (S.p (Opposite.op V) a))) :=
    (Sec.res s₀ (X₀.basicOpen_le (S.p (Opposite.op V) a)) : Sec s₀ V.1 →+* _).toAlgebra
  have hloc : IsLocalization.Away (S.p (Opposite.op V) a) (Sec s₀ (X₀.basicOpen (S.p (Opposite.op V) a))) :=
    hV.isLocalization_basicOpen (S.p (Opposite.op V) a)
  haveI := S.smooth (Opposite.op ⟨_, hW'⟩)
  haveI : IsLocalization.Away a (S.F.obj (Opposite.op ⟨_, hW'⟩)) :=
    GlobalTheory.LiftAway.isLocalization_away_of_flat_lift R _ _ (Sec s₀ V.1) (Sec s₀ (X₀.basicOpen (S.p (Opposite.op V) a))) I hI inferInstance
      (S.p _) (S.p _) (S.surj _) (S.surj _) (S.ker _) (S.ker _) (fun b ↦ S.nat (homOfLE hle).op b) a hloc
  exact IsOpenImmersion.of_isLocalization a

theorem diag_open (S : Sys I π s₀) (hI : I ^ 2 = 0) {U V : X₀.affineOpens} (hle : U.1 ≤ V.1) :
    IsOpenImmersion ((diag S).map (homOfLE (show U ≤ V from hle))) := by
  have hV : IsAffineOpen V.1 := V.2
  haveI := emb_surj S hI U
  haveI := emb_closed S V
  apply IsOpenImmersion.of_forall_source_exists
  · intro x y hxy
    obtain ⟨x, rfl⟩ := (emb S U).surjective x
    obtain ⟨y, rfl⟩ := (emb S U).surjective y
    rw [emb_apply S hle, emb_apply S hle] at hxy
    rw [(X₀.homOfLE hle).isOpenEmbedding.injective ((emb S V).isClosedEmbedding.injective hxy)]
  · intro x
    obtain ⟨x, rfl⟩ := (emb S U).surjective x
    obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le (V := U.1) ⟨x.1, x.2⟩ (hle x.2)
    obtain ⟨a, ha⟩ := S.surj (Opposite.op V) g
    let W : X₀.affineOpens := ⟨X₀.basicOpen g, hV.basicOpen g⟩
    have hWU : W ≤ U := hg
    have hWV : W ≤ V := hWU.trans hle
    have h1 : IsOpenImmersion ((diag S).map (homOfLE hWU)) := by
      refine loc_open S hI U W (mp S.F (homOfLE (show U ≤ V from hle)).op a) ?_ hWU
      have e1 := S.nat (homOfLE (show U ≤ V from hle)).op a
      rw [e1, ha]
      change X₀.basicOpen g = X₀.basicOpen ((X₀.presheaf.map (homOfLE hle).op).hom g)
      rw [Scheme.basicOpen_res]
      exact (inf_eq_right.mpr hg).symm
    have h2 : IsOpenImmersion ((diag S).map (homOfLE hWV)) := loc_open S hI V W a (by rw [ha]) hWV
    refine ⟨_, (diag S).map (homOfLE hWU), h1, ⟨emb S W ⟨x.1, hxg⟩, ?_⟩, ?_⟩
    · refine (emb_apply S (U := W) (V := U) hg ⟨x.1, hxg⟩).trans ?_
      congr 1
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← Functor.map_comp]
      exact h2

end

theorem exists_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ S : Sys I π s₀, ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsClosedImmersion i ∧ Surjective i ∧ Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ S
  have hbas : ∀ U ∈ X₀.affineOpens, ∀ (W : X₀.Opens) (x : X₀), x ∈ U → x ∈ W →
      ∃ V ∈ X₀.affineOpens, x ∈ V ∧ V ≤ U ∧ V ≤ W := by
    intro U hU W x hxU hxW
    have hU' : IsAffineOpen U := hU
    obtain ⟨f, hf, hxf⟩ := hU'.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
    exact ⟨_, hU'.basicOpen f, hxf, X₀.basicOpen_le f, hf⟩
  have hcov : sSup X₀.affineOpens = ⊤ := by
    rw [sSup_eq_iSup']
    exact iSup_affineOpens_eq_top X₀
  obtain ⟨X, j, hj1, hj2, κ, hκ, h1, h3, hdesc⟩ := exists_glue_desc X₀ X₀.affineOpens hbas hcov (diag S)
    (fun {U V} f ↦ diag_open S hI (U := U) (V := V) f.le) (emb S) (emb_closed S) (emb_surj S hI)
    (fun h ↦ emb_nat S h)
  obtain ⟨s, hs⟩ := hdesc (Sp R) (fun U ↦ spMap (algebraMap R (S.F.obj (Opposite.op U)))) (fun {U V} f ↦ by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact (mp S.F f.op).commutes r)
  refine ⟨X, s, j, hj1, hj2, ⟨Sys.Presents.ofSurjective S hj2 (fun U ↦ κ U.unop) (fun U ↦ hκ _) (fun U ↦ hs _)
    (fun U V a ↦ h3 a.unop) (fun U ↦ ?_)⟩⟩
  have hU : IsAffineOpen U.unop.1 := U.unop.2
  change spMap _ ≫ _ = hU.fromSpec ≫ j
  rw [← hU.isoSpec_inv_ι, Category.assoc, h1, emb, ← hU.isoSpec_hom]
  have key : ∀ {A B C D : Scheme.{0}} (e : A ≅ B) (f : B ⟶ C) (g : C ⟶ D), f ≫ g = e.inv ≫ (e.hom ≫ f) ≫ g :=
    fun e f g ↦ by simp
  exact key hU.isoSpec _ _

end GlobalTheory.LiftGlue
