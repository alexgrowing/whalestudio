import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.AffineZariskiSite

noncomputable section

namespace GlobalTheory.RelativeSpectrum

structure QCohSub {X Y : Scheme.{0}} (f : X ⟶ Y) (F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)) : Prop where
  app_mem : ∀ V : Y.Opens, IsAffineOpen V → ∀ a : Γ(Y, V), (f.app V).hom a ∈ F V
  res_mem : ∀ (V V' : Y.Opens) (hle : V' ≤ V), IsAffineOpen V → IsAffineOpen V' → ∀ x ∈ F V,
    (X.presheaf.map (homOfLE (f.preimage_mono hle)).op).hom x ∈ F V'
  loc : ∀ V : Y.Opens, IsAffineOpen V → ∀ (r : Γ(Y, V)) (x : Γ(X, f ⁻¹ᵁ Y.basicOpen r)),
    x ∈ F (Y.basicOpen r) →
    ∃ (k : ℕ) (y : Γ(X, f ⁻¹ᵁ V)), y ∈ F V ∧
      (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom y =
        (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom ((f.app V).hom r) ^ k * x

variable {X Y : Scheme.{0}} {f : X ⟶ Y} {F : ∀ V : Y.Opens, Subring Γ(X, f ⁻¹ᵁ V)}

set_option backward.isDefEq.respectTransparency false in

def diagram (H : QCohSub f F) : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := .of (F U.unop.1)
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono (toOpens_mono i.unop.le))).op).hom.restrict
      _ _ fun x hx ↦ H.res_mem _ _ (toOpens_mono i.unop.le) V.unop.2 U.unop.2 x hx)
  map_id U := by
    ext x
    change ((X.presheaf.map (𝟙 _)).hom x.1) = x.1
    simp
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono (toOpens_mono j.unop.le))
      (f.preimage_mono (toOpens_mono i.unop.le)), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def diagramMap (H : QCohSub f F) : (toOpensFunctor Y).op ⋙ Y.presheaf ⟶ diagram H where
  app U := CommRingCat.ofHom ((f.app U.unop.1).hom.codRestrict (F U.unop.1) (H.app_mem _ U.unop.2))
  naturality {U V} i := by
    ext x
    exact Subtype.ext congr($(f.naturality ((toOpensFunctor Y).op.map i)) x)

variable [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered (H : QCohSub f F) : (diagramMap H).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let inst : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have hl : IsLocalization.Away ((f.app U.1).hom r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
    let : Algebra Γ(X, f ⁻¹ᵁ U.1) Γ(X, X.basicOpen (f.app _ r)) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
    dsimp +instances [inst]
    rw! (castMode := .all) [f.preimage_basicOpen r]
    exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage U.2.isCompact)
        (f.isQuasiSeparated_preimage U.2.isQuasiSeparated) (f.app _ r)
  letI := ((diagram H).map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · have h1 : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) :=
      Y.toRingedSpace.isUnit_res_basicOpen r
    have h2 := h1.map ((diagramMap H).app (.op (U.basicOpen r))).hom
    convert h2 using 1
    exact congr($((diagramMap H).naturality (homOfLE (U.basicOpen_le r)).op) r).symm
  · intro s
    obtain ⟨k, y, hy, e⟩ := H.loc U.1 U.2 r s.1 s.2
    refine ⟨k, ⟨y, hy⟩, Subtype.ext ?_⟩
    rw [mul_comm] at e
    exact e.symm
  · intro a b hab
    have hab' : algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) a.1 =
        algebraMap Γ(X, f ⁻¹ᵁ U.1) Γ(X, f ⁻¹ᵁ Y.basicOpen r) b.1 := congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq ((f.app U.1).hom r) hab'
    exact ⟨n, Subtype.ext hn⟩

def glueData (H : QCohSub f F) := relativeGluingData (coequifibered H)

instance (H : QCohSub f F) : ((glueData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def relSpec (H : QCohSub f F) : Scheme := (glueData H).glued

def relCover (H : QCohSub f F) : (relSpec H).OpenCover := (glueData H).cover

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

def toRel (H : QCohSub f F) : X ⟶ relSpec H :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦
      (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U)
    fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Cover.trans, Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [relCover]
  rw [← colimit.w (glueData H).functor i]
  dsimp [glueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_toRel (H : QCohSub f F) (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toRel H = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (F U.1).subtype) ≫ (relCover H).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toRel H
  · congr 1; simp
  delta toRel
  generalize_proofs _ _ _ _ H'
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H' _

def fromRel (H : QCohSub f F) : relSpec H ⟶ Y := (glueData H).toBase

@[reassoc]
lemma ι_fromRel (H : QCohSub f F) (U : Y.affineOpens) :
    (relCover H).f U ≫ fromRel H =
      Spec.map ((diagramMap H).app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma fromRel_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    fromRel H ⁻¹ᵁ U = ((relCover H).f U).opensRange := by
  simpa using! (glueData H).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toRel_fromRel (H : QCohSub f F) : toRel H ≫ fromRel H = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toRel_assoc H _ _).trans ?_
  rw [ι_fromRel, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false in
lemma isFinite_fromRel (H : QCohSub f F)
    (hfin : ∀ U : Y.affineOpens, ((diagramMap H).app (.op U)).hom.Finite) : IsFinite (fromRel H) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (fromRel H ⁻¹ᵁ U).ι ((relCover H).f U)
      (by simpa using congr($(fromRel_preimage H U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hfin U)
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, ι_fromRel]

set_option backward.isDefEq.respectTransparency.types false in

def relObjIso (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    Γ(relSpec H, fromRel H ⁻¹ᵁ U) ≅ .of (F U) :=
  (relSpec H).presheaf.mapIso (eqToIso
    (by simpa using! (fromRel_preimage H ⟨U, hU⟩).symm)).op ≪≫
  ((relCover H).f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
lemma toRel_app_preimage (H : QCohSub f F) (U : Y.affineOpens) :
    (toRel H).app (fromRel H ⁻¹ᵁ ↑U) =
      (relObjIso H U.2).hom ≫
      CommRingCat.ofHom (F U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  dsimp [relObjIso]
  change _ = (relSpec H).presheaf.map (eqToHom (by simp [fromRel_preimage])).op ≫
      (((relCover H).f U).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (F U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op
  have H' : toRel H ⁻¹ᵁ fromRel H ⁻¹ᵁ U =
      (f ⁻¹ᵁ U).ι ''ᵁ (((f ⁻¹ᵁ U).ι ≫ toRel H) ⁻¹ᵁ fromRel H ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert! congr($(Scheme.Hom.congr_app (ι_toRel H U) (fromRel H ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H').op) using 1
  · simp [Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc, eqToHom_unop,
    ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _), eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

lemma relObjIso_hom_subtype (H : QCohSub f F) {U : Y.Opens} (hU : IsAffineOpen U) :
    (relObjIso H hU).hom ≫ CommRingCat.ofHom (F U).subtype =
    (toRel H).appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [Hom.appLE, toRel_app_preimage H ⟨U, hU⟩, Category.assoc]
  simp [← Functor.map_comp]
  rfl

lemma isDominant_toRel (H : QCohSub f F) (hfin : IsFinite (fromRel H)) : IsDominant (toRel H) := by
  have hqc : QuasiCompact (toRel H) := by
    apply MorphismProperty.of_postcomp (W := @QuasiCompact)
      (W' := @QuasiSeparated) _ (fromRel H)
    · infer_instance
    · rw [toRel_fromRel]
      infer_instance
  have hker : (toRel H).ker = ⊥ := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun U : Y.affineOpens ↦ ⟨fromRel H ⁻¹ᵁ U.1, U.2.preimage _⟩)
      (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top _) _) fun U ↦ ?_
    simp only [Hom.ker_apply, IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot,
      ← ConcreteCategory.mono_iff_injective_of_preservesPullback, ← MorphismProperty.monomorphisms]
    simp only [toRel_app_preimage,
      eqToHom_op, MorphismProperty.cancel_left_of_respectsIso,
      MorphismProperty.cancel_right_of_respectsIso]
    rw [MorphismProperty.monomorphisms, @ConcreteCategory.mono_iff_injective_of_preservesPullback]
    exact Subtype.val_injective
  have := congr(($(hker).support : Set (relSpec H)))
  rw [IdealSheafData.support_bot, Scheme.Hom.support_ker, TopologicalSpace.Closeds.coe_top] at this
  exact ⟨dense_iff_closure_eq.mpr this⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
lemma isReduced_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced (relSpec H) :=
  have (i : _) : AlgebraicGeometry.IsReduced ((relCover H).X i) := by
    have : _root_.IsReduced ((diagram H).obj (.op i)) :=
      isReduced_of_injective (F i.1).subtype Subtype.val_injective
    dsimp [relCover, glueData, relativeGluingData]
    infer_instance
  .of_openCover _ (relCover H)

lemma isIntegral_relSpec (H : QCohSub f F) [AlgebraicGeometry.IsIntegral X] [IsDominant (toRel H)] :
    AlgebraicGeometry.IsIntegral (relSpec H) :=
  have := isReduced_relSpec H
  have : IrreducibleSpace (relSpec H) := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          (toRel H).continuous.continuousOn).closure
    simpa using (toRel H).denseRange.closure_range.symm
  isIntegral_of_irreducibleSpace_of_isReduced _

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem exists_finite_cover {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [AlgebraicGeometry.IsIntegral S]
    [IsDominant gp] (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)) (hF : GlobalTheory.Mum.IsFinSub gp F) :
    ∃ (S' : Scheme) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ AlgebraicGeometry.IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (GlobalTheory.Mum.le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  obtain ⟨h1, h2, h3, h4⟩ := hF
  have H : QCohSub gp F := ⟨h1, h2, h3⟩
  haveI : AlgebraicGeometry.IsIntegral (Sp K) := inferInstanceAs (AlgebraicGeometry.IsIntegral (Spec (.of K)))
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : TopologicalSpace.NoetherianSpace (Sp K) := inferInstance
  haveI : QuasiCompact gp := inferInstance
  haveI : QuasiSeparated gp := inferInstance
  have hfin : IsFinite (fromRel H) := by
    refine isFinite_fromRel H fun U ↦ ?_
    obtain ⟨t, ht, hx⟩ := h4 U.1 U.2
    letI : Algebra Γ(S, U.1) (F U.1) :=
      ((gp.app U.1).hom.codRestrict (F U.1) (h1 _ U.2)).toAlgebra
    change Module.Finite Γ(S, U.1) (F U.1)
    refine Module.Finite.of_fg_top ?_
    rw [Submodule.fg_def]
    refine ⟨Set.range (fun y : t ↦ (⟨y.1, ht y.1 y.2⟩ : F U.1)), Set.finite_range _, ?_⟩
    rw [eq_top_iff]
    rintro x -
    obtain ⟨c, hc⟩ := hx x.1 x.2
    have : x = ∑ y : t, c y.1 • (⟨y.1, ht y.1 y.2⟩ : F U.1) := by
      apply Subtype.ext
      rw [hc, AddSubmonoidClass.coe_finset_sum, ← Finset.sum_coe_sort]
      rfl
    rw [this]
    exact Submodule.sum_mem _ fun y _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  haveI := isDominant_toRel H hfin
  refine ⟨relSpec H, fromRel H, toRel H, toRel_fromRel H, hfin, isIntegral_relSpec H, this, ?_⟩
  intro V hV x hx
  refine ⟨(relObjIso H hV).inv.hom ⟨x, hx⟩, ?_⟩
  rw [← relObjIso_hom_subtype H hV, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]
  rfl

end GlobalTheory.RelativeSpectrum
