import Mathlib

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AffineQuotient

open Scheme.AffineZariskiSite

variable {W X Y : Scheme.{0}}

def pullOver (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (U : Y.Opens) :
    Γ(X, f ⁻¹ᵁ U) ⟶ Γ(W, g ⁻¹ᵁ U) :=
  a.appLE _ _ (by rw [← ha]; exact le_rfl)

variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)

lemma app_pullOver (U : Y.Opens) : f.app U ≫ pullOver f g a ha U = g.app U := by
  subst ha
  rw [pullOver, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_comp_appLE ..

lemma map_pullOver {U V : Y.Opens} (h : U ≤ V) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op ≫ pullOver f g a ha U =
      pullOver f g a ha V ≫ W.presheaf.map (homOfLE (g.preimage_mono h)).op := by
  simp [pullOver]

def invariants (U : Y.Opens) : Subring Γ(X, f ⁻¹ᵁ U) :=
  (pullOver f g a ha U).hom.eqLocus (pullOver f g p hp U).hom

lemma mem_invariants {U : Y.Opens} {x : Γ(X, f ⁻¹ᵁ U)} :
    x ∈ invariants f g a ha p hp U ↔ pullOver f g a ha U x = pullOver f g p hp U x := Iff.rfl

lemma app_mem_invariants {U : Y.Opens} (y : Γ(Y, U)) : f.app U y ∈ invariants f g a ha p hp U := by
  rw [mem_invariants, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, app_pullOver,
    app_pullOver]

lemma map_mem_invariants {U V : Y.Opens} (h : U ≤ V) {x : Γ(X, f ⁻¹ᵁ V)}
    (hx : x ∈ invariants f g a ha p hp V) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op x ∈ invariants f g a ha p hp U := by
  rw [mem_invariants, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, map_pullOver _ _ _ _ h,
    map_pullOver _ _ _ _ h, CommRingCat.comp_apply, CommRingCat.comp_apply,
    (mem_invariants ..).1 hx]

set_option backward.isDefEq.respectTransparency false in

def diagram : Y.Opensᵒᵖ ⥤ CommRingCat where
  obj U := .of (invariants f g a ha p hp U.unop)
  map {V U} i :=
    CommRingCat.ofHom ((X.presheaf.map (homOfLE (f.preimage_mono i.unop.le)).op).hom.restrict
      _ _ fun x hx ↦ map_mem_invariants f g a ha p hp i.unop.le hx)
  map_id U := by simp; rfl
  map_comp i j := by
    simp only [← CommRingCat.ofHom_comp]
    rw [← homOfLE_comp (f.preimage_mono j.unop.le) (f.preimage_mono i.unop.le), op_comp]
    simp_rw [X.presheaf.map_comp]
    rfl

def diagramMap : Y.presheaf ⟶ diagram f g a ha p hp where
  app U := CommRingCat.ofHom ((f.app U.unop).hom.codRestrict (invariants f g a ha p hp U.unop)
    (app_mem_invariants f g a ha p hp))
  naturality {U V} i := by ext x; exact Subtype.ext congr($(f.naturality i) x)

set_option backward.isDefEq.respectTransparency false in
lemma isLocalization_preimage [QuasiCompact f] [QuasiSeparated f] {U : Y.Opens}
    (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    letI := (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
    IsLocalization.Away (f.app U r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := by
  let : Algebra Γ(X, f ⁻¹ᵁ U) Γ(X, X.basicOpen (f.app _ r)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le _)).op).hom.toAlgebra
  rw! (castMode := .all) [f.preimage_basicOpen r]
  exact isLocalization_basicOpen_of_qcqs (f.isCompact_preimage hU.isCompact)
      (f.isQuasiSeparated_preimage hU.isQuasiSeparated) (f.app _ r)

lemma isLocalization_eqLocus {B T B' T' : Type} [CommRing B] [CommRing T] [CommRing B']
    [CommRing T'] [Algebra B B'] [Algebra T T'] (α β : B →+* T) (α' β' : B' →+* T')
    (hα : ∀ x, α' (algebraMap B B' x) = algebraMap T T' (α x))
    (hβ : ∀ x, β' (algebraMap B B' x) = algebraMap T T' (β x))
    (r : α.eqLocus β) [IsLocalization.Away (r : B) B'] [IsLocalization.Away (α r) T']
    [Algebra (α.eqLocus β) (α'.eqLocus β')]
    (h : ∀ x, (algebraMap (α.eqLocus β) (α'.eqLocus β') x : B') = algebraMap B B' x) :
    IsLocalization.Away r (α'.eqLocus β') := by
  have hr : α r = β r := r.2
  refine IsLocalization.Away.mk r ?_ ?_ ?_
  · obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := B') (r : B)).exists_right_inv
    have hT := IsLocalization.Away.algebraMap_isUnit (S := T') (α r)
    have hm : α' u = β' u := by
      apply hT.mul_left_cancel
      have h1 := congr(α' $hu)
      have h2 := congr(β' $hu)
      rw [map_mul, map_one, hα] at h1
      rw [map_mul, map_one, hβ, ← hr] at h2
      rw [h1, h2]
    refine IsUnit.of_mul_eq_one (⟨u, hm⟩ : α'.eqLocus β') (Subtype.ext ?_)
    simpa [h] using hu
  · rintro ⟨z, hz⟩
    obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj (r : B) z
    have hz' : α' z = β' z := hz
    have h1 : algebraMap T T' (α y) = algebraMap T T' (β y) := by
      rw [← hα, ← hβ, ← hy, map_mul, map_mul, map_pow, map_pow, hα, hβ, hr, hz']
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (α r) h1
    refine ⟨m + n, ⟨r ^ m * y, ?_⟩, Subtype.ext ?_⟩
    · change α _ = β _
      rw [map_mul, map_mul, map_pow, map_pow, hm, hr]
    · simp only [h, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ← hy]
      ring
  · intro x y hxy
    have h1 : algebraMap B B' x = algebraMap B B' y := by rw [← h, ← h, hxy]
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (r : B) h1
    exact ⟨m, Subtype.ext (by simpa using hm)⟩

variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

set_option backward.isDefEq.respectTransparency false in
lemma coequifibered_diagramMap :
    ((toOpensFunctor Y).op.whiskerLeft (diagramMap f g a ha p hp)).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let := (X.presheaf.map (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  let := (W.presheaf.map (homOfLE (g.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have h1 := isLocalization_preimage f U.2 r
  have h2 := isLocalization_preimage g U.2 r
  rw [← app_pullOver f g a ha] at h2
  exact @isLocalization_eqLocus _ _ _ _ _ _ _ _ _ _ (pullOver f g a ha U.1).hom
    (pullOver f g p hp U.1).hom (pullOver f g a ha (Y.basicOpen r)).hom
    (pullOver f g p hp (Y.basicOpen r)).hom
    (fun x ↦ congr($(map_pullOver f g a ha (Y.basicOpen_le r)) x))
    (fun x ↦ congr($(map_pullOver f g p hp (Y.basicOpen_le r)) x))
    ⟨f.app U.1 r, app_mem_invariants f g a ha p hp r⟩ h1 h2
    ((diagram f g a ha p hp).map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra (fun _ ↦ rfl)

def glueData := relativeGluingData (coequifibered_diagramMap f g a ha p hp)

instance : ((glueData f g a ha p hp).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

def quot : Scheme := (glueData f g a ha p hp).glued

def cover : (quot f g a ha p hp).OpenCover := (glueData f g a ha p hp).cover

def invariantsInclusion (U : Y.Opens) :
    (diagram f g a ha p hp).obj (.op U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  CommRingCat.ofHom (invariants f g a ha p hp U).subtype

def toQuotPiece (U : Y.affineOpens) : (f ⁻¹ᵁ U.1).toScheme ⟶ quot f g a ha p hp :=
  (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (invariantsInclusion f g a ha p hp U.1) ≫
    (cover f g a ha p hp).f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

def toQuot : X ⟶ quot f g a ha p hp :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Y).pullback₁ f)
    (fun U ↦ (pullbackRestrictIsoRestrict f _).hom ≫ toQuotPiece f g a ha p hp U)
    fun {U V : Y.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Scheme.Cover.trans ((directedCover Y).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, toQuotPiece, toQuotPiece,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  dsimp [cover]
  rw [← colimit.w (glueData f g a ha p hp).functor i]
  dsimp [glueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_toQuot (U : Y.affineOpens) :
    (f ⁻¹ᵁ U.1).ι ≫ toQuot f g a ha p hp = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype) ≫
        (cover f g a ha p hp).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Y).pullback₁ f).f U ≫ toQuot f g a ha p hp
  · congr 1; simp
  delta toQuot
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

def fromQuot : quot f g a ha p hp ⟶ Y := (glueData f g a ha p hp).toBase

@[reassoc]
lemma ι_fromQuot (U : Y.affineOpens) :
    (cover f g a ha p hp).f U ≫ fromQuot f g a ha p hp =
      Spec.map ((diagramMap f g a ha p hp).app (.op U.1)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma fromQuot_preimage (U : Y.affineOpens) :
    fromQuot f g a ha p hp ⁻¹ᵁ U = ((cover f g a ha p hp).f U).opensRange := by
  simpa using! (glueData f g a ha p hp).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toQuot_fromQuot : toQuot f g a ha p hp ≫ fromQuot f g a ha p hp = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toQuot_assoc f g a ha p hp _ _).trans ?_
  rw [ι_fromQuot, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in

lemma of_charts (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {ι : Type}
    (X' Y' : ι → Scheme.{0}) (u : ∀ i, X' i ⟶ X) (v : ∀ i, Y' i ⟶ Y) (f' : ∀ i, X' i ⟶ Y' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (f' i) (u i) (v i) f) (hP : ∀ i, P (f' i)) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers ι Y' v hv) fun i ↦ ?_
  have := (h i).flip.isoPullback_inv_snd
  change P (pullback.snd f (v i))
  rw [← this, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP i

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in

lemma isPullback_of_charts {Z Q : Scheme.{0}} (b : W ⟶ Z) (q : X ⟶ Q) (q' : Z ⟶ Q) {ι : Type}
    (W' X' : ι → Scheme.{0}) (u : ∀ i, W' i ⟶ W) (v : ∀ i, X' i ⟶ X) (a' : ∀ i, W' i ⟶ X' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (a' i) (u i) (v i) a)
    (h' : ∀ i, IsPullback (a' i) (u i ≫ b) (v i ≫ q) q') : IsPullback a b q q' := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers ι X' v hv) fun i ↦ ?_
  change IsPullback (pullback.snd a (v i)) (pullback.fst a (v i) ≫ b) (v i ≫ q) q'
  refine (h' i).of_iso (h i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    <;> simp

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in
lemma SpecMap_pullOver {U : Y.Opens} (hf : IsAffineOpen (f ⁻¹ᵁ U)) (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    Spec.map (pullOver f g a ha U) ≫ hf.fromSpec = hg.fromSpec ≫ a :=
  IsAffineOpen.SpecMap_appLE_fromSpec ..

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in
lemma isPullback_pullOver {U : Y.Opens} (hf : IsAffineOpen (f ⁻¹ᵁ U))
    (hg : IsAffineOpen (g ⁻¹ᵁ U)) :
    IsPullback (Spec.map (pullOver f g a ha U)) hg.fromSpec hf.fromSpec a := by
  refine IsOpenImmersion.isPullback _ _ _ _ (SpecMap_pullOver f g a ha hf hg).symm ?_
  subst ha
  rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]
  rfl

lemma fromSpec_toQuot (U : Y.affineOpens) (hf : IsAffineOpen (f ⁻¹ᵁ U.1)) :
    hf.fromSpec ≫ toQuot f g a ha p hp =
      Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype) ≫
        (cover f g a ha p hp).f U := by
  rw [← cancel_epi hf.isoSpec.hom, IsAffineOpen.isoSpec_hom,
    IsAffineOpen.toSpecΓ_fromSpec_assoc, ι_toQuot]

lemma isPullback_toQuot (U : Y.affineOpens) (hf : IsAffineOpen (f ⁻¹ᵁ U.1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)) hf.fromSpec
      ((cover f g a ha p hp).f U) (toQuot f g a ha p hp) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (fromSpec_toQuot f g a ha p hp U hf) ?_
  rw [← fromQuot_preimage, ← Scheme.Hom.comp_preimage, toQuot_fromQuot,
    IsAffineOpen.opensRange_fromSpec]

lemma isPullback_fromQuot (U : Y.affineOpens) :
    IsPullback (Spec.map ((diagramMap f g a ha p hp).app (.op U.1))) ((cover f g a ha p hp).f U)
      U.2.fromSpec (fromQuot f g a ha p hp) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (ι_fromQuot f g a ha p hp U) ?_
  rw [← fromQuot_preimage, IsAffineOpen.opensRange_fromSpec]

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in
lemma exists_fromSpec_eq [IsAffineHom f] (x : X) :
    ∃ (U : Y.affineOpens) (z : Spec Γ(X, f ⁻¹ᵁ U.1)), (U.2.preimage f).fromSpec z = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  refine ⟨⟨U, hU⟩, ?_⟩
  change x ∈ Set.range _
  rw [IsAffineOpen.range_fromSpec]
  exact hx

lemma isFinite_fromQuot [IsFinite f] [IsLocallyNoetherian Y] :
    IsFinite (fromQuot f g a ha p hp) := by
  refine of_charts _ @IsFinite _ _ _ _ _ (fun y ↦ ?_) (isPullback_fromQuot f g a ha p hp)
    fun U ↦ ?_
  · exact exists_fromSpec_eq (𝟙 Y) y
  · rw [IsFinite.SpecMap_iff]
    have h1 : (f.app U.1).hom.Finite := f.finite_app U.1 U.2
    have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
    let φ : Γ(Y, U.1) →+* invariants f g a ha p hp U.1 :=
      (f.app U.1).hom.codRestrict (invariants f g a ha p hp U.1)
        (app_mem_invariants f g a ha p hp)
    change φ.Finite
    algebraize [(f.app U.1).hom, φ]
    have : IsScalarTower Γ(Y, U.1) (invariants f g a ha p hp U.1) Γ(X, f ⁻¹ᵁ U.1) :=
      .of_algebraMap_eq' rfl
    exact Module.Finite.of_injective
      (IsScalarTower.toAlgHom Γ(Y, U.1) (invariants f g a ha p hp U.1)
        Γ(X, f ⁻¹ᵁ U.1)).toLinearMap Subtype.val_injective

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g] in

theorem exists_quotient [IsFinite f] [IsAffineHom g] [IsLocallyNoetherian Y]
    (H : ∀ U : Y.affineOpens, (invariants f g a ha p hp U.1).subtype.FaithfullyFlat ∧
      IsPushout (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (CommRingCat.ofHom (invariants f g a ha p hp U.1).subtype)
        (pullOver f g a ha U.1) (pullOver f g p hp U.1)) :
    ∃ (Q : Scheme.{0}) (q : X ⟶ Q) (π : Q ⟶ Y), q ≫ π = f ∧ IsFinite π ∧ IsFinite q ∧ Flat q ∧
      Surjective q ∧ IsPullback a p q q := by
  have h1 := isFinite_fromQuot f g a ha p hp
  have hc : ∀ y, ∃ (U : Y.affineOpens) (z : _), (cover f g a ha p hp).f U z = y :=
    fun y ↦ (cover f g a ha p hp).exists_eq y
  refine ⟨_, toQuot f g a ha p hp, fromQuot f g a ha p hp, toQuot_fromQuot .., h1, ?_, ?_, ?_, ?_⟩
  · have : IsFinite (toQuot f g a ha p hp ≫ fromQuot f g a ha p hp) := by
      rw [toQuot_fromQuot]; infer_instance
    exact .of_comp _ (fromQuot f g a ha p hp)
  · exact of_charts _ @Flat _ _ _ _ _ hc
      (fun U ↦ isPullback_toQuot f g a ha p hp U (U.2.preimage f))
      fun U ↦ ((flat_and_surjective_SpecMap_iff _).2 (H U).1).1
  · exact of_charts _ @Surjective _ _ _ _ _ hc
      (fun U ↦ isPullback_toQuot f g a ha p hp U (U.2.preimage f))
      fun U ↦ ((flat_and_surjective_SpecMap_iff _).2 (H U).1).2
  · refine isPullback_of_charts a p _ _ _ _ _ _ _ (exists_fromSpec_eq f)
      (fun U ↦ isPullback_pullOver f g a ha (U.2.preimage f) (U.2.preimage g)) fun U ↦ ?_
    rw [← SpecMap_pullOver f g p hp (U.2.preimage f), fromSpec_toQuot]
    exact (isPullback_SpecMap_of_isPushout _ _ _ _ (H U).2).paste_vert
      (isPullback_toQuot f g a ha p hp U (U.2.preimage f))

end GlobalTheory.AffineQuotient
