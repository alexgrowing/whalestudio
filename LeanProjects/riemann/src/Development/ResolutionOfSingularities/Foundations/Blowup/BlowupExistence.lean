import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

private theorem ideal_map_inv_map_hom {A B : CommRingCat.{u}} (e : A ≅ B) (K : Ideal A) :
    Ideal.map e.inv.hom (Ideal.map e.hom.hom K) = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

theorem IsBlowupAlongIdealSheaf.exists_lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    ∃ a : W ⟶ X', a ≫ π = g :=
  (h.2 W g hg).exists

noncomputable section

noncomputable def IsBlowupAlongIdealSheaf.lift {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) : W ⟶ X' :=
  (h.exists_lift g hg).choose

theorem IsBlowupAlongIdealSheaf.lift_comp {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) :
    h.lift g hg ≫ π = g :=
  (h.exists_lift g hg).choose_spec

end

theorem IsBlowupAlongIdealSheaf.hom_ext {X X' : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) {W : Scheme.{u}} {g : W ⟶ X}
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) {a b : W ⟶ X'}
    (ha : a ≫ π = g) (hb : b ≫ π = g) : a = b :=
  h.hom_ext_of_comp_eq hg ha hb

theorem IsBlowupAlongIdealSheaf.comp_iso_hom {X X' Y : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (e : X ≅ Y) :
    IsBlowupAlongIdealSheaf (π ≫ e.hom) (I.comap e.inv) := by
  constructor
  · rw [← Scheme.IdealSheafData.comap_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
    exact h.1
  · intro W g hg
    rw [← Scheme.IdealSheafData.comap_comp] at hg
    obtain ⟨a, ha, hu⟩ := h.2 W (g ≫ e.inv) hg
    refine ⟨a, ?_, ?_⟩
    · show a ≫ π ≫ e.hom = g
      rw [← Category.assoc, ha, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro b hb
      have hb' : b ≫ π ≫ e.hom = g := hb
      refine hu b ?_
      show b ≫ π = g ≫ e.inv
      rw [← hb']
      simp

theorem IsBlowupAlongIdealSheaf.pullback_snd_of_isOpenImmersion {X X' U : Scheme.{u}} {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) (f : U ⟶ X) [IsOpenImmersion f] :
    IsBlowupAlongIdealSheaf (pullback.snd π f) (I.comap f) := by
  constructor
  · have h1 : (I.comap f).comap (pullback.snd π f)
        = (I.comap π).comap (pullback.fst π f) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        pullback.condition]
    rw [h1]
    exact h.1.comap_of_isOpenImmersion (pullback.fst π f)
  · intro W g hg
    rw [← Scheme.IdealSheafData.comap_comp] at hg
    obtain ⟨a, ha, hu⟩ := h.2 W (g ≫ f) hg
    refine ⟨pullback.lift a g ha, pullback.lift_snd _ _ _, ?_⟩
    intro b hb
    have hb' : b ≫ pullback.snd π f = g := hb
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst]
      refine hu _ ?_
      show (b ≫ pullback.fst π f) ≫ π = g ≫ f
      rw [Category.assoc, pullback.condition, ← Category.assoc, hb']
    · rw [pullback.lift_snd, hb']

private theorem exists_isBlowupAlongIdealSheaf_spec_of_commRing (R : Type u) [CommRing R]
    (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (CommRingCat.of R)), IsBlowupAlongIdealSheaf π I := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal R, specIdealSheaf J = I := by
    refine ⟨Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (I.ideal ⟨⊤, isAffineOpen_top _⟩), ?_⟩
    refine Scheme.IdealSheafData.ext_of_isAffine ?_
    rw [specIdealSheaf_ideal_top, ideal_map_inv_map_hom]
  refine ⟨affineBlowup J, AffineBlowup.toSpec J, ?_⟩
  rw [← hJ]
  exact isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem exists_isBlowupAlongIdealSheaf_spec (R : CommRingCat.{u}) (I : (Spec R).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec R), IsBlowupAlongIdealSheaf π I :=
  exists_isBlowupAlongIdealSheaf_spec_of_commRing (R : Type u) I

theorem exists_isBlowupAlongIdealSheaf_of_isAffine (X : Scheme.{u}) [IsAffine X] (I : X.IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsBlowupAlongIdealSheaf π I := by
  obtain ⟨Y, π, hπ⟩ := exists_isBlowupAlongIdealSheaf_spec Γ(X, ⊤) (I.comap X.isoSpec.inv)
  refine ⟨Y, π ≫ X.isoSpec.inv, ?_⟩
  have h2 := hπ.comp_iso_hom X.isoSpec.symm
  simp only [Iso.symm_hom, Iso.symm_inv] at h2
  rwa [← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id,
    Scheme.IdealSheafData.comap_id] at h2

private theorem comp_base_apply {A B C : Scheme.{u}} (u : A ⟶ B) (z : B ⟶ C) (p : A) :
    (u ≫ z).base p = z.base (u.base p) := by simp

private theorem ι_base_mem {X : Scheme.{u}} (U : X.Opens) (v : U.toScheme) :
    U.ι.base v ∈ U := by
  have h : U.ι.base v ∈ Set.range ⇑U.ι.base := Set.mem_range_self v
  rwa [Scheme.Opens.range_ι] at h

private theorem isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp {X P Z : Scheme.{u}} (I : X.IdealSheafData)
    (u : P ⟶ Z) [IsOpenImmersion u] (z : Z ⟶ X) (hz : IsLocallyGeneratedByNonZeroDivisor (I.comap z)) :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (u ≫ z)) := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact hz.comap_of_isOpenImmersion u

private theorem range_id_base (Z : Scheme.{u}) :
    Set.range ⇑(𝟙 Z : Z ⟶ Z).base = Set.univ := by
  refine Set.eq_univ_of_forall (fun v => ⟨v, ?_⟩)
  simp

private theorem pullback_hom_ext_of_mono {Z A B : Scheme.{u}} (a : A ⟶ Z) (b : B ⟶ Z)
    [Mono a] [Mono b] {P : Scheme.{u}} {u v : P ⟶ pullback a b}
    (h : u ≫ pullback.fst a b ≫ a = v ≫ pullback.fst a b ≫ a) : u = v := by
  have h1 : u ≫ pullback.fst a b = v ≫ pullback.fst a b := by
    rw [← cancel_mono a, Category.assoc, Category.assoc]
    exact h
  have h2 : u ≫ pullback.snd a b = v ≫ pullback.snd a b := by
    rw [← cancel_mono b, Category.assoc, Category.assoc, ← pullback.condition]
    exact h
  exact pullback.hom_ext h1 h2

private def IsBlowupAlongIdealSheafOver {X : Scheme.{u}} (I : X.IdealSheafData) (S : X.Opens) {Z : Scheme.{u}}
    (z : Z ⟶ X) : Prop :=
  Set.range ⇑z.base ⊆ (S : Set X) ∧ IsLocallyGeneratedByNonZeroDivisor (I.comap z) ∧
    ∀ {Y : Scheme.{u}} (y : Y ⟶ X), IsLocallyGeneratedByNonZeroDivisor (I.comap y) →
      Set.range ⇑y.base ⊆ (S : Set X) → ∃! a : Y ⟶ Z, a ≫ z = y

private theorem blowupOver_hom_ext {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X))
    {a b : Y ⟶ Z} (ha : a ≫ z = y) (hb : b ≫ z = y) : a = b := by
  obtain ⟨c, -, hu⟩ := hz.2.2 y hy hr
  rw [hu a ha, hu b hb]

private noncomputable def liftOfIsBlowupAlongIdealSheafOver {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X)) : Y ⟶ Z :=
  (hz.2.2 y hy hr).choose

private theorem blowupOverLift_comp {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) {Y : Scheme.{u}} (y : Y ⟶ X)
    (hy : IsLocallyGeneratedByNonZeroDivisor (I.comap y)) (hr : Set.range ⇑y.base ⊆ (S : Set X)) :
    liftOfIsBlowupAlongIdealSheafOver hz y hy hr ≫ z = y :=
  (hz.2.2 y hy hr).choose_spec.1

private theorem blowupOver_of_isBlowupAlongIdealSheaf {X Z : Scheme.{u}} {I : X.IdealSheafData} {W : X.Opens}
    {p : Z ⟶ W.toScheme} (h : IsBlowupAlongIdealSheaf p (I.comap W.ι)) : IsBlowupAlongIdealSheafOver I W (p ≫ W.ι) := by
  have hrange : Set.range ⇑(W.ι).base = (W : Set X) := W.range_ι
  refine ⟨?_, ?_, ?_⟩
  · rw [← hrange]
    rintro _ ⟨v, rfl⟩
    exact ⟨p.base v, by simp⟩
  · rw [Scheme.IdealSheafData.comap_comp]
    exact h.1
  · intro Y y hy hry
    have hr : Set.range ⇑y.base ⊆ Set.range ⇑W.ι.base := by
      rw [hrange]; exact hry
    have hfac : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac W.ι y hr
    have hy2 : IsLocallyGeneratedByNonZeroDivisor ((I.comap W.ι).comap (IsOpenImmersion.lift W.ι y hr)) := by
      rw [← Scheme.IdealSheafData.comap_comp, hfac]; exact hy
    obtain ⟨a, ha, hu⟩ := h.2 Y (IsOpenImmersion.lift W.ι y hr) hy2
    refine ⟨a, ?_, ?_⟩
    · show a ≫ p ≫ W.ι = y
      rw [← Category.assoc, ha, hfac]
    · intro b hb
      have hbb : b ≫ (p ≫ W.ι) = y := hb
      refine hu b ?_
      have hbb2 : (b ≫ p) ≫ W.ι = IsOpenImmersion.lift W.ι y hr ≫ W.ι := by
        rw [Category.assoc, hbb, hfac]
      exact (cancel_mono W.ι).mp hbb2

private theorem blowupOver_inf_preimage {X Z : Scheme.{u}} {I : X.IdealSheafData} {S : X.Opens}
    {z : Z ⟶ X} (hz : IsBlowupAlongIdealSheafOver I S z) (T : X.Opens) :
    IsBlowupAlongIdealSheafOver I (S ⊓ T) ((z ⁻¹ᵁ T).ι ≫ z) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    rw [comp_base_apply]
    refine TopologicalSpace.Opens.mem_inf.mpr ⟨hz.1 (Set.mem_range_self _), ?_⟩
    exact ι_base_mem (z ⁻¹ᵁ T) p
  · exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ z hz.2.1
  · intro Y y hy hr
    have hrS : Set.range ⇑y.base ⊆ (S : Set X) := fun p hp =>
      (TopologicalSpace.Opens.mem_inf.mp (hr hp)).1
    obtain ⟨a, ha, hu⟩ := hz.2.2 y hy hrS
    have hra : Set.range ⇑a.base ⊆ Set.range ⇑(z ⁻¹ᵁ T).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      show z.base (a.base p) ∈ T
      rw [← comp_base_apply, ha]
      exact (TopologicalSpace.Opens.mem_inf.mp (hr (Set.mem_range_self p))).2
    refine ⟨IsOpenImmersion.lift _ a hra, ?_, ?_⟩
    · show IsOpenImmersion.lift (z ⁻¹ᵁ T).ι a hra ≫ ((z ⁻¹ᵁ T).ι ≫ z) = y
      rw [← Category.assoc, IsOpenImmersion.lift_fac, ha]
    · intro b hb
      have hbb : b ≫ ((z ⁻¹ᵁ T).ι ≫ z) = y := hb
      have hb' : (b ≫ (z ⁻¹ᵁ T).ι) ≫ z = y := by rw [Category.assoc]; exact hbb
      have h1 : b ≫ (z ⁻¹ᵁ T).ι = a := hu _ hb'
      have h2 : IsOpenImmersion.lift (z ⁻¹ᵁ T).ι a hra ≫ (z ⁻¹ᵁ T).ι = a :=
        IsOpenImmersion.lift_fac _ _ _
      exact (cancel_mono (z ⁻¹ᵁ T).ι).mp (by rw [h1, h2])

private theorem exists_isBlowupAlongIdealSheaf_affineOpen {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ (U : X.Opens).toScheme),
      IsBlowupAlongIdealSheaf p (I.comap (U : X.Opens).ι) := by
  have : IsAffine (U : X.Opens).toScheme := U.2
  exact exists_isBlowupAlongIdealSheaf_of_isAffine _ _

private noncomputable def localBlowup {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Scheme.{u} :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose

private noncomputable def localBlowupProjection {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    localBlowup I U ⟶ (U : X.Opens).toScheme :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose_spec.choose

private theorem isBlowupAlongIdealSheaf_localBlowupProj {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    IsBlowupAlongIdealSheaf (localBlowupProjection I U) (I.comap (U : X.Opens).ι) :=
  (exists_isBlowupAlongIdealSheaf_affineOpen I U).choose_spec.choose_spec

private noncomputable def localBlowupToBase {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    localBlowup I U ⟶ X :=
  localBlowupProjection I U ≫ (U : X.Opens).ι

private theorem blowupOver_localBlowupMap {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    IsBlowupAlongIdealSheafOver I (U : X.Opens) (localBlowupToBase I U) :=
  blowupOver_of_isBlowupAlongIdealSheaf (isBlowupAlongIdealSheaf_localBlowupProj I U)

private noncomputable def overlap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (localBlowup I i).Opens :=
  (localBlowupToBase I i) ⁻¹ᵁ (j : X.Opens)

private noncomputable def overlapInclusion {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ localBlowup I i :=
  (overlap I i j).ι

private theorem overlapIncl_eq {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens) :
    overlapInclusion I i j = (overlap I i j).ι := rfl

private theorem isOpenImmersion_overlapIncl {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : IsOpenImmersion (overlapInclusion I i j) := by
  rw [overlapIncl_eq]
  infer_instance

private noncomputable def overlapToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ X :=
  overlapInclusion I i j ≫ localBlowupToBase I i

private theorem overlapMap_eq {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens) :
    overlapToBase I i j = overlapInclusion I i j ≫ localBlowupToBase I i := rfl

private theorem blowupOver_overlapMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) :
    IsBlowupAlongIdealSheafOver I ((i : X.Opens) ⊓ (j : X.Opens)) (overlapToBase I i j) :=
  blowupOver_inf_preimage (blowupOver_localBlowupMap I i) (j : X.Opens)

private theorem overlapMap_base_mem_inf {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) (p : (overlap I i j).toScheme) :
    (overlapToBase I i j).base p ∈ ((i : X.Opens) ⊓ (j : X.Opens)) :=
  (blowupOver_overlapMap I i j).1 (Set.mem_range_self p)

private theorem range_overlapMap_subset_inf_swap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) :
    Set.range ⇑(overlapToBase I i j).base ⊆ (((j : X.Opens) ⊓ (i : X.Opens)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact TopologicalSpace.Opens.mem_inf.mpr
    ⟨(TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf I i j p)).2,
      (TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf I i j p)).1⟩

private noncomputable def overlapTransition {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j : X.affineOpens) : (overlap I i j).toScheme ⟶ (overlap I j i).toScheme :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I j i) (overlapToBase I i j)
    (blowupOver_overlapMap I i j).2.1 (range_overlapMap_subset_inf_swap I i j)

private theorem overlapTrans_comp_overlapMap {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens) :
    overlapTransition I i j ≫ overlapToBase I j i = overlapToBase I i j :=
  blowupOverLift_comp _ _ _ _

private theorem isIso_overlapIncl_self {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) : IsIso (overlapInclusion I i i) := by
  have := isOpenImmersion_overlapIncl I i i
  have e2 : ((overlap I i i : (localBlowup I i).Opens) : Set (localBlowup I i)) = Set.univ := by
    ext v
    simp only [Set.mem_univ, iff_true]
    show (localBlowupToBase I i).base v ∈ (i : X.Opens)
    exact (blowupOver_localBlowupMap I i).1 (Set.mem_range_self v)
  have h1 : Set.range ⇑(overlapInclusion I i i).base
      = Set.range ⇑(𝟙 (localBlowup I i) : localBlowup I i ⟶ localBlowup I i).base := by
    rw [overlapIncl_eq, Scheme.Opens.range_ι, e2, range_id_base]
  have h2 := IsOpenImmersion.isoOfRangeEq_hom_fac (overlapInclusion I i i) (𝟙 (localBlowup I i)) h1
  rw [Category.comp_id] at h2
  rw [← h2]
  infer_instance

private theorem overlapTrans_self {X : Scheme.{u}} (I : X.IdealSheafData) (i : X.affineOpens) :
    overlapTransition I i i = 𝟙 ((overlap I i i).toScheme) := by
  have := isOpenImmersion_overlapIncl I i i
  rw [← cancel_mono (overlapInclusion I i i)]
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I i) (overlapToBase I i i)
    (blowupOver_overlapMap I i i).2.1 ?_ ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact (TopologicalSpace.Opens.mem_inf.mp (overlapMap_base_mem_inf I i i p)).1
  · rw [Category.assoc, ← overlapMap_eq, overlapTrans_comp_overlapMap]
  · rw [Category.id_comp, ← overlapMap_eq]

private noncomputable def tripleOverlapToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) : pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ X :=
  pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j

private theorem overlapPullbackMap_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapToBase I i j k
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i j := rfl

private theorem isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (tripleOverlapToBase I i j k)) := by
  have := isOpenImmersion_overlapIncl I i j
  have := isOpenImmersion_overlapIncl I i k
  have h : tripleOverlapToBase I i j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapInclusion I i j)
        ≫ localBlowupToBase I i := by
    rw [overlapPullbackMap_eq, overlapMap_eq, Category.assoc]
  rw [h]
  exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ (localBlowupToBase I i) (blowupOver_localBlowupMap I i).2.1

private theorem overlapPullbackMap_base_mem_inf_left {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) (p : ↥(pullback (overlapInclusion I i j) (overlapInclusion I i k))) :
    (tripleOverlapToBase I i j k).base p ∈ ((i : X.Opens) ⊓ (j : X.Opens)) := by
  rw [overlapPullbackMap_eq, comp_base_apply]
  exact (blowupOver_overlapMap I i j).1 (Set.mem_range_self _)

private theorem overlapPullbackMap_base_mem_inf_right {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) (p : ↥(pullback (overlapInclusion I i j) (overlapInclusion I i k))) :
    (tripleOverlapToBase I i j k).base p ∈ ((i : X.Opens) ⊓ (k : X.Opens)) := by
  have h : tripleOverlapToBase I i j k
      = pullback.snd (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapToBase I i k := by
    rw [overlapPullbackMap_eq, overlapMap_eq, overlapMap_eq, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  rw [h, comp_base_apply]
  exact (blowupOver_overlapMap I i k).1 (Set.mem_range_self _)

private theorem range_overlapPullbackMap_subset_source {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    Set.range ⇑(tripleOverlapToBase I i j k).base ⊆ ((i : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left I i j k p)).1

private theorem range_overlapPullbackMap_subset_target {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    Set.range ⇑(tripleOverlapToBase I i j k).base ⊆ ((j : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left I i j k p)).2

private theorem range_overlapPullbackMap_subset_inf {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    Set.range ⇑(tripleOverlapToBase I i j k).base
      ⊆ (((j : X.Opens) ⊓ (k : X.Opens)) : Set X) := by
  rintro _ ⟨p, rfl⟩
  exact TopologicalSpace.Opens.mem_inf.mpr
    ⟨(TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_left I i j k p)).2,
      (TopologicalSpace.Opens.mem_inf.mp (overlapPullbackMap_base_mem_inf_right I i j k p)).2⟩

private noncomputable def tripleOverlapLift {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    pullback (overlapInclusion I i j) (overlapInclusion I i k) ⟶ (overlap I j k).toScheme :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I j k) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) (range_overlapPullbackMap_subset_inf I i j k)

private theorem overlapPullbackLift_comp_overlapMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapLift I i j k ≫ overlapToBase I j k = tripleOverlapToBase I i j k :=
  blowupOverLift_comp _ _ _ _

private theorem overlapPullbackLift_comp_overlapIncl {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapLift I i j k ≫ overlapInclusion I j k
      = (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
        ≫ overlapInclusion I j i := by
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I j) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) (range_overlapPullbackMap_subset_target I i j k) ?_ ?_
  · rw [Category.assoc, ← overlapMap_eq, overlapPullbackLift_comp_overlapMap]
  · rw [Category.assoc, ← overlapMap_eq, Category.assoc, overlapTrans_comp_overlapMap,
      overlapPullbackMap_eq]

private noncomputable def tripleOverlapTransition {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    pullback (overlapInclusion I i j) (overlapInclusion I i k)
      ⟶ pullback (overlapInclusion I j k) (overlapInclusion I j i) :=
  pullback.lift (tripleOverlapLift I i j k)
    (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
    (overlapPullbackLift_comp_overlapIncl I i j k)

private theorem overlapTransPullback_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapTransition I i j k
      = pullback.lift (tripleOverlapLift I i j k)
          (pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j)
          (overlapPullbackLift_comp_overlapIncl I i j k) := rfl

private theorem overlapTransPullback_comp_snd {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapTransition I i j k ≫ pullback.snd (overlapInclusion I j k) (overlapInclusion I j i)
      = pullback.fst (overlapInclusion I i j) (overlapInclusion I i k) ≫ overlapTransition I i j := by
  rw [overlapTransPullback_eq]
  exact pullback.lift_snd _ _ _

private theorem overlapTransPullback_comp_overlapPullbackMap {X : Scheme.{u}} (I : X.IdealSheafData)
    (i j k : X.affineOpens) :
    tripleOverlapTransition I i j k ≫ tripleOverlapToBase I j k i
      = tripleOverlapToBase I i j k := by
  rw [overlapPullbackMap_eq, overlapTransPullback_eq, ← Category.assoc, pullback.lift_fst,
    overlapPullbackLift_comp_overlapMap]

private theorem overlapTransPullback_cocycle {X : Scheme.{u}} (I : X.IdealSheafData) (i j k : X.affineOpens) :
    tripleOverlapTransition I i j k ≫ tripleOverlapTransition I j k i ≫ tripleOverlapTransition I k i j
      = 𝟙 (pullback (overlapInclusion I i j) (overlapInclusion I i k)) := by
  have := isOpenImmersion_overlapIncl I i j
  have := isOpenImmersion_overlapIncl I i k
  refine pullback_hom_ext_of_mono (overlapInclusion I i j) (overlapInclusion I i k) ?_
  refine blowupOver_hom_ext (blowupOver_localBlowupMap I i) (tripleOverlapToBase I i j k)
    (isLocallyGeneratedByNonZeroDivisor_comap_overlapPullbackMap I i j k) (range_overlapPullbackMap_subset_source I i j k) ?_ ?_
  · simp only [Category.assoc]
    rw [← overlapMap_eq, ← overlapPullbackMap_eq, overlapTransPullback_comp_overlapPullbackMap,
      overlapTransPullback_comp_overlapPullbackMap, overlapTransPullback_comp_overlapPullbackMap]
  · simp only [Category.id_comp, Category.assoc]
    rw [← overlapMap_eq, ← overlapPullbackMap_eq]

private noncomputable def blowupGlueData {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.GlueData where
  toGlueData :=
    { J := X.affineOpens
      U := fun i => localBlowup I i
      V := fun p => (overlap I p.1 p.2).toScheme
      f := fun i j => overlapInclusion I i j
      f_mono := fun i j => by
        have := isOpenImmersion_overlapIncl I i j
        infer_instance
      f_hasPullback := fun i j k => by
        have := isOpenImmersion_overlapIncl I i j
        have := isOpenImmersion_overlapIncl I i k
        infer_instance
      f_id := fun i => isIso_overlapIncl_self I i
      t := fun i j => overlapTransition I i j
      t_id := fun i => overlapTrans_self I i
      t' := fun i j k => tripleOverlapTransition I i j k
      t_fac := fun i j k => overlapTransPullback_comp_snd I i j k
      cocycle := fun i j k => overlapTransPullback_cocycle I i j k }
  f_open := fun i j => isOpenImmersion_overlapIncl I i j

private noncomputable def gluedBlowup {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.{u} :=
  (blowupGlueData I).glued

private noncomputable def localBlowupToGlued {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) : localBlowup I i ⟶ gluedBlowup I :=
  (blowupGlueData I).ι i

private theorem isOpenImmersion_gluedIncl {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) : IsOpenImmersion (localBlowupToGlued I i) :=
  (blowupGlueData I).ι_isOpenImmersion i

private theorem overlapTrans_comp_gluedIncl {X : Scheme.{u}} (I : X.IdealSheafData) (i j : X.affineOpens) :
    overlapTransition I i j ≫ overlapInclusion I j i ≫ localBlowupToGlued I j
      = overlapInclusion I i j ≫ localBlowupToGlued I i :=
  (blowupGlueData I).glue_condition i j

private theorem gluedIncl_jointly_surjective {X : Scheme.{u}} (I : X.IdealSheafData)
    (p : gluedBlowup I) :
    ∃ (j : X.affineOpens) (y : localBlowup I j), (localBlowupToGlued I j).base y = p := by
  obtain ⟨j, y, hy⟩ := (blowupGlueData I).ι_jointly_surjective p
  exact ⟨j, y, hy⟩

private theorem pullback_fst_comp_localBlowupMap_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (x y : X.affineOpens) :
    pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I x
      = pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I y := by
  obtain ⟨m, hm1, hm2⟩ := PullbackCone.IsLimit.lift' ((blowupGlueData I).vPullbackConeIsLimit x y)
    (pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y))
    (pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y)) pullback.condition
  have e1 : m ≫ overlapInclusion I x y = pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) := hm1
  have e2 : m ≫ (overlapTransition I x y ≫ overlapInclusion I y x)
      = pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) := hm2
  have key : overlapInclusion I x y ≫ localBlowupToBase I x
      = (overlapTransition I x y ≫ overlapInclusion I y x) ≫ localBlowupToBase I y := by
    rw [Category.assoc]
    exact (overlapTrans_comp_overlapMap I x y).symm
  have A : pullback.fst (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I x
      = m ≫ (overlapInclusion I x y ≫ localBlowupToBase I x) :=
    (congrArg (fun t => t ≫ localBlowupToBase I x) e1).symm.trans
      (Category.assoc m (overlapInclusion I x y) (localBlowupToBase I x))
  have B : pullback.snd (localBlowupToGlued I x) (localBlowupToGlued I y) ≫ localBlowupToBase I y
      = m ≫ ((overlapTransition I x y ≫ overlapInclusion I y x) ≫ localBlowupToBase I y) :=
    (congrArg (fun t => t ≫ localBlowupToBase I y) e2).symm.trans
      (Category.assoc m (overlapTransition I x y ≫ overlapInclusion I y x) (localBlowupToBase I y))
  exact A.trans ((congrArg (fun t => m ≫ t) key).trans B.symm)

private noncomputable def gluedBlowupProjection {X : Scheme.{u}} (I : X.IdealSheafData) :
    gluedBlowup I ⟶ X :=
  (blowupGlueData I).openCover.glueMorphisms (fun i => localBlowupToBase I i)
    (fun x y => pullback_fst_comp_localBlowupMap_eq I x y)

private theorem gluedIncl_comp_gluedProj {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) : localBlowupToGlued I i ≫ gluedBlowupProjection I = localBlowupToBase I i :=
  (blowupGlueData I).openCover.ι_glueMorphisms _ _ i

private theorem gluedProj_base_gluedIncl {X : Scheme.{u}} (I : X.IdealSheafData)
    (i : X.affineOpens) (v : localBlowup I i) :
    (gluedBlowupProjection I).base ((localBlowupToGlued I i).base v) = (localBlowupToBase I i).base v := by
  rw [← comp_base_apply, gluedIncl_comp_gluedProj]

private theorem mem_range_gluedIncl_of_mem {X : Scheme.{u}} (I : X.IdealSheafData) (i : X.affineOpens)
    (p : gluedBlowup I) (hp : (gluedBlowupProjection I).base p ∈ (i : X.Opens)) :
    p ∈ Set.range ⇑(localBlowupToGlued I i).base := by
  obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective I p
  have h1 : (localBlowupToBase I j).base y ∈ (i : X.Opens) := by
    rw [← gluedProj_base_gluedIncl I j y, hy]
    exact hp
  have h2 : y ∈ Set.range ⇑(overlapInclusion I j i).base := by
    rw [overlapIncl_eq, Scheme.Opens.range_ι]
    exact h1
  obtain ⟨v, hv⟩ := h2
  have hcb : (overlapTransition I j i ≫ overlapInclusion I i j ≫ localBlowupToGlued I i).base v
      = (overlapInclusion I j i ≫ localBlowupToGlued I j).base v := by
    rw [overlapTrans_comp_gluedIncl I j i]
  rw [comp_base_apply, comp_base_apply, comp_base_apply] at hcb
  refine ⟨(overlapInclusion I i j).base ((overlapTransition I j i).base v), ?_⟩
  rw [hcb, hv]
  exact hy

private theorem comp_gluedIncl_eq_of_comp_localBlowupMap {X P : Scheme.{u}} (I : X.IdealSheafData)
    (x y : X.affineOpens) (q : P ⟶ X) (hq : IsLocallyGeneratedByNonZeroDivisor (I.comap q))
    (hx : Set.range ⇑q.base ⊆ ((x : X.Opens) : Set X))
    (hy : Set.range ⇑q.base ⊆ ((y : X.Opens) : Set X))
    {ax : P ⟶ localBlowup I x} {ay : P ⟶ localBlowup I y}
    (hax : ax ≫ localBlowupToBase I x = q) (hay : ay ≫ localBlowupToBase I y = q) :
    ax ≫ localBlowupToGlued I x = ay ≫ localBlowupToGlued I y := by
  have hxy : Set.range ⇑q.base ⊆ (((x : X.Opens) ⊓ (y : X.Opens)) : Set X) :=
    fun w hw => TopologicalSpace.Opens.mem_inf.mpr ⟨hx hw, hy hw⟩
  have hb1 : liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I x y) q hq hxy ≫ overlapToBase I x y = q :=
    blowupOverLift_comp _ _ _ _
  have e1 : ax = liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I x y) q hq hxy ≫ overlapInclusion I x y := by
    refine blowupOver_hom_ext (blowupOver_localBlowupMap I x) q hq hx hax ?_
    rw [Category.assoc, ← overlapMap_eq, hb1]
  have e2 : ay = (liftOfIsBlowupAlongIdealSheafOver (blowupOver_overlapMap I x y) q hq hxy ≫ overlapTransition I x y)
      ≫ overlapInclusion I y x := by
    refine blowupOver_hom_ext (blowupOver_localBlowupMap I y) q hq hy hay ?_
    rw [Category.assoc, ← overlapMap_eq, Category.assoc, overlapTrans_comp_overlapMap, hb1]
  rw [e1, e2]
  simp only [Category.assoc, ← overlapTrans_comp_gluedIncl I x y]

private noncomputable def preimageAffineOpen {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    W.Opens :=
  g ⁻¹ᵁ (i : X.Opens)

private noncomputable def preimageAffineOpenToBase {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    (preimageAffineOpen g i).toScheme ⟶ X :=
  (preimageAffineOpen g i).ι ≫ g

private theorem preimageAffineOpenToBase_eq {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    preimageAffineOpenToBase g i = (preimageAffineOpen g i).ι ≫ g := rfl

private theorem isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    IsLocallyGeneratedByNonZeroDivisor (I.comap (preimageAffineOpenToBase g i)) :=
  isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ g hg

private theorem range_preimageAffineOpenToBase_subset {X W : Scheme.{u}} (g : W ⟶ X) (i : X.affineOpens) :
    Set.range ⇑(preimageAffineOpenToBase g i).base ⊆ ((i : X.Opens) : Set X) := by
  rintro _ ⟨p, rfl⟩
  rw [preimageAffineOpenToBase_eq, comp_base_apply]
  exact ι_base_mem (preimageAffineOpen g i) p

private noncomputable def localBlowupLift {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    (preimageAffineOpen g i).toScheme ⟶ localBlowup I i :=
  liftOfIsBlowupAlongIdealSheafOver (blowupOver_localBlowupMap I i) (preimageAffineOpenToBase g i) (isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase I g hg i)
    (range_preimageAffineOpenToBase_subset g i)

private theorem liftChart_comp_localBlowupMap {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    localBlowupLift I g hg i ≫ localBlowupToBase I i = preimageAffineOpenToBase g i :=
  blowupOverLift_comp _ _ _ _

private noncomputable def preimageAffineOpensCover {X W : Scheme.{u}} (g : W ⟶ X) : W.OpenCover :=
  Scheme.Cover.mkOfCovers X.affineOpens (fun i => (preimageAffineOpen g i).toScheme)
    (fun i => (preimageAffineOpen g i).ι)
    (fun w => by
      obtain ⟨i, hi⟩ := X.exists_affineOpens_mem (g.base w)
      have hw : w ∈ Set.range ⇑(preimageAffineOpen g i).ι.base := by
        rw [Scheme.Opens.range_ι]
        exact hi
      obtain ⟨v, hv⟩ := hw
      exact ⟨i, v, hv⟩)

private theorem hom_ext_of_preimageAffineOpen_ι_comp {X W : Scheme.{u}} (g : W ⟶ X) {Z : Scheme.{u}} (a b : W ⟶ Z)
    (h : ∀ i : X.affineOpens, (preimageAffineOpen g i).ι ≫ a = (preimageAffineOpen g i).ι ≫ b) : a = b := by
  refine (preimageAffineOpensCover g).hom_ext a b (fun i => ?_)
  exact h i

private theorem liftChart_pullback_condition {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (x y : X.affineOpens) :
    pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ (localBlowupLift I g hg x ≫ localBlowupToGlued I x)
      = pullback.snd (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι
        ≫ (localBlowupLift I g hg y ≫ localBlowupToGlued I y) := by
  have hxy : pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x
      = pullback.snd (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g y := by
    rw [preimageAffineOpenToBase_eq, preimageAffineOpenToBase_eq, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hcart : IsLocallyGeneratedByNonZeroDivisor (I.comap
      (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x)) := by
    have h : pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x
        = (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ (preimageAffineOpen g x).ι) ≫ g := by
      rw [preimageAffineOpenToBase_eq, Category.assoc]
    rw [h]
    exact isLocallyGeneratedByNonZeroDivisor_comap_openImmersion_comp I _ g hg
  have hrx : Set.range ⇑(pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x).base
      ⊆ ((x : X.Opens) : Set X) := by
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply]
    exact range_preimageAffineOpenToBase_subset g x (Set.mem_range_self _)
  have hry : Set.range ⇑(pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x).base
      ⊆ ((y : X.Opens) : Set X) := by
    rw [hxy]
    rintro _ ⟨p, rfl⟩
    rw [comp_base_apply]
    exact range_preimageAffineOpenToBase_subset g y (Set.mem_range_self _)
  rw [← Category.assoc, ← Category.assoc]
  refine comp_gluedIncl_eq_of_comp_localBlowupMap I x y
    (pullback.fst (preimageAffineOpen g x).ι (preimageAffineOpen g y).ι ≫ preimageAffineOpenToBase g x) hcart hrx hry ?_ ?_
  · rw [Category.assoc, liftChart_comp_localBlowupMap]
  · rw [Category.assoc, liftChart_comp_localBlowupMap, hxy]

private noncomputable def gluedBlowupLift {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) : W ⟶ gluedBlowup I :=
  (preimageAffineOpensCover g).glueMorphisms (fun i => localBlowupLift I g hg i ≫ localBlowupToGlued I i)
    (fun x y => liftChart_pullback_condition I g hg x y)

private theorem ι_comp_liftGlued {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (i : X.affineOpens) :
    (preimageAffineOpen g i).ι ≫ gluedBlowupLift I g hg = localBlowupLift I g hg i ≫ localBlowupToGlued I i :=
  (preimageAffineOpensCover g).ι_glueMorphisms _ _ i

private theorem liftGlued_comp_gluedProj {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) : gluedBlowupLift I g hg ≫ gluedBlowupProjection I = g := by
  refine hom_ext_of_preimageAffineOpen_ι_comp g (gluedBlowupLift I g hg ≫ gluedBlowupProjection I) g (fun i => ?_)
  rw [← Category.assoc, ι_comp_liftGlued, Category.assoc, gluedIncl_comp_gluedProj, liftChart_comp_localBlowupMap,
    preimageAffineOpenToBase_eq]

private theorem eq_liftGlued_of_comp_eq {X W : Scheme.{u}} (I : X.IdealSheafData) (g : W ⟶ X)
    (hg : IsLocallyGeneratedByNonZeroDivisor (I.comap g)) (b : W ⟶ gluedBlowup I)
    (hb : b ≫ gluedBlowupProjection I = g) : b = gluedBlowupLift I g hg := by
  refine hom_ext_of_preimageAffineOpen_ι_comp g b (gluedBlowupLift I g hg) (fun i => ?_)
  rw [ι_comp_liftGlued]
  have hr : Set.range ⇑((preimageAffineOpen g i).ι ≫ b).base ⊆ Set.range ⇑(localBlowupToGlued I i).base := by
    rintro _ ⟨p, rfl⟩
    refine mem_range_gluedIncl_of_mem I i _ ?_
    rw [← comp_base_apply, Category.assoc, hb]
    exact range_preimageAffineOpenToBase_subset g i (Set.mem_range_self p)
  have := isOpenImmersion_gluedIncl I i
  have hc : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr ≫ localBlowupToGlued I i
      = (preimageAffineOpen g i).ι ≫ b := IsOpenImmersion.lift_fac _ _ _
  have hc2 : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr ≫ localBlowupToBase I i
      = preimageAffineOpenToBase g i := by
    rw [← gluedIncl_comp_gluedProj I i, ← Category.assoc, hc, Category.assoc, hb, preimageAffineOpenToBase_eq]
  have hc3 : IsOpenImmersion.lift (localBlowupToGlued I i) ((preimageAffineOpen g i).ι ≫ b) hr
      = localBlowupLift I g hg i :=
    blowupOver_hom_ext (blowupOver_localBlowupMap I i) (preimageAffineOpenToBase g i) (isLocallyGeneratedByNonZeroDivisor_comap_preimageAffineOpenToBase I g hg i)
      (range_preimageAffineOpenToBase_subset g i) hc2 (liftChart_comp_localBlowupMap I g hg i)
  rw [← hc, hc3]

private theorem isBlowupAlongIdealSheaf_gluedProj {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsBlowupAlongIdealSheaf (gluedBlowupProjection I) I := by
  constructor
  · have : ∀ i : X.affineOpens, IsOpenImmersion (localBlowupToGlued I i) := fun i =>
      isOpenImmersion_gluedIncl I i
    refine IsLocallyGeneratedByNonZeroDivisor.of_isOpenImmersion_cover (I.comap (gluedBlowupProjection I))
      (fun i => localBlowup I i) (fun i => localBlowupToGlued I i) ?_ ?_
    · intro p
      obtain ⟨j, y, hy⟩ := gluedIncl_jointly_surjective I p
      exact ⟨j, y, hy⟩
    · intro i
      rw [← Scheme.IdealSheafData.comap_comp, gluedIncl_comp_gluedProj]
      exact (blowupOver_localBlowupMap I i).2.1
  · intro W g hg
    exact ⟨gluedBlowupLift I g hg, liftGlued_comp_gluedProj I g hg,
      fun b hb => eq_liftGlued_of_comp_eq I g hg b hb⟩

theorem exists_isBlowupAlongIdealSheaf (X : Scheme.{u}) (I : X.IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X), IsBlowupAlongIdealSheaf π I :=
  ⟨gluedBlowup I, gluedBlowupProjection I, isBlowupAlongIdealSheaf_gluedProj I⟩

noncomputable section

noncomputable def blowup {X : Scheme.{u}} (I : X.IdealSheafData) : Scheme.{u} :=
  (exists_isBlowupAlongIdealSheaf X I).choose

noncomputable def blowup.proj {X : Scheme.{u}} (I : X.IdealSheafData) : blowup I ⟶ X :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose

end

theorem blowup.isBlowupAlongIdealSheaf_proj {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsBlowupAlongIdealSheaf (blowup.proj I) I :=
  (exists_isBlowupAlongIdealSheaf X I).choose_spec.choose_spec

end FunctorialResolution.Blowup
