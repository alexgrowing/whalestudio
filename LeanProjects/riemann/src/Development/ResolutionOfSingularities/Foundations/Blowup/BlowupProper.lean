import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

private theorem ofIdealTop_ideal_top_eq_self {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
      (I.ideal ⟨⊤, isAffineOpen_top X⟩) = I :=
  Scheme.IdealSheafData.ext_of_isAffine (by simp)

private theorem map_inv_map_hom_eq_self {A B : CommRingCat.{u}} (e : A ≅ B) (K : Ideal ↑A) :
    Ideal.map (CommRingCat.Hom.hom e.inv) (Ideal.map (CommRingCat.Hom.hom e.hom) K) = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

private theorem exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (CommRingCat.of A)),
      IsBlowupAlongIdealSheaf π I ∧ AlgebraicGeometry.IsProper π := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, FunctorialResolution.Blowup.specIdealSheaf J = I := by
    refine ⟨Ideal.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
      (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩), ?_⟩
    rw [FunctorialResolution.Blowup.specIdealSheaf_eq_ofIdealTop, map_inv_map_hom_eq_self (Scheme.ΓSpecIso (CommRingCat.of A))]
    exact ofIdealTop_ideal_top_eq_self I
  refine ⟨FunctorialResolution.Blowup.affineBlowup J, FunctorialResolution.Blowup.AffineBlowup.toSpec J, ?_,
    FunctorialResolution.Blowup.isProper_affineBlowup_toSpec J⟩
  rw [← hJ]
  exact FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec J

theorem exists_isBlowupAlongIdealSheaf_isProper_spec (R : CommRingCat.{u}) [IsNoetherianRing ↑R]
    (I : (Spec R).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec R), IsBlowupAlongIdealSheaf π I ∧ AlgebraicGeometry.IsProper π :=
  exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (↑R) I

theorem isProper_of_isBlowupAlongIdealSheaf_of_isAffine {Y B : Scheme.{u}} [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Y.IdealSheafData) {p : B ⟶ Y} (h : IsBlowupAlongIdealSheaf p J) :
    AlgebraicGeometry.IsProper p := by
  obtain ⟨Y', π, hπ, hproper⟩ :=
    exists_isBlowupAlongIdealSheaf_isProper_spec Γ(Y, ⊤) (J.comap Y.isoSpec.inv)
  have hq : IsBlowupAlongIdealSheaf (p ≫ Y.isoSpec.hom) (J.comap Y.isoSpec.inv) := h.comp_iso_hom Y.isoSpec
  obtain ⟨b, hb⟩ := hπ.exists_lift (p ≫ Y.isoSpec.hom) hq.1
  obtain ⟨a, ha⟩ := hq.exists_lift π hπ.1
  have hab : a ≫ b = 𝟙 Y' := by
    refine hπ.hom_ext hπ.1 ?_ ?_
    · rw [Category.assoc, hb, ha]
    · rw [Category.id_comp]
  have hba : b ≫ a = 𝟙 B := by
    refine hq.hom_ext hq.1 ?_ ?_
    · rw [Category.assoc, ha, hb]
    · rw [Category.id_comp]
  have : IsIso b := ⟨a, hba, hab⟩
  have : AlgebraicGeometry.IsProper π := hproper
  have hp : b ≫ π ≫ Y.isoSpec.inv = p := by
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hp]
  infer_instance

private theorem isProper_morphismRestrict_of_isProper_pullbackSnd {X X' : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) (h : AlgebraicGeometry.IsProper (pullback.snd f U.ι)) :
    AlgebraicGeometry.IsProper (AlgebraicGeometry.morphismRestrict f U) := by
  have key : (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
      AlgebraicGeometry.morphismRestrict f U = pullback.snd f U.ι := by
    simp [AlgebraicGeometry.morphismRestrict]
  have h2 : AlgebraicGeometry.IsProper
      ((AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
        AlgebraicGeometry.morphismRestrict f U) := by
    rw [key]; exact h
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.IsProper)
    (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom
    (AlgebraicGeometry.morphismRestrict f U)).mp h2

private theorem isNoetherianRing_sections_top_of_affineOpen {X : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := by
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv ((U : X.Opens).topIso)).symm

theorem blowupIsProper : BlowupIsProper.{u} := by
  intro X X' hX π Z hZ
  have := hX
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.IsProper)
    (fun U : X.affineOpens => (U : X.Opens)) (AlgebraicGeometry.iSup_affineOpens_eq_top X) ?_
  intro U
  have : AlgebraicGeometry.IsAffine (U : X.Opens).toScheme := U.2
  have : IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := isNoetherianRing_sections_top_of_affineOpen U
  exact isProper_morphismRestrict_of_isProper_pullbackSnd π (U : X.Opens)
    (isProper_of_isBlowupAlongIdealSheaf_of_isAffine (Z.comap (U : X.Opens).ι)
      (hZ.pullback_snd_of_isOpenImmersion (U : X.Opens).ι))

theorem isProper_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.IsProper π :=
  blowupIsProper X X' π I h

theorem locallyOfFiniteType_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.LocallyOfFiniteType π := by
  have := isProper_of_isBlowupAlongIdealSheaf h
  infer_instance

theorem quasiCompact_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.QuasiCompact π := by
  have := isProper_of_isBlowupAlongIdealSheaf h
  infer_instance

end FunctorialResolution.Blowup
