import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace HasSmoothCoordCodim

variable {k : Type u} [Field k]

private theorem smooth_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f]
    (U : Y.Opens) : AlgebraicGeometry.Smooth (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth)
    (isPullback_morphismRestrict f U).flip ‹AlgebraicGeometry.Smooth f›

private theorem resLE_comp_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  simp [Scheme.Hom.resLE_comp_ι]

private theorem ker_eq_comap_of_isPullback {X X' X'' X₂ : Scheme.{u}} {τ : X ⟶ X'} [IsClosedImmersion τ]
    {g : X'' ⟶ X'} {τ'' : X₂ ⟶ X''} {p : X₂ ⟶ X} (H : IsPullback p τ'' τ g) :
    τ''.ker = τ.ker.comap g := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion τ g, ← H.flip.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

private theorem ker_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) :
    (f.resLE U (f ⁻¹ᵁ U) le_rfl).ker = f.ker.comap U.ι := by
  have H := (isPullback_morphismRestrict f U).flip
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact ker_eq_comap_of_isPullback H

private theorem ker_comp_iso {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (φ : Y ≅ Z) :
    (f ≫ φ.hom).ker = f.ker.comap φ.inv :=
  ker_eq_comap_of_isPullback (p := 𝟙 X) (IsPullback.of_horiz_isIso ⟨by simp⟩)

theorem resLE_open {X X' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (O : X'.Opens) :
    HasSmoothCoordCodim (O.ι ≫ s) (τ.resLE O (τ ⁻¹ᵁ O) le_rfl) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h ((τ ⁻¹ᵁ O).ι.base x)
  have : AlgebraicGeometry.Smooth q := hq
  have : AlgebraicGeometry.Smooth O.ι := inferInstance
  have : AlgebraicGeometry.Smooth (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := smooth_resLE O.ι U
  have hw : O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) = τ.base ((τ ⁻¹ᵁ O).ι.base x) :=
    congrArg (fun m : (τ ⁻¹ᵁ O).toScheme ⟶ X' => m.base x) (resLE_comp_ι τ O)
  refine ⟨O.ι ⁻¹ᵁ U, ?_, O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show O.ι.base ((τ.resLE O (τ ⁻¹ᵁ O) le_rfl).base x) ∈ U
    rw [hw]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι O.ι U, Category.assoc]
  · calc restrictIdeal (τ.resLE O (τ ⁻¹ᵁ O) le_rfl).ker (O.ι ⁻¹ᵁ U)
        = (τ.ker.comap O.ι).comap (O.ι ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_resLE]
      _ = τ.ker.comap ((O.ι ⁻¹ᵁ U).ι ≫ O.ι) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ U.ι) := by rw [resLE_comp_ι O.ι U]
      _ = (τ.ker.comap U.ι).comap (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (O.ι.resLE U (O.ι ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]

theorem comp_iso_hom {X X' X'' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (φ : X' ≅ X'')
    (s' : X'' ⟶ Spec (CommRingCat.of k)) (hφ : φ.hom ≫ s' = s) :
    HasSmoothCoordCodim s' (τ ≫ φ.hom) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h x
  have : AlgebraicGeometry.Smooth q := hq
  have : AlgebraicGeometry.Smooth φ.inv := inferInstance
  have : AlgebraicGeometry.Smooth (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := smooth_resLE φ.inv U
  have hs' : φ.inv ≫ s = s' := by rw [← hφ, Iso.inv_hom_id_assoc]
  refine ⟨φ.inv ⁻¹ᵁ U, ?_, φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q, inferInstance, ?_, ?_⟩
  · show φ.inv.base ((τ ≫ φ.hom).base x) ∈ U
    have hb : φ.inv.base ((τ ≫ φ.hom).base x) = τ.base x :=
      congrArg (fun m : X ⟶ X' => m.base x) (by simp : (τ ≫ φ.hom) ≫ φ.inv = τ)
    rw [hb]
    exact hU
  · rw [Category.assoc, hqs, ← Category.assoc, resLE_comp_ι φ.inv U, Category.assoc, hs']
  · calc restrictIdeal (τ ≫ φ.hom).ker (φ.inv ⁻¹ᵁ U)
        = (τ.ker.comap φ.inv).comap (φ.inv ⁻¹ᵁ U).ι := by
          rw [restrictIdeal_eq_comap_ι, ker_comp_iso]
      _ = τ.ker.comap ((φ.inv ⁻¹ᵁ U).ι ≫ φ.inv) := by rw [Scheme.IdealSheafData.comap_comp]
      _ = τ.ker.comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ U.ι) := by
          rw [resLE_comp_ι φ.inv U]
      _ = (τ.ker.comap U.ι).comap (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by
          rw [Scheme.IdealSheafData.comap_comp]
      _ = ((coordSubspaceIdeal k c Finset.univ).comap q).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl) := by rw [← restrictIdeal_eq_comap_ι, hker]
      _ = (coordSubspaceIdeal k c Finset.univ).comap
            (φ.inv.resLE U (φ.inv ⁻¹ᵁ U) le_rfl ≫ q) := by rw [Scheme.IdealSheafData.comap_comp]

theorem iso_hom_comp {X X' X₀ : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (e : X₀ ≅ X) :
    HasSmoothCoordCodim s (e.hom ≫ τ) c := by
  intro x
  obtain ⟨U, hU, q, hq, hqs, hker⟩ := h (e.hom.base x)
  refine ⟨U, hU, q, hq, hqs, ?_⟩
  rw [restrictIdeal_eq_comap_ι, Scheme.Hom.ker_comp_of_isIso, ← restrictIdeal_eq_comap_ι, hker]

end HasSmoothCoordCodim

end FunctorialResolution.EmbeddedResolution

end
