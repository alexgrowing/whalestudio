import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.Blowup

universe u

variable {R : Type u} [CommRing R]

def specIdealSheaf (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)

theorem specIdealSheaf_eq_ofIdealTop (I : Ideal R) :
    specIdealSheaf I =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I) := rfl

theorem specIdealSheaf_ideal_top (I : Ideal R) :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I :=
  Scheme.IdealSheafData.ofIdealTop_ideal_top _

def chartSectionsIso (I : Ideal R) (a : ↥I) :
    CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) ≅
      Γ(affineBlowup I, affineBlowupChart I a ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso
      (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).symm ≪≫
    ((affineBlowupChart I a).appIso ⊤).symm

theorem chartSectionsIso_hom (I : Ideal R) (a : ↥I) :
    (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv ≫
        ((affineBlowupChart I a).appIso ⊤).inv := rfl

theorem chartSectionsIso_hom_apply (I : Ideal R) (a : ↥I)
    (x : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    (chartSectionsIso I a).hom.hom x =
      ((affineBlowupChart I a).appIso ⊤).inv.hom
        ((Scheme.ΓSpecIso
            (CommRingCat.of
              (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv.hom x) := rfl

private theorem comp_presheaf_map_eq_of_heq {Z : Scheme.{u}} {A : CommRingCat.{u}} (U : Z.Opens) (hU : U = ⊤)
    (φ : A ⟶ Γ(Z, U)) (h : (⊤ : Z.Opens) ≤ U) (ψ : A ⟶ Γ(Z, (⊤ : Z.Opens)))
    (hφ : HEq φ ψ) : φ ≫ Z.presheaf.map (homOfLE h).op = ψ := by
  subst hU
  obtain rfl : φ = ψ := eq_of_heq hφ
  rw [show (homOfLE h : (⊤ : Z.Opens) ⟶ ⊤) = 𝟙 (⊤ : Z.Opens) from rfl]
  simp

private theorem appTop_eq_appLE_top_top {Z S : Scheme.{u}} (f : Z ⟶ S)
    (h : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  comp_presheaf_map_eq_of_heq (f ⁻¹ᵁ (⊤ : S.Opens)) (le_antisymm le_top h) (f.app ⊤) h f.appTop HEq.rfl

private theorem appLE_image_top_comp_appIso_hom {Z X S : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] (p : X ⟶ S)
    (e : (g ''ᵁ (⊤ : Z.Opens)) ≤ p ⁻¹ᵁ (⊤ : S.Opens)) :
    p.appLE ⊤ (g ''ᵁ ⊤) e ≫ (g.appIso ⊤).hom = (g ≫ p).appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  exact appTop_eq_appLE_top_top (g ≫ p) _

theorem chartRingHom_comp_chartSectionsIso_hom (I : Ideal R) (a : ↥I) :
    CommRingCat.ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm) := by
  rw [chartSectionsIso_hom, ← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    appLE_image_top_comp_appIso_hom, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  exact Scheme.ΓSpecIso_inv_naturality _

theorem ideal_comap_toSpec_chart_eq_span (I : Ideal R) (a : ↥I)
    (hW : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (AffineBlowup.toSpec I)).ideal ⟨_, hW⟩ =
      Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
  have hcomp := congrArg CommRingCat.Hom.hom (chartRingHom_comp_chartSectionsIso_hom I a)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hcomp
  have key : Ideal.map ((AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
        (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)).hom
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)
      = Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map, map_chartRingHom_eq_span_singleton, Ideal.map_span,
      Set.image_singleton]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) (AffineBlowup.toSpec I)
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ ⟨_, hW⟩
      (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)]
  rw [specIdealSheaf_ideal_top]
  exact key

theorem isLocallyGeneratedByNonZeroDivisor_comap_toSpec (I : Ideal R) :
    IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (AffineBlowup.toSpec I)) := by
  intro x
  obtain ⟨a, hx⟩ : ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base :=
    ⟨(affineBlowupAffineOpenCover I).idx x, (affineBlowupAffineOpenCover I).covers x⟩
  have hW := (isAffineOpen_top (Spec (CommRingCat.of
      (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))))).image_of_isOpenImmersion
      (affineBlowupChart I a)
  refine ⟨⟨_, hW⟩, (chartSectionsIso I a).hom.hom (chartRingHom I a (a : R)), ?_, ?_,
    ideal_comap_toSpec_chart_eq_span I a hW⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, trivial, hy⟩
  · exact map_mem_nonZeroDivisors_of_iso (chartSectionsIso I a) (chartRingHom_mem_nonZeroDivisors I a)

end FunctorialResolution.Blowup
