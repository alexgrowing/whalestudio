import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem ker_le_ker_of_comp_eq {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    (h : e ≫ g = f) : g.ker ≤ f.ker := by
  subst h
  exact Scheme.Hom.le_ker_comp e g

theorem comap_strictTransform_of_iso {X X₁ X₁' : Scheme.{u}} (π : X₁ ⟶ X)
    (f : X₁' ≅ X₁) (Z D : X.IdealSheafData) (_hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π))
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι (f.hom ≫ π) Z D)] :
    (Blowup.strictTransform π Z D).comap f.hom = Blowup.strictTransform (f.hom ≫ π) Z D := by
  have hRHS : Blowup.strictTransform (f.hom ≫ π) Z D
      = Blowup.strictTransform f.hom (Z.comap π) (D.comap π) :=
    strictTransform_eq_of_comap_eq (f.hom ≫ π) f.hom Z D (Z.comap π) (D.comap π)
      (by rw [Scheme.IdealSheafData.comap_comp])
      (by rw [Scheme.IdealSheafData.comap_comp])
  obtain ⟨m₀, hiso, hm₀⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso f.hom (D.comap π)
  have := hiso
  have hsupp : ((Z.comap π).comap f.hom).support.compl
      = f.hom ⁻¹ᵁ (Z.comap π).support.compl := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have h1 : m₀ ⁻¹ᵁ strictTransformOpens π Z D
      = ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ (f.hom ⁻¹ᵁ (Z.comap π).support.compl) :=
    congrArg (fun w => w ⁻¹ᵁ (Z.comap π).support.compl) hm₀
  have hV' : strictTransformOpens f.hom (Z.comap π) (D.comap π)
      = m₀ ⁻¹ᵁ strictTransformOpens π Z D := by
    rw [h1]
    exact congrArg (fun W => ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ W) hsupp
  have hm₀2 : m₀ ≫ ((D.comap π).subschemeι ≫ inv f.hom)
      = ((D.comap π).comap f.hom).subschemeι := by
    rw [← Category.assoc, hm₀, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm₀3 : inv m₀ ≫ ((D.comap π).comap f.hom).subschemeι
      = (D.comap π).subschemeι ≫ inv f.hom := by
    rw [IsIso.inv_comp_eq, hm₀2]
  have hinvle : strictTransformOpens π Z D
      ≤ inv m₀ ⁻¹ᵁ strictTransformOpens f.hom (Z.comap π) (D.comap π) := by
    rw [hV']
    have h3 : inv m₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ strictTransformOpens π Z D)
        = (inv m₀ ≫ m₀) ⁻¹ᵁ strictTransformOpens π Z D := rfl
    rw [h3, IsIso.inv_hom_id]
    simp
  have hfac1 : (Scheme.Hom.resLE m₀ (strictTransformOpens π Z D)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π)) (le_of_eq hV'))
      ≫ (strictTransformι π Z D ≫ inv f.hom)
      = strictTransformι f.hom (Z.comap π) (D.comap π) := by
    rw [strictTransformι_eq_ι_comp_subschemeι π Z D,
      strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc, hm₀2]
  have hfac2 : (Scheme.Hom.resLE (inv m₀)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π))
        (strictTransformOpens π Z D) hinvle)
      ≫ strictTransformι f.hom (Z.comap π) (D.comap π)
      = strictTransformι π Z D ≫ inv f.hom := by
    rw [strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      strictTransformι_eq_ι_comp_subschemeι π Z D, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hm₀3, Category.assoc]
  have hcomp : (strictTransformι π Z D ≫ inv f.hom) ≫ f.hom
      = strictTransformι π Z D := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : QuasiCompact (strictTransformι π Z D ≫ inv f.hom) := inferInstance
  have : QuasiCompact ((strictTransformι π Z D ≫ inv f.hom) ≫ f.hom) := by
    rw [hcomp]
    infer_instance
  have hL := Blowup.comap_ker_comp_of_isOpenImmersion
    (strictTransformι π Z D ≫ inv f.hom) f.hom
  rw [hcomp] at hL
  rw [hRHS, strictTransform_eq_ker_strictTransformι π Z D, hL,
    strictTransform_eq_ker_strictTransformι f.hom (Z.comap π) (D.comap π)]
  exact le_antisymm (ker_le_ker_of_comp_eq _ _ _ hfac1) (ker_le_ker_of_comp_eq _ _ _ hfac2)

theorem exists_iso_subscheme_of_ker_eq_strictTransform {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι)) :
    ∃ (e : S ≅ (Scheme.Hom.ker ι).subscheme)
      (e₁ : S₁ ≅ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme),
      e.hom ≫ (Scheme.Hom.ker ι).subschemeι = ι ∧
        e₁.hom ≫ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ ∧
        e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) = ρ ≫ e.hom := by
  have hkH : (Scheme.Hom.ker ι).subschemeι.ker = Scheme.Hom.ker ι :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hkT : (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι.ker
      = Blowup.strictTransform π Z (Scheme.Hom.ker ι) :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hu : IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH) ≫
      (Scheme.Hom.ker ι).subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)) :=
    IsClosedImmersion.isIso_of_ker_eq ι (Scheme.Hom.ker ι).subschemeι _ hu hkH.symm
  have hu₁ : IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
        (le_of_eq (hkT.trans hker.symm)) ≫
      (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))) :=
    IsClosedImmersion.isIso_of_ker_eq ι₁ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι _
      hu₁ (hker.trans hkT.symm)
  refine ⟨asIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)),
    asIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))), hu, hu₁, ?_⟩
  rw [← cancel_mono (Scheme.Hom.ker ι).subschemeι, Category.assoc,
    strictTransformSubschemeLift_comp_subschemeι π Z (Scheme.Hom.ker ι), ← Category.assoc]
  simp only [asIso_hom]
  rw [hu₁, Category.assoc, hu, hsq]

theorem comap_strictTransform_of_closedImmersion_commSq {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap ι₁ =
      Blowup.strictTransform ρ (Z.comap ι) (D.comap ι) := by
  obtain ⟨e, e₁, he, he₁, hcomm⟩ :=
    exists_iso_subscheme_of_ker_eq_strictTransform π Z ι ι₁ ρ hsq hker
  have : IsLocallyNoetherian (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme :=
    isLocallyNoetherian_subscheme _
  have hq := isBlowupAlongIdealSheaf_strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) hπ
  have hfinal : (e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) ≫
      (Scheme.Hom.ker ι).subschemeι = ρ ≫ ι := by
    rw [Category.assoc, strictTransformSubschemeLift_comp_subschemeι, ← Category.assoc, he₁, hsq]
  have hmain := comap_strictTransform_eq_strictTransformSubschemeLift p π Z (Scheme.Hom.ker ι) E hsnc hHZ hπ D hD
  have h1 : (Blowup.strictTransform π Z D).comap ι₁
      = ((Blowup.strictTransform π Z D).comap
          (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι).comap e₁.hom := by
    rw [← he₁, Scheme.IdealSheafData.comap_comp]
  rw [h1, hmain, comap_strictTransform_of_iso
    (strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) e₁ (Z.comap (Scheme.Hom.ker ι).subschemeι)
    (D.comap (Scheme.Hom.ker ι).subschemeι) hq.1]
  refine strictTransform_eq_of_comap_eq _ ρ _ _ _ _ ?_ ?_
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]

theorem comap_exceptionalIdeal_of_commSq {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S) (hsq : ι₁ ≫ π = ρ ≫ ι)
    (Z : X.IdealSheafData) :
    (Blowup.exceptionalIdeal π Z).comap ι₁ = Blowup.exceptionalIdeal ρ (Z.comap ι) := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

theorem map_comap_strictTransform_append_exceptionalIdeal {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (List.map (Blowup.strictTransform π Z) E ++ [Blowup.exceptionalIdeal π Z]).map
        (fun A => A.comap ι₁) =
      List.map (Blowup.strictTransform ρ (Z.comap ι)) (List.map (fun D => D.comap ι) E) ++
        [Blowup.exceptionalIdeal ρ (Z.comap ι)] := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left ?_
    intro D hD
    exact comap_strictTransform_of_closedImmersion_commSq p π Z ι ι₁ ρ hsq hker E hsnc hHZ hπ D hD
  · rw [comap_exceptionalIdeal_of_commSq π ι ι₁ ρ hsq Z]

end FunctorialResolution.EmbeddedResolution

end
