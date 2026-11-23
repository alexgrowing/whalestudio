import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem map_maximalIdeal_le_maximalIdeal_of_retraction {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R) :
    Ideal.map f (IsLocalRing.maximalIdeal R) ≤ IsLocalRing.maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hx
  have h3 : g (f x) = x := by
    rw [← RingHom.comp_apply, hgf, RingHom.id_apply]
  have h2 := hu.map g
  rwa [h3] at h2

theorem idealOrder_map_eq_of_comp_eq_id {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) (g : S →+* R)
    (hgf : g.comp f = RingHom.id R) (hfg : f.comp g = RingHom.id S) (I : Ideal R) :
    idealOrder (Ideal.map f I) = idealOrder I := by
  have hf := map_maximalIdeal_le_maximalIdeal_of_retraction f g hgf
  have hg := map_maximalIdeal_le_maximalIdeal_of_retraction g f hfg
  have h1 := idealOrder_le_idealOrder_map f hf I
  have h3 := idealOrder_le_idealOrder_map g hg (Ideal.map f I)
  rw [Ideal.map_map, hgf, Ideal.map_id] at h3
  exact le_antisymm h3 h1

theorem orderAt_comap_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (J : Y.IdealSheafData)
    (x : X) [IsIso (f.stalkMap x)] :
    orderAt (J.comap f) x = orderAt J (f.base x) := by
  have hgf : ((inv (f.stalkMap x)).hom).comp ((f.stalkMap x).hom) = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom (IsIso.hom_inv_id (f.stalkMap x))
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  have hfg : ((f.stalkMap x).hom).comp ((inv (f.stalkMap x)).hom) = RingHom.id _ := by
    have h := congrArg CommRingCat.Hom.hom (IsIso.inv_hom_id (f.stalkMap x))
    rwa [CommRingCat.hom_comp, CommRingCat.hom_id] at h
  simp only [orderAt_eq_idealOrder]
  rw [stalkIdeal_comap]
  exact idealOrder_map_eq_of_comp_eq_id _ _ hgf hfg _

theorem isIso_stalkMap_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x : X₁) (hx : π.base x ∉ Z.support) :
    IsIso (π.stalkMap x) := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hoi : IsOpenImmersion (π ∣_ Z.support.compl) := IsOpenImmersion.of_isIso _
  have hxV : x ∈ π ⁻¹ᵁ Z.support.compl := hx
  let y : ↥((π ⁻¹ᵁ Z.support.compl).toScheme) := ⟨x, hxV⟩
  have hs2 : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := inferInstance
  have hoi2 : IsOpenImmersion
      ((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl) := inferInstance
  have hB : IsIso (((π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl).stalkMap y) :=
    inferInstance
  have hcomp : Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π
      = (π ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl :=
    (morphismRestrict_ι π Z.support.compl).symm
  have hA : IsIso ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y) := by
    rw [hcomp]
    exact hB
  have e2 : (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl) ≫ π).stalkMap y
      = π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
        ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y := Scheme.Hom.stalkMap_comp _ _ _
  have hC : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [e2] at hA
    exact hA
  have hr : π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
      = (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)
          ≫ (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y)
        ≫ inv ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).stalkMap y) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hfin : IsIso (π.stalkMap ((Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl)).base y)) := by
    rw [hr]
    infer_instance
  exact hfin

namespace OrderLocusBlowup

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData)
    (μ : ℕ) (hA : Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π)
    (hZ : (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ) :
    orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ := by
  intro x hx
  by_cases hxZ : π.base x ∈ Z.support
  · exact hZ hxZ
  · have := isIso_stalkMap_of_isBlowupAlongIdealSheaf π Z hπ x hxZ
    have hle : stalkIdeal (A.comap π) x ≤ stalkIdeal A₁ x := by
      rw [← hA, stalkIdeal_mul]
      exact le_trans Ideal.mul_le_inf inf_le_right
    have h2 : orderAt A₁ x ≤ orderAt (A.comap π) x := idealOrder_le_of_le hle
    have h3 : orderAt (A.comap π) x = orderAt A (π.base x) :=
      orderAt_comap_of_isIso_stalkMap π A x
    show (μ : ℕ∞) ≤ orderAt A (π.base x)
    calc (μ : ℕ∞) ≤ orderAt A₁ x := hx
      _ ≤ orderAt (A.comap π) x := h2
      _ = orderAt A (π.base x) := h3

end OrderLocusBlowup

end FunctorialResolution.EmbeddedResolution
