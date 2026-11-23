import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenterGeometry

theorem isClosed_sUnion_intersectionComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsClosed (⋃₀ 𝒞) := by
  classical
  have hfin : 𝒞.Finite := Set.Finite.subset (intersectionComponents_finite T hT J) h𝒞
  rw [Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion
    (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))

theorem isClosed_componentUnionOpens (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    IsClosed ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) := by
  have hK : IsClosed (⋃₀ 𝒞) := isClosed_sUnion_intersectionComponents T hT J 𝒞 h𝒞
  have h1 : IsOpen ((⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)ᶜ) := by
    rw [← Set.preimage_compl]
    exact ((intersectionIdeal T.boundary J).subschemeι ⁻¹ᵁ ⟨(⋃₀ 𝒞)ᶜ, hK.isOpen_compl⟩).isOpen
  exact isOpen_compl_iff.mp h1

theorem componentUnionIdeal_eq_openSubschemeKer (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    componentUnionIdeal T.boundary J 𝒞 hop
      = openSubschemeKer (intersectionIdeal T.boundary J) (componentUnionOpens T.boundary J 𝒞 hop) := by
  rw [componentUnionIdeal_eq_ker, openSubschemeKer_eq_ker]

theorem smooth_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
          AlgebraicGeometry.Smooth
            ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap) := by
  intro T hT J 𝒞 h𝒞 hop
  have hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) :=
    MonomialChart.smooth_intersectionIdeal_subscheme T hT J
  rw [componentUnionIdeal_eq_openSubschemeKer T J 𝒞 hop]
  exact smooth_subschemeι_openSubschemeKer_comp (intersectionIdeal T.boundary J)
    (componentUnionOpens T.boundary J 𝒞 hop)
    (isClosed_componentUnionOpens T hT J 𝒞 h𝒞 hop) T.structMap

theorem hasStrictNormalCrossingsWith_componentUnionIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)),
      ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
        ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
          HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary := by
  classical
  intro T hT J 𝒞 h𝒞 hop
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  have hWcl : IsClosed
      ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) :=
    isClosed_componentUnionOpens T hT J 𝒞 h𝒞 hop
  have hce : componentUnionIdeal T.boundary J 𝒞 hop
      = openSubschemeKer (intersectionIdeal T.boundary J) (componentUnionOpens T.boundary J 𝒞 hop) :=
    componentUnionIdeal_eq_openSubschemeKer T J 𝒞 hop
  have hximg : x ∈ ⇑(intersectionIdeal T.boundary J).subschemeι.base ''
      ((componentUnionOpens T.boundary J 𝒞 hop : Set ↥(intersectionIdeal T.boundary J).subscheme)) := by
    rw [← support_openSubschemeKer (intersectionIdeal T.boundary J)
      (componentUnionOpens T.boundary J 𝒞 hop) hWcl, ← hce]
    exact hx
  obtain ⟨U₁, hxU₁, hU₁⟩ := exists_opens_preimage_subschemeι_le (intersectionIdeal T.boundary J)
    (componentUnionOpens T.boundary J 𝒞 hop) x hximg
  obtain ⟨U₀, hxU₀, m, c₀, a, ha1, ha2, ha3⟩ :=
    (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc).2 x).exists_etaleChart
  have hxV : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
  have hxsupp : x ∈ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) := by
    have hxs : x ∈ ⋃₀ 𝒞 := by
      rw [← componentUnionIdeal_support_eq_sUnion T hT J 𝒞 h𝒞 hop]
      exact hx
    obtain ⟨C, hC, hxC⟩ := hxs
    exact (h𝒞 hC).2.1 hxC
  have hbs : restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁)
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) :=
    MonomialChart.restrictIdeal_biSup_finset (U₀ ⊓ U₁) (fun j => T.boundary.get j) J
  have h4 : restrictIdeal (componentUnionIdeal T.boundary J 𝒞 hop) (U₀ ⊓ U₁)
      = restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁) := by
    rw [hce]
    exact restrictIdeal_openSubschemeKer_of_preimage_le (intersectionIdeal T.boundary J)
      (componentUnionOpens T.boundary J 𝒞 hop) hWcl (U₀ ⊓ U₁)
      (le_trans (Scheme.Hom.preimage_mono _ inf_le_right) hU₁)
  have hJsome : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    by_cases hn : a (j : ℕ) = none
    · exfalso
      have htop : restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) = ⊤ :=
        restrictIdeal_eq_top_of_le (T.boundary.get j) inf_le_left
          (ha2 (j : ℕ) j.isLt hn)
      have hle : restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)
          ≤ ⨆ i ∈ J, restrictIdeal (T.boundary.get i) (U₀ ⊓ U₁) :=
        le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) =>
          restrictIdeal (T.boundary.get i) (U₀ ⊓ U₁)) j hj
      rw [htop] at hle
      have htop' : restrictIdeal (intersectionIdeal T.boundary J) (U₀ ⊓ U₁) = ⊤ :=
        hbs.trans (top_le_iff.mp hle)
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top (intersectionIdeal T.boundary J)
        htop' hxV hxsupp
    · exact Option.ne_none_iff_exists'.mp hn
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), ∀ t : Fin m, t ∈ S ↔ ∃ j ∈ J, a (j : ℕ) = some t :=
    ⟨Finset.univ.filter (fun t => ∃ j ∈ J, a (j : ℕ) = some t), by intro t; simp⟩
  have key : ∀ j ∈ J, ∃ t : Fin m, t ∈ S ∧
      restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)
        = (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t} := by
    intro j hj
    obtain ⟨t, hat⟩ := hJsome j hj
    exact ⟨t, (hS t).mpr ⟨j, hj, hat⟩,
      restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ (T.boundary.get j) {t}
        (ha3 (j : ℕ) j.isLt t hat)⟩
  have key2 : ∀ t ∈ S, ∃ j ∈ J,
      (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t}
        = restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁) := by
    intro t ht
    obtain ⟨j, hj, hat⟩ := (hS t).mp ht
    exact ⟨j, hj, (restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ (T.boundary.get j) {t}
      (ha3 (j : ℕ) j.isLt t hat)).symm⟩
  refine ⟨U₀ ⊓ U₁, hxV, m, c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀), a, S, ha1, ?_, ?_, ?_⟩
  · intro i hi hin
    exact restrictIdeal_eq_top_of_le _ inf_le_left (ha2 i hi hin)
  · intro i hi t hit
    exact restrictIdeal_eq_restrict_coordIdeal_of_le inf_le_left c₀ _ {t} (ha3 i hi t hit)
  · rw [h4, hbs, MonomialChart.coordIdeal_eq_biSup_singleton T.structMap (U₀ ⊓ U₁) m
      (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)) S]
    refine le_antisymm (iSup₂_le ?_) (iSup₂_le ?_)
    · intro j hj
      obtain ⟨t, htS, heq⟩ := key j hj
      rw [heq]
      exact le_iSup₂ (f := fun (t : Fin m) (_ : t ∈ S) =>
        (c₀.restrict (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).coordIdeal {t}) t htS
    · intro t ht
      obtain ⟨j, hj, heq⟩ := key2 t ht
      rw [heq]
      exact le_iSup₂ (f := fun (j : Fin T.boundary.length) (_ : j ∈ J) =>
        restrictIdeal (T.boundary.get j) (U₀ ⊓ U₁)) j hj

end MonomialCenterGeometry

end FunctorialResolution.EmbeddedResolution

end
