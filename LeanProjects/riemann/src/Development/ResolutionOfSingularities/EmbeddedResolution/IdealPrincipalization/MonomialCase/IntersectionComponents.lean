import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem mem_irreducibleComponents_iff_isIrreducible_and_maximal {α : Type*}
    [TopologicalSpace α] (s : Set α) :
    s ∈ irreducibleComponents α ↔
      IsIrreducible s ∧ ∀ t : Set α, IsIrreducible t → s ⊆ t → t ⊆ s :=
  ⟨fun h => ⟨h.1, fun _ ht hst => h.2 ht hst⟩, fun h => ⟨h.1, fun t ht hst => h.2 t ht hst⟩⟩

private theorem maximal_irreducible_subset_range_iff {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Topology.IsClosedEmbedding f) {S : Set β}
    (hr : Set.range f = S) (C : Set β) :
    (IsIrreducible C ∧ C ⊆ S ∧ ∀ C' : Set β, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C)
      ↔ ∃ D ∈ irreducibleComponents α, f '' D = C := by
  constructor
  · rintro ⟨hirr, hsub, hmax⟩
    have hCr : C ⊆ Set.range f := by rw [hr]; exact hsub
    have himg : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCr
    refine ⟨f ⁻¹' C, (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mpr ⟨?_, ?_⟩, himg⟩
    · exact isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hirr hCr
    · intro t ht hDt x hx
      have himgt : IsIrreducible (f '' t) := ht.image f hf.continuous.continuousOn
      have hCt : C ⊆ f '' t := by
        rw [← himg]
        exact Set.image_mono hDt
      have htS : f '' t ⊆ S := by
        rw [← hr]
        exact Set.image_subset_range _ _
      have heq : f '' t = C := hmax _ himgt hCt htS
      have hmem : f x ∈ C := by
        rw [← heq]
        exact ⟨x, hx, rfl⟩
      exact hmem
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨hDirr, hDmax⟩ := (mem_irreducibleComponents_iff_isIrreducible_and_maximal _).mp hD
    refine ⟨hDirr.image f hf.continuous.continuousOn, ?_, ?_⟩
    · rw [← hr]
      exact Set.image_subset_range _ _
    · intro C' hC' hsub' hS'
      have hC'r : C' ⊆ Set.range f := by rw [hr]; exact hS'
      have hirr' : IsIrreducible (f ⁻¹' C') :=
        isIrreducible_preimage_of_isEmbedding hf.toIsEmbedding hC' hC'r
      have hDD : D ⊆ f ⁻¹' C' := fun x hx => hsub' ⟨x, hx, rfl⟩
      have h1 : f ⁻¹' C' ⊆ D := hDmax _ hirr' hDD
      have h2 : f '' (f ⁻¹' C') = C' := Set.image_preimage_eq_of_subset hC'r
      apply Set.Subset.antisymm
      · rw [← h2]
        exact Set.image_mono h1
      · exact hsub'

theorem mem_intersectionComponents_iff_exists_irreducibleComponent {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (C : Set ↥Y) :
    C ∈ intersectionComponents L J ↔
      ∃ D ∈ irreducibleComponents ↥(intersectionIdeal L J).subscheme,
        ⇑(intersectionIdeal L J).subschemeι '' D = C := by
  have hemb : Topology.IsClosedEmbedding ⇑(intersectionIdeal L J).subschemeι :=
    Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι
  have hrange : Set.range ⇑(intersectionIdeal L J).subschemeι
      = (↑(intersectionIdeal L J).support : Set ↥Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  exact maximal_irreducible_subset_range_iff hemb hrange C

theorem isClosed_of_mem_intersectionComponents {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (C : Set ↥Y) (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent L J C).mp hC
  exact (Scheme.Hom.isClosedEmbedding (intersectionIdeal L J).subschemeι).isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ hD)

theorem intersectionComponents_finite (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) : (intersectionComponents T.boundary J).Finite := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have h : intersectionComponents T.boundary J =
      (fun D => ⇑(intersectionIdeal T.boundary J).subschemeι '' D) ''
        irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme := by
    ext C
    rw [mem_intersectionComponents_iff_exists_irreducibleComponent]
    exact Iff.rfl
  rw [h]
  exact Set.Finite.image _ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents ..)

private theorem irreducibleComponents_eq_of_inter_nonempty_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)) :
    ∀ C₁ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme,
        (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
  have := hsm
  rintro C₁ h₁ C₂ h₂ ⟨x, hx₁, hx₂⟩
  exact irreducibleComponents_eq_of_stalk_isDomain _
    (fun z => isDomain_stalk_of_smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) z)
    h₁ h₂ hx₁ hx₂

theorem intersectionComponents_disjoint_of_smooth (T : MarkedIdealWithBoundary.{u})
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (C C' : Set ↥T.scheme) (hC : C ∈ intersectionComponents T.boundary J)
    (hC' : C' ∈ intersectionComponents T.boundary J) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC
  obtain ⟨D', hD', rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp hC'
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  rw [Set.disjoint_left]
  rintro x ⟨d, hd, rfl⟩ ⟨d', hd', he⟩
  have hdd : d' = d := hinj he
  subst hdd
  have hDD : D = D' :=
    irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm D hD D' hD' ⟨d', hd, hd'⟩
  exact hne (by rw [hDD])

theorem isOpen_preimage_sUnion_intersectionComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length))
    (hsm : AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap))
    (𝒞 : Set (Set ↥T.scheme)) (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J) :
    IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞) := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hinj : Function.Injective ⇑(intersectionIdeal T.boundary J).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (intersectionIdeal T.boundary J).subschemeι).injective
  have key : ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 =
      ⋃₀ {D : Set ↥(intersectionIdeal T.boundary J).subscheme |
        D ∈ irreducibleComponents ↥(intersectionIdeal T.boundary J).subscheme ∧
          ⇑(intersectionIdeal T.boundary J).subschemeι '' D ∈ 𝒞} := by
    apply Set.Subset.antisymm
    · rintro x hx
      obtain ⟨C, hC𝒞, hxC⟩ := hx
      obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC𝒞)
      obtain ⟨d, hd, hde⟩ := hxC
      have hdx : d = x := hinj hde
      subst hdx
      exact ⟨D, ⟨hD, hC𝒞⟩, hd⟩
    · rintro x ⟨D, ⟨hD, hD𝒞⟩, hxD⟩
      exact ⟨⇑(intersectionIdeal T.boundary J).subschemeι '' D, hD𝒞, ⟨x, hxD, rfl⟩⟩
  rw [key]
  exact isOpen_sUnion_of_subset_irreducibleComponents
    (irreducibleComponents_eq_of_inter_nonempty_of_smooth T J hsm) (fun D hD => hD.1)

theorem componentUnionIdeal_support_eq_sUnion (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme))
    (h𝒞 : 𝒞 ⊆ intersectionComponents T.boundary J)
    (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme) = ⋃₀ 𝒞 := by
  have := hT.isNoetherian
  have : TopologicalSpace.NoetherianSpace ↥(intersectionIdeal T.boundary J).subscheme := inferInstance
  have hqc : QuasiCompact ((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) := inferInstance
  have hsub : ⋃₀ 𝒞 ⊆ Set.range ⇑(intersectionIdeal T.boundary J).subschemeι := by
    rintro x ⟨C, hC, hxC⟩
    obtain ⟨D, hD, rfl⟩ := (mem_intersectionComponents_iff_exists_irreducibleComponent _ _ _).mp (h𝒞 hC)
    obtain ⟨d, hd, rfl⟩ := hxC
    exact ⟨d, rfl⟩
  have h0 : ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫ (intersectionIdeal T.boundary J).subschemeι)
      = ⇑(intersectionIdeal T.boundary J).subschemeι ∘ ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι := rfl
  have hr2 : Set.range ⇑(componentUnionOpens T.boundary J 𝒞 hop).ι
      = ⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞 :=
    Scheme.Opens.range_ι _
  have hrange : Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
      (intersectionIdeal T.boundary J).subschemeι) = ⋃₀ 𝒞 := by
    rw [h0, Set.range_comp, hr2]
    exact Set.image_preimage_eq_of_subset hsub
  have hfin : 𝒞.Finite := (intersectionComponents_finite T hT J).subset h𝒞
  have hclosed : IsClosed (⋃₀ 𝒞) := by
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion
      (fun C hC => isClosed_of_mem_intersectionComponents T.boundary J C (h𝒞 hC))
  have h1 : (↑(componentUnionIdeal T.boundary J 𝒞 hop).support : Set ↥T.scheme)
      = closure (Set.range ⇑((componentUnionOpens T.boundary J 𝒞 hop).ι ≫
          (intersectionIdeal T.boundary J).subschemeι)) :=
    Scheme.Hom.support_ker _
  rw [h1, hrange]
  exact hclosed.closure_eq

end FunctorialResolution.EmbeddedResolution

end
