import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem subset_or_subset_of_isIrreducible {W : Type*} [TopologicalSpace W] {s a b : Set W}
    (hs : IsIrreducible s) (ha : IsClosed a) (hb : IsClosed b) (h : s ⊆ a ∪ b) :
    s ⊆ a ∨ s ⊆ b :=
  isPreirreducible_iff_isClosed_union_isClosed.mp hs.2 a b ha hb h

private theorem exists_mem_finset_subset_of_isIrreducible {W : Type*} [TopologicalSpace W]
    {s : Set W} (hs : IsIrreducible s) (F : Finset (Set W))
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ (F : Set (Set W))) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  revert hcl hsub
  refine Finset.induction_on F ?_ ?_
  · intro _ hsub'
    obtain ⟨x, hx⟩ := hs.1
    have hx' := hsub' hx
    simp at hx'
  · intro a G _ ih hcl' hsub'
    have hcla : IsClosed a := hcl' a (Finset.mem_insert_self a G)
    have hclG : ∀ Z ∈ G, IsClosed Z := fun Z hZ => hcl' Z (Finset.mem_insert_of_mem hZ)
    have hclU : IsClosed (⋃₀ ((G : Finset (Set W)) : Set (Set W))) := by
      rw [Set.sUnion_eq_biUnion]
      exact Set.Finite.isClosed_biUnion G.finite_toSet (fun Z hZ => hclG Z hZ)
    have hsub2 : s ⊆ a ∪ ⋃₀ ((G : Finset (Set W)) : Set (Set W)) := by
      intro y hy
      have hy' := hsub' hy
      rw [Finset.coe_insert, Set.sUnion_insert] at hy'
      exact hy'
    rcases subset_or_subset_of_isIrreducible hs hcla hclU hsub2 with hh | hh
    · exact ⟨a, Finset.mem_insert_self a G, hh⟩
    · obtain ⟨Z, hZ, hZs⟩ := ih hclG hh
      exact ⟨Z, Finset.mem_insert_of_mem hZ, hZs⟩

theorem exists_mem_of_isIrreducible_subset_sUnion {W : Type*} [TopologicalSpace W]
    {s : Set W} (hs : IsIrreducible s) {F : Set (Set W)} (hF : F.Finite)
    (hcl : ∀ Z ∈ F, IsClosed Z) (hsub : s ⊆ ⋃₀ F) :
    ∃ Z ∈ F, s ⊆ Z := by
  classical
  obtain ⟨Z, hZ, hsZ⟩ :=
    exists_mem_finset_subset_of_isIrreducible hs hF.toFinset
      (fun Z hZ => hcl Z (hF.mem_toFinset.mp hZ))
      (by
        intro y hy
        obtain ⟨Z, hZF, hyZ⟩ := hsub hy
        refine ⟨Z, ?_, hyZ⟩
        simpa only [Finset.mem_coe, Set.Finite.mem_toFinset] using hZF)
  exact ⟨Z, hF.mem_toFinset.mp hZ, hsZ⟩

private theorem exists_isOpen_preimage_eq {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {f : X → Z} (hf : Topology.IsClosedEmbedding f) {u : Set X} (hu : IsOpen u) :
    ∃ U : Set Z, IsOpen U ∧ f ⁻¹' U = u :=
  hf.isInducing.isOpen_iff.mp hu

theorem isPreirreducible_preimage_of_isClosedEmbedding {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] {f : X → Z} (hf : Topology.IsClosedEmbedding f) {t : Set Z}
    (hran : t ⊆ Set.range f) (ht : IsPreirreducible t) :
    IsPreirreducible (f ⁻¹' t) := by
  intro u v hu hv hsu hsv
  obtain ⟨U, hU, hUeq⟩ := exists_isOpen_preimage_eq hf hu
  obtain ⟨V, hV, hVeq⟩ := exists_isOpen_preimage_eq hf hv
  obtain ⟨x, hxt, hxu⟩ := hsu
  obtain ⟨y, hyt, hyv⟩ := hsv
  have hxU : f x ∈ U := by
    have hx' : x ∈ f ⁻¹' U := by rw [hUeq]; exact hxu
    exact hx'
  have hyV : f y ∈ V := by
    have hy' : y ∈ f ⁻¹' V := by rw [hVeq]; exact hyv
    exact hy'
  obtain ⟨z, hzt, hzU, hzV⟩ := ht U V hU hV ⟨f x, hxt, hxU⟩ ⟨f y, hyt, hyV⟩
  obtain ⟨w, rfl⟩ := hran hzt
  refine ⟨w, hzt, ?_, ?_⟩
  · have hw : w ∈ f ⁻¹' U := hzU
    rw [hUeq] at hw
    exact hw
  · have hw : w ∈ f ⁻¹' V := hzV
    rw [hVeq] at hw
    exact hw

theorem isIrreducible_preimage_of_isClosedEmbedding {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] {f : X → Z} (hf : Topology.IsClosedEmbedding f) {t : Set Z}
    (hran : t ⊆ Set.range f) (ht : IsIrreducible t) :
    IsIrreducible (f ⁻¹' t) := by
  refine ⟨?_, isPreirreducible_preimage_of_isClosedEmbedding hf hran ht.2⟩
  obtain ⟨z, hz⟩ := ht.1
  obtain ⟨w, rfl⟩ := hran hz
  exact ⟨w, hz⟩

theorem discardedComponents_subset_irreducibleComponents (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (i : ℕ) :
    (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i ⊆
      irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) := by
  intro C hC
  exact (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).mem_discardedComponents_iff i C).mp hC).1

theorem isClosedEmbedding_discardedι (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (i : ℕ) :
    Topology.IsClosedEmbedding ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base :=
  AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i).subschemeι

theorem range_discardedι_eq_sUnion_discardedComponents (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (i : ℕ)
    (hi : i < (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) :
    Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      ⋃₀ ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i) := by
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
      (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i
      (le_of_lt hi)
  have h1 : Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i).support :
        Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i)) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedIdeal i)
  rw [h1, AffineSpacePrincipalizationData.discardedIdeal_eq_vanishingIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    AffineSpacePrincipalizationData.coe_discardedLocusClosure, AffineSpacePrincipalizationData.discardedLocus_eq_sUnion_discardedComponents]

theorem affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineStrictTransformEmptyAtLast A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  show (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength = ⊤
  have htop : (OpenImmersionRestriction.principalizationOfEmbedding k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A).ideal
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length = ⊤ := by
    have h := hA.lastIdeal_eq_top k (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambient
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct
      (AlgebraicGeometry.Scheme.Hom.ker (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).emb)
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).nonzeroOnComponents_ker
      ([] : List (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambient.IdealSheafData)
      (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).sncEmpty
    rw [IdealBlowupSequence.lastIdeal_eq] at h
    exact h
  have hno : ∀ C : Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength),
      C ∉ irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) := by
    intro C hC
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    have himgCl : IsClosed (⇑(((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).strictTransformι
        ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length).base '' C) :=
      (EmbeddedBlowupSequence.isClosedEmbedding_strictTransformι
        ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A) _).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨-, hord⟩ := OpenImmersionRestriction.agreesWithComponentsOrderOne_of_le (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).length le_rfl C hC ξ hξ himgCl
    rw [htop] at hord
    have h01 : (0 : ℕ∞) = 1 := (orderAt_top _).symm.trans hord
    simp at h01
  have : IsEmpty ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength) := by
    constructor
    intro x
    exact hno (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  have hsupp : (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformIdeal
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength).support :
      Set ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLevel
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength)) = ∅ := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι]
    exact Set.range_eq_empty _
  exact (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr hsupp

theorem affineDetachedComponentsNotInBoundary (A : PrincipalizationAlgorithm.{u})
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) :
    AffineDetachedComponentsNotInBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi j hj C hC hsubset
  have hle : i ≤ (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).ambientLength := le_of_lt hi
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
      (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i hle
  have hfemb : Topology.IsClosedEmbedding
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base :=
    isClosedEmbedding_discardedι A hemb hsnc hsm k Y pY i
  have hrange : Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base =
      ⋃₀ ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i) :=
    range_discardedι_eq_sUnion_discardedComponents A hemb hsnc hsm k Y pY i hi
  have hsubComp : (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i ⊆
      irreducibleComponents ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) :=
    discardedComponents_subset_irreducibleComponents A hemb hsnc hsm k Y pY i
  have hfin : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedComponents i).Finite :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset hsubComp
  have hCirr : IsIrreducible C := hC.1
  have himgIrr :
      IsIrreducible (⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C) :=
    hCirr.image _ hfemb.continuous.continuousOn
  obtain ⟨C₀, hC₀mem, hC₀sub⟩ :=
    exists_mem_of_isIrreducible_subset_sUnion himgIrr hfin
      (fun Z hZ => isClosed_of_mem_irreducibleComponents _ (hsubComp hZ))
      (by rw [← hrange]; exact Set.image_subset_range _ _)
  have hC₀ic : C₀ ∈ irreducibleComponents
      ↥((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransform i) := hsubComp hC₀mem
  have hC₀range :
      C₀ ⊆ Set.range ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base := by
    rw [hrange]
    exact Set.subset_sUnion_of_mem hC₀mem
  have hpre : IsIrreducible
      (⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀) :=
    isIrreducible_preimage_of_isClosedEmbedding hfemb hC₀range hC₀ic.1
  have hCsub : C ⊆ ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀ :=
    fun z hz => hC₀sub ⟨z, hz, rfl⟩
  have hCeq : ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base ⁻¹' C₀ ⊆ C :=
    hC.2 hpre hCsub
  have himg : ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C = C₀ := by
    refine Set.Subset.antisymm hC₀sub ?_
    intro z hz
    obtain ⟨w, rfl⟩ := hC₀range hz
    exact ⟨w, hCeq hz, rfl⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC₀ic.1 (isClosed_of_mem_irreducibleComponents _ hC₀ic)
  have hξmem : ξ ∈ ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base '' C := by
    rw [himg]
    exact hξ.mem
  obtain ⟨w, hwC, hw⟩ := hξmem
  have hmem : ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ξ ∈
      ⇑((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i ≫
        (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base '' C := by
    refine ⟨w, hwC, ?_⟩
    show ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base
        (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).discardedι i).base w) =
      ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).strictTransformι i).base ξ
    rw [hw]
  have hx := hsubset hmem
  have hclear := EmbeddedBlowupSequence.avoidsCenters_strictTransformι_of_isGenericPoint
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A)
    (OpenImmersionRestriction.isNoetherian_schemeAt_toEmbeddedBlowupSequence (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A) i hle
    C₀ hC₀ic ξ hξ
  exact OpenImmersionRestriction.not_avoidsCenters_of_mem_boundary_support (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) A i hle
    (((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).boundary i).get ⟨j, hj⟩)
    (List.get_mem ..) _ hx hclear

end FunctorialResolution.EmbeddedResolution

end
