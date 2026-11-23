import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothOrderOneCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

private theorem smooth_strictTransformι_comp_schemeAtToSpec
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) :
    ∀ i, i ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length →
      AlgebraicGeometry.Smooth
        ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι i ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec i) := by
  have : AlgebraicGeometry.Smooth pY := hsm
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)
  intro i
  induction i with
  | zero =>
      intro _
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hker : AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι 0)
          = AlgebraicGeometry.Scheme.Hom.ker (S.emb ≫ S.ambientSeq.isoZero.inv) := by
        rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
          EmbeddedBlowupSequence.strictTransformIdeal_zero]
      obtain ⟨e, he⟩ :=
        exists_iso_of_ker_eq (S.strictTransformι 0) (S.emb ≫ S.ambientSeq.isoZero.inv) hker
      have hstruct : S.ambientSeq.isoZero.inv ≫ S.schemeAtToSpec 0 = S.ambientStruct := by
        rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      have key : e.hom ≫ pY = S.strictTransformι 0 ≫ S.schemeAtToSpec 0 := by
        rw [← he]
        simp only [Category.assoc]
        rw [hstruct, S.emb_comp]
      rw [← key]
      infer_instance
  | succ i ih =>
      intro hi
      set S := D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad) with _hS
      have hi' : i < S.length := hi
      have ih' := ih (Nat.le_of_succ_le hi)
      have hredi : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
        EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN i (Nat.le_of_lt hi')
      have hredi1 : AlgebraicGeometry.IsReduced (S.strictTransform (i + 1)) :=
        EmbeddedBlowupSequence.isReduced_strictTransform_of_isNoetherian S hN (i + 1) hi
      set U : (S.schemeAt (i + 1)).Opens :=
        (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) with _hU
      have hUsub : (U : Set ↥(S.schemeAt (i + 1))) ⊆
          ⇑(S.blowdown i).base ⁻¹'
            ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := fun _ hx => hx
      have hgi : AlgebraicGeometry.IsOpenImmersion (U.ι ≫ S.blowdown i) :=
        EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown S i hi' U hUsub
      have hrangeA : Set.range ⇑(S.strictTransformι (i + 1)).base ⊆ Set.range ⇑U.ι.base := by
        rw [Scheme.Opens.range_ι]
        rintro z ⟨y, rfl⟩
        exact (S.mem_ambientCenterSupportCompl i _).mpr
          ((S.avoidsCenters_succ_iff i _).mp (avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm (i + 1) hi y)).1
      set j := AlgebraicGeometry.IsOpenImmersion.lift U.ι (S.strictTransformι (i + 1)) hrangeA with _hjdef
      have hj : j ≫ U.ι = S.strictTransformι (i + 1) :=
        AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
      have hjc : AlgebraicGeometry.IsClosedImmersion (j ≫ U.ι) := by
        rw [hj]; infer_instance
      have : AlgebraicGeometry.IsClosedImmersion j :=
        AlgebraicGeometry.IsClosedImmersion.of_comp j U.ι
      have hbase : ∀ y : ↥(S.strictTransform (i + 1)),
          U.ι.base (j.base y) = (S.strictTransformι (i + 1)).base y := by
        intro y
        rw [show U.ι.base (j.base y) = (j ≫ U.ι).base y from rfl, hj]
      have hkeymap : ∀ y : ↥(S.strictTransform (i + 1)),
          (S.blowdown i).base ((S.strictTransformι (i + 1)).base y)
            = (S.strictTransformι i).base ((S.strictTransformMap i).base y) := by
        intro y
        have h : (S.strictTransformMap i ≫ S.strictTransformι i).base y
            = (S.strictTransformι (i + 1) ≫ S.blowdown i).base y := by
          rw [S.strictTransformMap_comp_strictTransformι i]
        exact h.symm
      set pre : Set ↥(U.toScheme) := ⇑(U.ι ≫ S.blowdown i).base ⁻¹'
          (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
            Set ↥(S.schemeAt i)) with hpre
      have hsuppcl : IsClosed pre := by
        rw [hpre]
        exact (S.strictTransformIdeal i).support.2.preimage
          (U.ι ≫ S.blowdown i).base.hom.continuous
      have hker_eq : S.strictTransformIdeal i = AlgebraicGeometry.Scheme.Hom.ker (S.strictTransformι i) := by
        rw [EmbeddedBlowupSequence.strictTransformι_eq_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      have h1 : Scheme.IdealSheafData.vanishingIdeal
          ((S.strictTransformIdeal i).support) = S.strictTransformIdeal i := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support, hker_eq]
        exact radical_ker_eq_ker (S.strictTransformι i)
      have hKvan : (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
          = Scheme.IdealSheafData.vanishingIdeal
              (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) := by
        calc (S.strictTransformIdeal i).comap (U.ι ≫ S.blowdown i)
            = (Scheme.IdealSheafData.vanishingIdeal
                ((S.strictTransformIdeal i).support)).comap (U.ι ≫ S.blowdown i) := by rw [h1]
          _ = Scheme.IdealSheafData.vanishingIdeal
                (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme)) :=
              comap_vanishingIdeal_of_isOpenImmersion (U.ι ≫ S.blowdown i) _ _ rfl
      have hrange1 : Set.range ⇑j.base = pre := by
        rw [hpre]
        ext z
        simp only [Set.mem_range, Set.mem_preimage]
        constructor
        · rintro ⟨y, rfl⟩
          rw [show (U.ι ≫ S.blowdown i).base (j.base y)
              = (S.blowdown i).base (U.ι.base (j.base y)) from rfl, hbase y, hkeymap y,
            ← Scheme.IdealSheafData.range_subschemeι (S.strictTransformIdeal i)]
          exact ⟨(S.strictTransformMap i).base y, rfl⟩
        · intro hz
          have hzU : U.ι.base z ∈ ((U : (S.schemeAt (i + 1)).Opens) :
              Set ↥(S.schemeAt (i + 1))) := by
            rw [← Scheme.Opens.range_ι U]
            exact ⟨z, rfl⟩
          have hnc : (S.blowdown i).base (U.ι.base z) ∉
              (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                Set ↥(S.schemeAt i)) :=
            (S.mem_ambientCenterSupportCompl i _).mp (hUsub hzU)
          have hin : (S.blowdown i).base (U.ι.base z) ∈
              (((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                Set ↥(S.schemeAt i)) := hz
          have hrr : Set.range ⇑(S.strictTransformι (i + 1)).base
              = closure (⇑(S.blowdown i).base ⁻¹'
                  ((((S.strictTransformIdeal i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                      Set ↥(S.schemeAt i)) \
                    (((S.ambientCenter i).support : TopologicalSpace.Closeds ↥(S.schemeAt i)) :
                      Set ↥(S.schemeAt i)))) :=
            EmbeddedBlowupSequence.range_strictTransformι_succ S hN i hi'
          have hx : U.ι.base z ∈ Set.range ⇑(S.strictTransformι (i + 1)).base := by
            rw [hrr]
            exact subset_closure ⟨hin, hnc⟩
          obtain ⟨w, hw⟩ := hx
          refine ⟨w, ?_⟩
          apply U.ι.isOpenEmbedding.injective
          rw [hbase w, hw]
      have hrange2 : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι.base
            = pre := by
        rw [FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
          AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      have : AlgebraicGeometry.IsReduced
          (Scheme.IdealSheafData.vanishingIdeal
            (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subscheme :=
        AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
      obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq j
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
        (hrange1.trans hrange2.symm)
      have ihsub : AlgebraicGeometry.Smooth
          ((S.strictTransformIdeal i).subschemeι ≫ S.schemeAtToSpec i) := by
        rw [← EmbeddedBlowupSequence.strictTransformι_eq_subschemeι]
        exact ih'
      have hsm2 := smooth_comap_subschemeι_of_isOpenImmersion
        (U.ι ≫ S.blowdown i) (S.strictTransformIdeal i) (S.schemeAtToSpec i) ihsub
      rw [hKvan] at hsm2
      have hlev : S.blowdown i ≫ S.schemeAtToSpec i = S.schemeAtToSpec (i + 1) := by
        rw [EmbeddedBlowupSequence.schemeAtToSpec_eq, EmbeddedBlowupSequence.schemeAtToSpec_eq, ← Category.assoc,
          ← FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_succ]
      have hgoal : S.strictTransformι (i + 1) ≫ S.schemeAtToSpec (i + 1)
          = e.hom ≫ ((Scheme.IdealSheafData.vanishingIdeal
              (⟨pre, hsuppcl⟩ : TopologicalSpace.Closeds ↥(U.toScheme))).subschemeι
              ≫ ((U.ι ≫ S.blowdown i) ≫ S.schemeAtToSpec i)) := by
        rw [← hj, ← hlev, ← he]
        simp only [Category.assoc]
      rw [hgoal]
      have := hsm2
      infer_instance

theorem smooth_strictTransformι_comp_chartLevelStructureMorphism
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    AlgebraicGeometry.Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  have hP : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec t
      = chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t := rfl
  rw [← hP]
  exact smooth_strictTransformι_comp_schemeAtToSpec hres hB hrad D hsm t ht

theorem disjoint_irreducibleComponents_strictTransform
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)}
    (h₁ : C₁ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (h₂ : C₂ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ :=
  FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth k _ _
    (smooth_strictTransformι_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht) C₁ h₁ C₂ h₂ hne

theorem isClopen_of_mem_irreducibleComponents_strictTransform
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)}
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)) :
    IsClopen C := by
  have hNoeth : TopologicalSpace.NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).noetherianSpace_strictTransform_of_isNoetherian
      (isNoetherian_schemeAt_toEmbeddedBlowupSequence D (canonicalPrincipalization hres hrad)) t ht
  have hsep : ∀ C₁ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t),
      ∀ C₂ ∈ irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t),
      (C₁ ∩ C₂).Nonempty → C₁ = C₂ := by
    intro C₁ h₁ C₂ h₂ hx
    by_contra hne
    obtain ⟨x, hx₁, hx₂⟩ := hx
    exact Set.disjoint_left.mp
      (disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm t ht h₁ h₂ hne) hx₁ hx₂
  have hopen : IsOpen (⋃₀ ({C} :
      Set (Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t)))) :=
    FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents hsep (by
      intro C' hC'
      obtain rfl : C' = C := Set.mem_singleton_iff.mp hC'
      exact hC)
  rw [Set.sUnion_singleton] at hopen
  exact ⟨isClosed_of_mem_irreducibleComponents _ hC, hopen⟩

theorem smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C)) :
    AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
            TopologicalSpace.Closeds
              ↥((D.toEmbeddedBlowupSequence
                (canonicalPrincipalization hres hrad)).schemeAt t))).subschemeι ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
  have hclopen : IsClopen C :=
    isClopen_of_mem_irreducibleComponents_strictTransform hres hB hrad D hsm t ht hC
  have hsmq : AlgebraicGeometry.Smooth
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) :=
    smooth_strictTransformι_comp_chartLevelStructureMorphism hres hB hrad D hsm t ht
  have hPlevel : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAtToSpec t
      = chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t := rfl
  have hftq : AlgebraicGeometry.LocallyOfFiniteType
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    have h1 :=
      (D.toEmbeddedBlowupSequence
        (canonicalPrincipalization hres hrad)).locallyOfFiniteType_strictTransformToSpec t ht
    rw [FunctorialResolution.EmbeddedResolution.EmbeddedBlowupSequence.strictTransformToSpec_eq, hPlevel] at h1
    exact h1
  have hsub := FunctorialResolution.EmbeddedResolution.smooth_subschemeι_vanishingIdeal_comp_of_isClopen
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t ≫
        chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) C hclopen
  have : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hclopen.isClosed⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).strictTransform t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have : AlgebraicGeometry.IsReduced
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence
              (canonicalPrincipalization hres hrad)).schemeAt t))).subscheme :=
    AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _ _
  have hrange :
      Set.range ⇑((Scheme.IdealSheafData.vanishingIdeal
            (⟨C, hclopen.isClosed⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).strictTransform t))).subschemeι ≫
          (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base
        = Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
                C, hCcl⟩ :
              TopologicalSpace.Closeds
                ↥((D.toEmbeddedBlowupSequence
                  (canonicalPrincipalization hres hrad)).schemeAt t))).subschemeι.base := by
    rw [Scheme.Hom.range_comp_base, FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      FunctorialResolution.EmbeddedResolution.range_base_subschemeι,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal,
      AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨e, he⟩ := FunctorialResolution.EmbeddedResolution.exists_iso_of_range_base_eq _ _ hrange
  exact smooth_comp_of_iso_hom_eq e _ _ _ _ he hsub

private theorem agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hClearAll : ∀ (s : ℕ), s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ y : ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        (D.toEmbeddedBlowupSequence A).AvoidsCenters s (((D.toEmbeddedBlowupSequence A).strictTransformι s).base y))
    (hDisjAll : ∀ (s : ℕ), s ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform s),
        C₁ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C₂ ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform s) →
        C₁ ≠ C₂ → Disjoint C₁ C₂) :
    ∀ (t : ℕ), t ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform t),
        C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform t) →
        ∀ hCcl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C),
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt t),
          x ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C →
          AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal t)
            (Scheme.IdealSheafData.vanishingIdeal
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι t).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt t))) x := by
  intro t
  induction t with
  | zero =>
    intro _ C hC hCcl x hx
    classical
    have hNoeth : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
      (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
        (Nat.zero_le _)
    have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
    have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
    have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
    obtain ⟨Bad, hBaddef⟩ : ∃ B : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0),
        B = ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
          ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' := ⟨_, rfl⟩
    have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
    have hBadcl : IsClosed Bad := by
      rw [hBaddef]
      exact hfin.isClosed_biUnion fun C'' hC'' =>
        hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ hC''.1)
    have hxU : x ∈ Badᶜ := by
      intro hmem
      rw [hBaddef] at hmem
      obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
      obtain ⟨z, hzC'', hz⟩ := hxim
      obtain ⟨w, hwC, hw⟩ := hx
      have hzw : z = w := hemb.injective (hz.trans hw.symm)
      rw [hzw] at hzC''
      have hne : C'' ≠ C := fun h => hC''D.2 (Set.mem_singleton_iff.mpr h)
      exact Set.disjoint_left.mp
        (hDisjAll 0 (Nat.zero_le _) C'' C hC''D.1 hC hne) hzC'' hwC
    have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
        = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
      ext z
      constructor
      · rintro ⟨⟨w, rfl⟩, hz⟩
        refine ⟨?_, hz⟩
        by_cases hw : w ∈ C
        · exact ⟨w, hw, rfl⟩
        · refine absurd ?_ hz
          rw [hBaddef]
          refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents w, ?_⟩
            ⟨w, mem_irreducibleComponent, rfl⟩
          intro h
          exact hw (h ▸ mem_irreducibleComponent)
      · rintro ⟨⟨w, hwC, rfl⟩, hz⟩
        exact ⟨⟨w, rfl⟩, hz⟩
    rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  | succ i ih =>
    intro hi C hC hCcl x hx
    classical
    have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
    have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
    have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
    obtain ⟨η, hηgen⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents _ hC)
    obtain ⟨C', hC'm, hη', _⟩ :=
      (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
    have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
      ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hC'm)
    obtain ⟨y, hyC, hxy⟩ := hx
    have hclx : (D.toEmbeddedBlowupSequence A).AvoidsCenters (i + 1) x := by
      rw [← hxy]
      exact hClearAll (i + 1) hi y
    have hnot := (((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hclx).1
    have hblow : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈
        ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' :=
      EmbeddedBlowupSequence.mem_image_strictTransformι_of_mem_image_succ (D.toEmbeddedBlowupSequence A) i C η hηgen
        C' hη' x ⟨y, hyC, hxy⟩
    obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp
      (ih (Nat.le_of_succ_le hi) C' hC'm hC'cl _ hblow)
    obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
    have hxV' : ((D.toEmbeddedBlowupSequence A).blowdown i).base x ∈ V' := by
      rw [hV']; exact hxV
    have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
      rw [hV']; exact hVeq
    obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
        U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
          (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
    have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
        ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
          (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
            Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      rw [hUdef]
      intro z hz
      exact hz.2
    have hmemU : ∀ z : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) ∉
        (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
      intro z
      exact hUsub z.2
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨hxV', ((D.toEmbeddedBlowupSequence A).mem_ambientCenterSupportCompl i _).mpr hnot⟩
    have : AlgebraicGeometry.IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
    have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
      refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
      rw [Set.disjoint_left]
      intro z hz hmem
      rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
      exact absurd (mem_support_of_mem_support_comap
        ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ z hmem) (hUsub hz)
    have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
        = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      comap_eq_comap_comp_of_mul_eq _ U _ _ _
        ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
    have hle : U ≤ (TopologicalSpace.Opens.map
        ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
      rw [hUdef]
      intro z hz
      exact hz.1
    have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = (Scheme.IdealSheafData.vanishingIdeal
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
      AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
        ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
    have hLHS : (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
        = Scheme.IdealSheafData.vanishingIdeal
            (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
              (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
                TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
      refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
      ext z
      have hcb : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
          = ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z) := rfl
      have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
        (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base z) (hmemU z)
      constructor
      · intro hz
        have hz1 : U.ι.base z ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hz1
        have hz3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [hcb]; exact hz2
        exact hz3
      · intro hz
        have hz1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base z
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hz
        have hz2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base z)
            ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
          rw [← hcb]; exact hz1
        exact hiff.mp hz2
    refine (agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩
    exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))

theorem agreeNear_ideal_vanishingIdeal_image_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t ≤ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hC : C ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hCcl : IsClosed
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C))
    (x : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))
    (hx : x ∈ ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C) :
    AgreeNear ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds
            ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) x :=
  agreeNear_vanishingIdeal_image_of_forall_avoidsCenters_of_disjoint D (canonicalPrincipalization hres hrad)
    (fun s hs y => avoidsCenters_strictTransformι_of_smooth hres hB hrad D hsm s hs y)
    (fun s hs _C₁ _C₂ h₁ h₂ hne =>
      disjoint_irreducibleComponents_strictTransform hres hB hrad D hsm s hs h₁ h₂ hne)
    t ht C hC hCcl x hx

theorem mem_detachedLocus_of_mem_support_ambientCenter
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    (y : ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t))
    (hy : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y ∈
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) :
    y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t := by
  classical
  have hqc : AlgebraicGeometry.QuasiCompact pY := inferInstance
  refine subset_detachedLocus_of_mem_detachedComponents
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t ?_ mem_irreducibleComponent
  rw [EmbeddedBlowupSequence.mem_detachedComponents]
  refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
  by_contra hsub
  have hCmem : irreducibleComponent y ∈
      irreducibleComponents
        ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    irreducibleComponent_mem_irreducibleComponents y
  have hCfr : irreducibleComponent y ∉
      (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents t := by
    intro hmem
    exact hsub
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).mem_detachedComponents t
        (irreducibleComponent y)).1 hmem).2
  have hCcl : IsClosed (irreducibleComponent y) :=
    isClosed_of_mem_irreducibleComponents _ hCmem
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hCmem.1 hCcl
  have hemb : Topology.IsClosedEmbedding
      ⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base :=
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).isClosedEmbedding_strictTransformι t
  have himcl : IsClosed (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
      irreducibleComponent y) := hemb.isClosedMap _ hCcl
  have himirr : IsIrreducible
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) := hCmem.1.image _ hemb.continuous.continuousOn
  have hgim : IsGenericPoint
      (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ)
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hξ
  have hxi : ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ ∉
      ((((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t).support) :
        Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)) :=
    (D.toEmbeddedBlowupSequence
      (canonicalPrincipalization hres hrad)).notMem_ambientCenter_support_of_isGenericPoint t
      (irreducibleComponent y) hCmem hCfr ξ hξ
  have hagreeId : ∀ x ∈
        (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
          irreducibleComponent y),
      AgreeNear ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
              irreducibleComponent y, himcl⟩ :
            TopologicalSpace.Closeds
              ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t))) x := by
    intro x hx
    exact agreeNear_ideal_vanishingIdeal_image_of_smooth hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl x hx
  have hsubsupp : (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) ⊆
      ((((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t).support) :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)) := by
    refine subset_support_of_agreeNear idealSheafGeometryHypotheses_vanishingIdealAssignment _ _ _ himcl ?_
    intro x hx
    rw [vanishingIdealAssignment_apply]
    exact hagreeId x hx
  have hnz : FunctorialResolution.EmbeddedResolution.NonzeroOnComponents
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) :=
    nonzeroOnComponents_ideal (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad))
      D.nonzeroOnComponents_ker t (le_of_lt ht)
  have hcomp : ∀ E ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t),
      ¬ E ⊆ (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y) := by
    intro E hE hEsub
    exact (FunctorialResolution.EmbeddedResolution.nonzeroOnComponents_iff _).1 hnz E hE (hEsub.trans hsubsupp)
  have hdisj : Disjoint
      (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
        irreducibleComponent y)
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t))) := by
    rw [Set.disjoint_left]
    rintro a ⟨z, hz, rfl⟩ ha
    obtain ⟨E, hE, haE⟩ := Set.mem_iUnion₂.mp ha
    exact strictTransformι_notMem_support_of_mem_boundary hres hB hrad D hsm t (le_of_lt ht) z E hE haE
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      t ht
  have hcert : FunctorialResolution.EmbeddedResolution.PrincipalizationCertificate
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).schemeAt t)
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t)
      ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t) 1
      (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
        (E.support :
          Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
      ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t) := hspec
  have hp : AlgebraicGeometry.Smooth
      (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) := by
    rw [chartLevelStructureMorphism_eq_structureMorphism]
    exact IdealBlowupSequence.smooth_structureMorphism
      (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)) t (le_of_lt ht)
  exact false_of_mem_support_center
    (chartLevelStructureMorphism k Y pY D (canonicalPrincipalization hres hrad) t) hp
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal t)
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).ambientCenter t)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary t,
      (E.support :
        Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt t)))
    hcert
    (⇑((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ''
      irreducibleComponent y)
    himcl himirr
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base ξ)
    (((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransformι t).base y)
    hgim ⟨y, mem_irreducibleComponent, rfl⟩
    (smooth_vanishingIdeal_image_comp_chartLevelStructureMorphism hres hB hrad D hsm t (le_of_lt ht)
      (irreducibleComponent y) hCmem himcl)
    hcomp hxi hdisj hagreeId hy

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
