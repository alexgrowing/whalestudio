import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

abbrev principalizationOfEmbedding (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    IdealBlowupSequence D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [] :=
  A k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb)
    D.nonzeroOnComponents_ker [] D.sncEmpty

structure ChartIsolationHypotheses (V : VanishingAssignment.{u}) (A : PrincipalizationAlgorithm.{u}) : Prop where
  noetherianSpace_alive : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform i)
  isClosedEmbedding_aliveι : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        Topology.IsClosedEmbedding ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base
  generic_not_mem_member : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ E ∈ (principalizationOfEmbedding k Y pY D A).boundary i,
        ((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ ∉
          (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))
  agreeNear_orderAt_eq_one : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
        AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
            (V ((D.toEmbeddedBlowupSequence A).schemeAt i)
              ⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
          orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1

theorem disjoint_detachedComponent_of_principalizationCertificate
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    (S : EmbeddedBlowupSequence k Y pY) (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)]
    (I : (S.schemeAt i).IdealSheafData) (Mem : Set ↥(S.schemeAt i))
    (hcl : Topology.IsClosedEmbedding ⇑(S.strictTransformι i).base)
    (hmem : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C → ((S.strictTransformι i).base ξ) ∉ Mem)
    (hagree : ∀ C ∈ irreducibleComponents ↥(S.strictTransform i),
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑(S.strictTransformι i).base '' C),
        AgreeNear I (V (S.schemeAt i) ⟨⇑(S.strictTransformι i).base '' C, hC⟩) ((S.strictTransformι i).base ξ) ∧
          orderAt I ((S.strictTransformι i).base ξ) = 1)
    (hcert : ∃ q : S.schemeAt i ⟶ Spec (CommRingCat.of k),
      PrincipalizationCertificate (S.schemeAt i) q I 1 Mem (S.ambientCenter i))
    {C₁ C₂ : Set ↥(S.strictTransform i)}
    (h₁ : C₁ ∈ S.detachedComponents i)
    (h₂ : C₂ ∈ irreducibleComponents ↥(S.strictTransform i))
    (h₂' : C₂ ∉ S.detachedComponents i) :
    Disjoint C₁ C₂ := by
  obtain ⟨q, hq⟩ := hcert
  have hiso := orderOneCentersIsolated_of_principalizationCertificate (V := V) hV hq
  have hC₁comp := ((S.mem_detachedComponents i C₁).1 h₁).1
  have hC₁sub := ((S.mem_detachedComponents i C₁).1 h₁).2
  have hcl₁ : IsClosed C₁ := isClosed_of_mem_irreducibleComponents _ hC₁comp
  have hcl₂ : IsClosed C₂ := isClosed_of_mem_irreducibleComponents _ h₂
  obtain ⟨ξ₁, hξ₁⟩ := QuasiSober.sober hC₁comp.1 hcl₁
  obtain ⟨ξ₂, hξ₂⟩ := QuasiSober.sober h₂.1 hcl₂
  have him1 : IsClosed (⇑(S.strictTransformι i).base '' C₁) := hcl.isClosedMap _ hcl₁
  have him2 : IsClosed (⇑(S.strictTransformι i).base '' C₂) := hcl.isClosedMap _ hcl₂
  have hirr1 : IsIrreducible (⇑(S.strictTransformι i).base '' C₁) :=
    hC₁comp.1.image _ hcl.continuous.continuousOn
  have hirr2 : IsIrreducible (⇑(S.strictTransformι i).base '' C₂) :=
    h₂.1.image _ hcl.continuous.continuousOn
  have hg1 : IsGenericPoint ((S.strictTransformι i).base ξ₁) (⇑(S.strictTransformι i).base '' C₁) :=
    isGenericPoint_image_of_isClosedEmbedding hcl hξ₁
  have hg2 : IsGenericPoint ((S.strictTransformι i).base ξ₂) (⇑(S.strictTransformι i).base '' C₂) :=
    isGenericPoint_image_of_isClosedEmbedding hcl hξ₂
  obtain ⟨hag1, hord1⟩ := hagree C₁ hC₁comp ξ₁ hξ₁ him1
  obtain ⟨hag2, hord2⟩ := hagree C₂ h₂ ξ₂ hξ₂ him2
  have hnotcenter :
      ((S.strictTransformι i).base ξ₂) ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    intro hmem2
    apply h₂'
    rw [S.mem_detachedComponents i C₂]
    exact ⟨h₂, (hg2.mem_closed_set_iff
      (hV.isClosed_support (S.schemeAt i) (S.ambientCenter i))).mp hmem2⟩
  rw [Set.disjoint_left]
  intro x hx1 hx2
  exact hiso
    ⟨⇑(S.strictTransformι i).base '' C₁, ⇑(S.strictTransformι i).base '' C₂,
      (S.strictTransformι i).base ξ₁, (S.strictTransformι i).base ξ₂, (S.strictTransformι i).base x,
      him1, him2, hirr1, hirr2, hg1, hg2, ⟨x, hx1, rfl⟩, ⟨x, hx2, rfl⟩⟩
    rfl hC₁sub hnotcenter (hmem C₁ hC₁comp ξ₁ hξ₁) (hmem C₂ h₂ ξ₂ hξ₂) hag1 hord1
    ((one_le_orderAt_iff_mem_support I ((S.strictTransformι i).base ξ₂)).1 (le_of_eq hord2.symm))

theorem disjoint_detachedComponent_canonicalPrincipalization
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hind : ChartIsolationHypotheses V (canonicalPrincipalization hres hrad))
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ)
    (hi : i < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length)
    {C₁ C₂ : Set ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform i)}
    (h₁ : C₁ ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents i)
    (h₂ : C₂ ∈ irreducibleComponents
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform i))
    (h₂' : C₂ ∉ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedComponents i) :
    Disjoint C₁ C₂ := by
  have := hind.noetherianSpace_alive k Y pY D i (le_of_lt hi)
  have hspec := (PrincipalizationRules.isMaxOrderReduction_outputLevelData (canonicalAlgorithmRules hres) hB
      (krullDimSucc D.ambient)).cert
      (markedTripleOrderOne k D.ambient D.ambientStruct (AlgebraicGeometry.Scheme.Hom.ker D.emb) [])
      (markedTripleOrderOne_isAdmissible k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker [] D.sncEmpty)
      (le_of_eq (markedTripleOrderOne_dim k D.ambient D.ambientStruct
        (AlgebraicGeometry.Scheme.Hom.ker D.emb) []))
      i hi
  refine disjoint_detachedComponent_of_principalizationCertificate hV
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) i
    ((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).ideal i)
    (⋃ E ∈ (principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).boundary i,
      (E.support : Set ↥((principalizationOfEmbedding k Y pY D (canonicalPrincipalization hres hrad)).schemeAt i)))
    (hind.isClosedEmbedding_aliveι k Y pY D i (le_of_lt hi)) ?_ ?_ ⟨_, hspec⟩ h₁ h₂ h₂'
  · intro C hC ξ hξ hx
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx
    exact hind.generic_not_mem_member k Y pY D i (le_of_lt hi) C hC ξ hξ E hE hxE
  · exact hind.agreeNear_orderAt_eq_one k Y pY D i (le_of_lt hi)

theorem detachedLocusIsOpen_toEmbeddedBlowupSequence
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hind : ChartIsolationHypotheses V (canonicalPrincipalization hres hrad))
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) :
    EmbeddedBlowupSequence.DetachedLocusIsOpen (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) := by
  intro i hi
  have := hind.noetherianSpace_alive k Y pY D i (le_of_lt hi)
  rw [EmbeddedBlowupSequence.detachedLocus_eq_sUnion]
  exact isOpen_sUnion_of_irreducibleComponents _
    (fun C₁ hC₁ C₂ hC₂ hC₂' =>
      disjoint_detachedComponent_canonicalPrincipalization hV hres hB hrad hind k Y pY D i hi hC₁ hC₂ hC₂')

theorem detachedLocusIsOpenForEmbeddings_canonicalPrincipalization
    {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hind : ChartIsolationHypotheses V (canonicalPrincipalization hres hrad)) :
    DetachedLocusIsOpenForEmbeddings (canonicalPrincipalization hres hrad) := by
  intro k _ _ Y pY _ _ _ _ D
  exact detachedLocusIsOpen_toEmbeddedBlowupSequence hV hres hB hrad hind k Y pY D

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
