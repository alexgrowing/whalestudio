import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupRemoval
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsStrictPullbackBlowupSeq h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hpb hstrict
  have hequiv : ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpushTb
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback hstrict hequiv

theorem isPullbackBlowupSequence_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsPullbackBlowupSequence h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsPullbackBlowupSequence h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h' := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hUstrict : IsStrictPullbackBlowupSeq h' (s.toSequenceOfBlowups.baseChange h') s.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange s.toSequenceOfBlowups h'
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hUstrict hstrict
  have hpushPrune : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    isPushforwardSequenceOfBlowups_withoutIsoBlowups ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN' hpushTb
  have heq : ((s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups).Isomorphic s'.toSequenceOfBlowups :=
    IsPullbackBlowupSequence.isomorphic hUstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hpb
  have hpush' : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    IsPushforwardBlowupSeq.of_isomorphic_source ι' heq hpushPrune
  have hequivT : (((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpush'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsPullbackBlowupSequence.of_isomorphic hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hequivT

end FunctorialResolution.EmbeddedResolution
