import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EtaleCoverClosedEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isPullbackBlowupSequence_presentedSelection_of_smooth (E : EmbeddedResolutionRule.{u}) (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (E k V pV (C.sel k V pV)) (E k Y pY (C.sel k Y pY)) := by
  obtain ⟨V'', pV'', c, hV''aff, hV''red, hV''ft, hV''qc, hcet, hcsurj, hcpV,
      ⟨G', f, hG'pres, hfsm, hfcomp, hfpb⟩, ⟨H', g, hH'pres, hgsm, hgcomp, hgpb⟩⟩ :=
    exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth hS hsm k (fun A q hq => hsnc k A q hq)
      Y V pY pV (C.sel k Y pY) (C.pres k Y pY) (C.sel k V pV) (C.pres k V pV) u r hu
  have := hV''aff
  have := hV''red
  have := hV''ft
  have := hV''qc
  have := hcet
  have := hcsurj
  have := hfsm
  have := hgsm
  have : AlgebraicGeometry.Smooth u := AlgebraicGeometry.SmoothOfRelativeDimension.smooth r u
  have : AlgebraicGeometry.Flat u := inferInstance
  have : AlgebraicGeometry.Flat c := inferInstance
  have s1 : IsPullbackBlowupSequence (c ≫ u) (E k V'' pV'' G') (E k Y pY (C.sel k Y pY)) :=
    hsbc k Y V'' pY pV'' (C.sel k Y pY) G' f (c ≫ u) hfcomp hfpb
  have s2 : IsPullbackBlowupSequence c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    hsbc k V V'' pV pV'' (C.sel k V pV) H' g c hgcomp hgpb
  have heq : (E k V'' pV'' G').Isomorphic (E k V'' pV'' H') :=
    hinv k V'' pV'' G' H' hG'pres.some hH'pres.some
  have s2' : IsStrictPullbackBlowupSeq c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    s2.isStrictPullback_of_surjective
      (fun i hi => hprop k V pV (C.sel k V pV) i hi)
  have hBu : IsStrictPullbackBlowupSeq u ((E k Y pY (C.sel k Y pY)).baseChange u)
      (E k Y pY (C.sel k Y pY)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (E k Y pY (C.sel k Y pY)) u
  have hB' : IsPullbackBlowupSequence u ((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups
      (E k Y pY (C.sel k Y pY)) := hBu.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have hCc : IsStrictPullbackBlowupSeq c
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) c
  have hC : IsPullbackBlowupSequence (c ≫ u)
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (E k Y pY (C.sel k Y pY)) := hB'.comp_isStrictPullbackSequenceOfBlowups hCc
  have heq2 : (E k V'' pV'' G').Isomorphic
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c) := s1.isomorphic hC
  have hdesc : (E k V pV (C.sel k V pV)).Isomorphic
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic s2' hCc (heq.symm.trans heq2)
  exact hB'.of_isomorphic hdesc.symm

theorem isCompatibleWithOpenImmersions_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithOpenImmersions (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ φ _ hφ
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  exact isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y V pY pV
    φ 0 hφ

theorem isCompatibleWithEtaleCovers_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithEtaleCovers (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y W pY pW _ _ _ _ _ _ _ _ φ _ hφ hsurj
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  have : AlgebraicGeometry.Surjective φ := ⟨hsurj⟩
  have hpb : IsPullbackBlowupSequence φ (E k W pW (C.sel k W pW)) (E k Y pY (C.sel k Y pY)) :=
    isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y W pY pW
      φ 0 hφ
  exact hpb.isStrictPullback_of_surjective
    (fun i hi => hprop k Y pY (C.sel k Y pY) i hi)

end FunctorialResolution.EmbeddedResolution

end
