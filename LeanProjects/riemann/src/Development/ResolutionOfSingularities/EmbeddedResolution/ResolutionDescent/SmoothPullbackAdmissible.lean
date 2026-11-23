import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MarkedIdealWithBoundary

theorem isAdmissible_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q]
    (hq : h ≫ T.structMap = q) :
    (T.pullbackAlong Y q h).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hqc : AlgebraicGeometry.QuasiCompact q := inferInstance
  subst hq
  have : AlgebraicGeometry.Smooth (h ≫ T.structMap) := inferInstance
  have : AlgebraicGeometry.Flat h := inferInstance
  refine ⟨hV.charZero, ?_, ?_, hV.one_le_mult, hqc, ?_, ?_⟩
  · show AlgebraicGeometry.LocallyOfFiniteType (h ≫ T.structMap)
    infer_instance
  · exact hV.nonzeroOnComponents.comap_of_flat h
  · show AlgebraicGeometry.Smooth (h ≫ T.structMap)
    infer_instance
  · exact inStrictNormalCrossingPosition_comap T.structMap h T.boundary hV.snc

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution
