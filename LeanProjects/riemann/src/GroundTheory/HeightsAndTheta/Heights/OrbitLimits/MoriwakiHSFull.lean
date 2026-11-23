import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHS
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountUpper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionRingFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsCoordNeZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnipotentCharacter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SecMRankBound.full : SecMRankBound.Statement :=
  SecMRankBound.proof GenericFibreVar.proof

theorem SublatticeDegree.full : SublatticeDegree.Statement :=
  SublatticeDegree.proof SublatticeExtension.proof SpanningExtension.proof CovolumeLeGram.proof
    GramContraction.proof

theorem PackingStatement.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.PackingStatement :=
  SmallPacking.proof (NmSectionsRankBound.proof (NmSectionsFinite.proof hC) SecMRankBound.full)
    (SmallSectionsSeparated.proof hG)

theorem SuccessiveMinimaSpan.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement) : SuccessiveMinimaSpan.Statement :=
  SuccessiveMinimaSpan.proof
    (SectionRingFinite.proof (SectionLatticeFinite.proof hC)
      (SectionSpanStep.proof (SpanStepHomog.proof (SpanStepLocal.proof (RelLatticeFinite.proof hR)))
        SerreGraded.proof))
    SectionBounded.proof SectionBoundedMul.proof

theorem G7.of_leaves (hC : KH.CondStatement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : G7.Statement :=
  G7.proof (SuccessiveMinimaSpan.of_leaves hC hR)
    (EuclideanSections.proof (EuclideanSectionsPower.proof hL2 hP) SmallSectionsNonzero.proof
      SublatticeDegree.full (SuccessiveMinimaSpan.of_leaves hC hR))

theorem NefCountLower.of_leaves (hM : NefCountAlongMultiples.Statement)
    (hS : NefSmallSectionEventually.Statement) (hC : KH.CondStatement) (hG : GridSeparation.Statement) :
    NefCountLower.Statement :=
  NefCountLower.proof hM hS (PackingStatement.of_leaves hC hG)

theorem NefCountUpper.of_leaves (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (hC : KH.CondStatement) (hG : GridSeparation.Statement) (hR : RelSectionsLarge.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) : NefCountUpper.Statement :=
  NefCountUpper.proof hApx hCurve (G7.of_leaves hC hR hL2 hP) (PackingStatement.of_leaves hC hG)

theorem MoriwakiHS.of_leaves (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hR : RelSectionsLarge.Statement) (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_found (NefCountLower.of_leaves hM hS hC hG)
    (NefCountUpper.of_leaves hApx hCurve hC hG hR hL2 hP)

end GroundTheory.Heights₂.Heights.Targets
