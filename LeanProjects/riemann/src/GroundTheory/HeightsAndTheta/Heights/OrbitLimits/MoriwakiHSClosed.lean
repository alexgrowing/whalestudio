import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelSectionsLarge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

theorem MoriwakiHS.of_open (hC : KH.CondStatement) (hG : GridSeparation.Statement)
    (hL2 : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement)
    (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement :=
  MoriwakiHS.of_leaves hC hG RelSectionsLarge.full hL2 hP hM hS hApx hCurve

end GroundTheory.Heights₂.Heights.Targets
