import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LowerBound
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseBoundedHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem HeightLowerBound.main : HeightLowerBound.Statement := heightLowerBound

theorem HeightMetricChange.main : HeightMetricChange.Statement := heightMetricChange

theorem HeightLocalAgreement.main : HeightLocalAgreement.Statement := heightLocalAgreement

theorem HeightPullback.main : HeightPullback.Statement := heightPullback

theorem HeightComparison.main : HeightComparison.Statement := heightComparison

theorem DenseBoundedHeight.main : DenseBoundedHeight.Statement := denseBoundedHeight

theorem SlopeMaxExtension.main : SlopeMaxExtension.Statement := slopeMaxExtension

theorem FlagDegreeBound.main : FlagDegreeBound.Statement := flagDegreeBound

end GroundTheory.Heights₂.Heights
