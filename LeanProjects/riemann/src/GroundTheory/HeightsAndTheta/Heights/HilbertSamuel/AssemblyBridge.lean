import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.proof

theorem BlockResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof BlockResolutionMixedBridge.full BlockResolutionInterpIntegral.full

theorem ResolutionMixedBridge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.proof

theorem ResolutionMixedIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof ResolutionMixedBridge.full ResolutionInterpIntegral.full

theorem Closed.Inter.pullbackPushforward_holds : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.proof Closed.Inter.BlockGenFinite Closed.Inter.FibreIsolFinite

theorem Closed.Inter.pullbackDensity_holds : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.ResBridge : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.resBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
