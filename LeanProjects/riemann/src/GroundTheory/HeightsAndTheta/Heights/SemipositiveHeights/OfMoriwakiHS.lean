import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.OfMoriwakiHS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

theorem Z1.of_moriwakiHS (hM : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement) : ReciprocityTheory.ChartRestriction.G.Geo.SuccessiveMinimaLowerBound :=
  LowerBoundFree.Z1.proof hM HilbertSamuel.BirationalModelExists.proof

end GroundTheory.Heights₂.Heights.ForSecondHalf
