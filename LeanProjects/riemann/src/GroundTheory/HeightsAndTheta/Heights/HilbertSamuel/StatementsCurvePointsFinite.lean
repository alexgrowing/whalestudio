import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.CurveComplexPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def CurvePointsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → Finite (GroundTheory.Heights₂.Heights.projPts W)

end GroundTheory.Heights₂.Heights.HilbertSamuel
