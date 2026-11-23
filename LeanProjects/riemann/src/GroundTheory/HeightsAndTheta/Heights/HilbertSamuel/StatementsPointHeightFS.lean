import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PointHeightFS.Statement : Prop :=
  ∀ I : AllFam, I.IsFamily → hhOf I 0 = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
