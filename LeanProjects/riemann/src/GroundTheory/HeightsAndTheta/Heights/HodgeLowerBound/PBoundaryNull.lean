import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryPtsNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BoundaryNull.proof : BoundaryNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  exact BoundaryPtsNull.proof II Ψ K ι Ω E D

end GroundTheory.Heights₂.Heights.LowerBoundFree
