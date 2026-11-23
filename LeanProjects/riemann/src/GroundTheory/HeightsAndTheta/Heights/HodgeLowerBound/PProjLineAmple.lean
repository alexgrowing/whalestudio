import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ProjLineDim
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ProjLineLaplace
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

theorem ProjLineAmple.proof (hL : LaplacianLogGrowth.Statement) : ProjLineAmple.Statement := by
  intro A hA ha W d hd hW _
  obtain ⟨rfl, rfl⟩ := eq_bot_of_isArithVar_line hd hW
  rw [LineChart.geomDeg_eq_degree hL hA]
  exact_mod_cast ha

end GroundTheory.Heights₂.Heights.LowerBoundFree
