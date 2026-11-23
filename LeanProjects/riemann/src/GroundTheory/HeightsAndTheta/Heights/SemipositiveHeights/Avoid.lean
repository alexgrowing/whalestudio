import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo

theorem avoid : ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement := by
  intro R _ K _ ι _ Ws hWs
  exact GroundTheory.Heights₂.Heights.Inter.AvoidRing.exists_form_avoid (↑Ws : Set (Ideal (MRingOver R ι)))
    Ws.finite_toSet (fun W hW => hWs W (Finset.mem_coe.mp hW))

end GroundTheory.Heights₂.Heights.ForSecondHalf
