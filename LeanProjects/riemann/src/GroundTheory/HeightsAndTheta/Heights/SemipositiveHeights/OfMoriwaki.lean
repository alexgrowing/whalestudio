import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PNmSmallIntoFS
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PFSSmallFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PSmallFormsFinite
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PFSSmallCountBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem G6ppB.of_moriwaki (hBig : MoriwakiBigStatement) (hHS : MoriwakiHSStatement) : BirationalPullbackPushforwardFormula :=
  G6ppB.proof hBig NmSmallIntoFS.proof (FSSmallFinite.proof SmallFormsFinite.proof)
    (FSSmallCountBound.proof hHS)

end GroundTheory.Heights₂.Heights.ForSecondHalf
