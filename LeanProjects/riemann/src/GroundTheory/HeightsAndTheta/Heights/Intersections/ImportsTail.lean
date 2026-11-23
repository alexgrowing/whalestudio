import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterHironaka
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPush
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

theorem PoincareLelongAlt.proof (hRes : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (hInt : PtsIntegrableStatement) (hSide : DivPushResSideStatement)
    (hPt : DivPushPointStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_hironaka hRes (resDivPush_of (resExists_of_hironaka hRes) resBridge hInt hSide hPt)

end GroundTheory.Heights₂.Heights.Inter
