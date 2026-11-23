import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_different_from_ideal : IdealSt → GlobalTheory.FlatCore.CMDiffSt := by
  first | exact @GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | exact GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt | (intros; apply GlobalTheory.FlatCore.CMDiff.cmDiffSt_of_idealSt <;> assumption)
