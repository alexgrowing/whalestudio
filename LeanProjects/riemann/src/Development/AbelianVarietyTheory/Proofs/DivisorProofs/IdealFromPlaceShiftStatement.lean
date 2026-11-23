import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShift
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_from_place_shift : PlaceShiftSt → IdealSt := by
  first | exact @GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | exact GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | (intros; apply GlobalTheory.CMIdeal.idealSt_of_placeShiftSt <;> assumption)
