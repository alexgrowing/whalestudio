import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEigenLine_degreeFormula : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → DegSt := by
  first | exact @GlobalTheory.CM.PureDeg.degSt | exact GlobalTheory.CM.PureDeg.degSt | (intros; apply GlobalTheory.CM.PureDeg.degSt <;> assumption)
