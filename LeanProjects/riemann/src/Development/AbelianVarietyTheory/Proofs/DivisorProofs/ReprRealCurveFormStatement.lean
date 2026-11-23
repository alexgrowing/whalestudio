import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprRealCurveForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar BottChern ArRing ArChow HolAtlas Alt IsType IsReal dens chPart tdPart hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repr_real_curve_form : ∀ (t : ℝ) (α : Alt 1), IsType 1 1 α → IsReal α → ⇑((bas 1).repr (algebraMap ℂ (Alt 1) t + α)) = curveForm t (dens α).re := by
  first | exact @GlobalTheory.CxForm.repr_const_add_eq_curveForm | exact GlobalTheory.CxForm.repr_const_add_eq_curveForm | (intros; apply GlobalTheory.CxForm.repr_const_add_eq_curveForm <;> assumption)
