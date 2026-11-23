import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralIsTopFormCurve
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
theorem _root_.GlobalTheory.T.integral_is_top_form_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (θ : h.Fld), (∀ σ, (h.atlas σ).IsForm (θ σ)) → IsTopForm (fun σ (c : AlgChart p σ 1) y => (dens ((h.atlas σ).loc (θ σ) c (c.e y))).re) (h.integral θ) := by
  first | exact @GlobalTheory.TorsionForm.isTopForm_reDens | exact GlobalTheory.TorsionForm.isTopForm_reDens | (intros; apply GlobalTheory.TorsionForm.isTopForm_reDens <;> assumption)
