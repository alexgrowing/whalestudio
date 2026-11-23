import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqOfExactRealFormCurve
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_of_exact_real_form_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (h : IsRegVar p 1) (σ : k →+* ℂ) (α β : (h.atlas σ).Fld), (h.atlas σ).IsRealForm 1 α → (h.atlas σ).IsExact (α - β) → (h.atlas σ).integral α = (h.atlas σ).integral β := by
  first | exact @GlobalTheory.ExactIntegral.integral_eq_of_isExact_curve | exact GlobalTheory.ExactIntegral.integral_eq_of_isExact_curve | (intros; apply GlobalTheory.ExactIntegral.integral_eq_of_isExact_curve <;> assumption)
