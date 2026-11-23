import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealZeroFormEqSmoothFunction
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
theorem _root_.GlobalTheory.T.real_zero_form_eq_smooth_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (σ : k →+* ℂ) (α : (h.atlas σ).Fld), (h.atlas σ).IsRealForm 0 α → ∃ t : CxPts p σ → ℝ, (∀ y, CInfAt t y) ∧ α = (h.atlas σ).fn t := by
  first | exact @GlobalTheory.CxForm.IsRegVar.exists_cInfAt_of_isRealForm_zero | exact GlobalTheory.CxForm.IsRegVar.exists_cInfAt_of_isRealForm_zero | (intros; apply GlobalTheory.CxForm.IsRegVar.exists_cInfAt_of_isRealForm_zero <;> assumption)
