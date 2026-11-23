import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArakelovFormMulFunction
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
theorem _root_.GlobalTheory.T.arakelov_form_mul_function : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (t : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (j : ℕ) (θ : h.Fld), h.IsArForm 0 (fun σ => (h.atlas σ).fn (t σ)) → h.IsArForm j θ → h.IsArForm j ((fun σ => (h.atlas σ).fn (t σ)) * θ) := by
  first | exact @GlobalTheory.ArFormMul.isArForm_fn_mul | exact GlobalTheory.ArFormMul.isArForm_fn_mul | (intros; apply GlobalTheory.ArFormMul.isArForm_fn_mul <;> assumption)
