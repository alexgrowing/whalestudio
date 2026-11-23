import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernCharacterLineBundleExp
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
theorem _root_.GlobalTheory.T.chern_character_line_bundle_exp : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (R : ArRing B h) (L : HermLB p), R.ch (.ofLB L) = ∑ j ∈ Finset.range (D + 2), ((j.factorial : ℚ)⁻¹) • R.c1 L ^ j := by
  first | exact @GlobalTheory.CxForm.ArRing.ch_ofLB | exact GlobalTheory.CxForm.ArRing.ch_ofLB | (intros; apply GlobalTheory.CxForm.ArRing.ch_ofLB <;> assumption)
