import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharClassGradedDegree
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
theorem _root_.GlobalTheory.T.char_class_graded_degree : ∀ (B : BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (R : ArRing B h) (r : ℕ) (E : HermVB p r) (j : ℕ), R.char E (chPart r j) ∈ R.gr j ∧ R.char E (tdPart r j) ∈ R.gr j := by
  first | exact @GlobalTheory.CharDegree.char_chPart_tdPart_mem | exact GlobalTheory.CharDegree.char_chPart_tdPart_mem | (intros; apply GlobalTheory.CharDegree.char_chPart_tdPart_mem <;> assumption)
