import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToddPartLowDegree
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
theorem _root_.GlobalTheory.T.todd_part_low_degree : ∀ r : ℕ, tdPart r 1 = (1 / 2 : ℚ) • chPart r 1 ∧ tdPart r 2 = (1 / 8 : ℚ) • chPart r 1 ^ 2 - (1 / 12 : ℚ) • chPart r 2 := by
  first | exact @GlobalTheory.ToddLow.tdPart_low | exact GlobalTheory.ToddLow.tdPart_low | (intros; apply GlobalTheory.ToddLow.tdPart_low <;> assumption)
