import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfExactTypeZero
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
theorem _root_.GlobalTheory.T.eq_of_exact_type_zero : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α β : A.Fld), (∀ x, IsType 0 0 (α x)) → (∀ x, IsType 0 0 (β x)) → A.IsExact (α - β) → α = β := by
  first | exact @GlobalTheory.ExactZero.eq_of_isExact_sub | exact GlobalTheory.ExactZero.eq_of_isExact_sub | (intros; apply GlobalTheory.ExactZero.eq_of_isExact_sub <;> assumption)
