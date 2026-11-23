import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionDual
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnSeqShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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
theorem _root_.GlobalTheory.T.self_intersection_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (L : HermLB p) (x : ℝ), IsRegSurf p → L.IsSelfInter x → L.dual.IsSelfInter x := by
  first | exact @GlobalTheory.DualHeight.isSelfInter_dual | exact GlobalTheory.DualHeight.isSelfInter_dual | (intros; apply GlobalTheory.DualHeight.isSelfInter_dual <;> assumption)
