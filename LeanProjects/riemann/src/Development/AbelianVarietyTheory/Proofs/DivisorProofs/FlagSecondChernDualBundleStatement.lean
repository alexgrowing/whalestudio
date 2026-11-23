import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSecondChernDualBundle
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
theorem _root_.GlobalTheory.T.flag_second_chern_dual_bundle : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S] (r : ℕ) (E : HermVB p r) (fl : Vert.Flag E.E r) (a : ℝ), IsRegSurf p → VMetric.IsFlagCh2 E.cInf fl a → ∃ fl' : Vert.Flag E.dual.E r, VMetric.IsFlagCh2 E.dual.cInf fl' a := by
  first | exact @GlobalTheory.DualFlag.isFlagCh2_dual | exact GlobalTheory.DualFlag.isFlagCh2_dual | (intros; apply GlobalTheory.DualFlag.isFlagCh2_dual <;> assumption)
