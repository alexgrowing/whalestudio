import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeSecondChernFlag
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
theorem _root_.GlobalTheory.T.arithmetic_degree_second_chern_flag : ∀ (B : CxForm.BottChern) (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S] (h : IsRegVar p 1) (R : CxForm.ArRing B h) (r : ℕ) (E : HermVB p r) (fl : Vert.Flag E.E r) (a : ℝ), VMetric.IsFlagCh2 E.cInf fl a → R.deg (R.char E (CxForm.chPart r 2)) = a := by
  first | exact @GlobalTheory.FlagCh2Ring.deg_ch2_eq_flag | exact GlobalTheory.FlagCh2Ring.deg_ch2_eq_flag | (intros; apply GlobalTheory.FlagCh2Ring.deg_ch2_eq_flag <;> assumption)
