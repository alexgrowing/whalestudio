import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveArithmeticKaehlerForm
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
theorem _root_.GlobalTheory.T.exists_positive_arithmetic_kaehler_form : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D), ∃ κ : h.Fld, h.IsArForm 1 κ ∧ ∀ σ, (h.atlas σ).del (κ σ) = 0 ∧ (h.atlas σ).dbar (κ σ) = 0 ∧ ∀ x, (hermMat (κ σ x)).PosDef := by
  first | exact @GlobalTheory.BaseKaehler.exists_kaehler | exact GlobalTheory.BaseKaehler.exists_kaehler | (intros; apply GlobalTheory.BaseKaehler.exists_kaehler <;> assumption)
