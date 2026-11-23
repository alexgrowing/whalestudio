import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFormPullbackClosed
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
theorem _root_.GlobalTheory.T.arithmetic_form_pullback_closed : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D D' : ℕ) (h : IsRegVar p D) (h' : IsRegVar q D') (f : Y ⟶ X) (hf : f ≫ p = q) (j : ℕ) (κ : h.Fld), h.IsArForm j κ → h'.IsArForm j (h.pullFld h' f hf κ) ∧ ∀ σ, ((h.atlas σ).del (κ σ) = 0 → (h'.atlas σ).del (h.pullFld h' f hf κ σ) = 0) ∧ ((h.atlas σ).dbar (κ σ) = 0 → (h'.atlas σ).dbar (h.pullFld h' f hf κ σ) = 0) := by
  first | exact @GlobalTheory.PullArForm.pullFld_isArForm | exact GlobalTheory.PullArForm.pullFld_isArForm | (intros; apply GlobalTheory.PullArForm.pullFld_isArForm <;> assumption)
