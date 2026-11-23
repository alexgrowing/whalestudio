import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormConjSwap
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernTop GlobalTheory.Points
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_form_conj_swap : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (L : HermLB p) (σ σ' : k →+* ℂ) (x : (h.atlas σ).Pt) (x' : (h.atlas σ').Pt), x'.pt.1 = spMap (starRingEnd ℂ) ≫ x.pt.1 → (∀ z ∈ x.ch.source, ∀ z' ∈ x'.ch.source, z'.1 = spMap (starRingEnd ℂ) ≫ z.1 → ∀ a, x'.ch z' a = conj (x.ch z a)) → swap (fld _ (c1F h σ' L) x') = (-1 : ℂ) ^ 1 • fld _ (c1F h σ L) x := by
  first | exact @GlobalTheory.ChernConjForm.swap_c1F_conj | exact GlobalTheory.ChernConjForm.swap_c1F_conj | (intros; apply GlobalTheory.ChernConjForm.swap_c1F_conj <;> assumption)
