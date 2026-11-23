import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionChartInjectiveDerivative
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
theorem _root_.GlobalTheory.T.closed_immersion_chart_injective_derivative : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D D' : ℕ) (i : X ⟶ Y), IsClosedImmersion i → ∀ (w : i ≫ q = p) (σ : k →+* ℂ) (c : AlgChart p σ D) (c0 : AlgChart q σ D') (y : CxPts p σ), y ∈ c.e.source → PtsOver.map i w (spMap σ) y ∈ c0.e.source → Function.Injective (fderiv ℂ (c0.e ∘ PtsOver.map i w (spMap σ) ∘ c.e.symm) (c.e y)) := by
  first | exact @GlobalTheory.ImmInj.fderiv_injective | exact GlobalTheory.ImmInj.fderiv_injective | (intros; apply GlobalTheory.ImmInj.fderiv_injective <;> assumption)
