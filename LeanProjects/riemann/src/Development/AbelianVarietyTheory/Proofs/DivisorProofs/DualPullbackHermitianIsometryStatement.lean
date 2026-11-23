import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPullbackHermitianIsometry
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
theorem _root_.GlobalTheory.T.dual_pullback_hermitian_isometry : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (f : Y ⟶ X) (hf : f ≫ p = q) (r : ℕ) (E : HermVB p r) (F : Y.Modules) (φ : (Scheme.Modules.pullback f).obj E.E ≅ F), ∃ χ : (E.dual.pull f hf).E ≅ VB.dual F, (E.dual.pull f hf).h.IsIsometry ((E.h.pull f hf).map φ).dual χ := by
  first | exact @GlobalTheory.DualPullMet.exists_isIsometry_dual_pull | exact GlobalTheory.DualPullMet.exists_isIsometry_dual_pull | (intros; apply GlobalTheory.DualPullMet.exists_isIsometry_dual_pull <;> assumption)
