import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsL2MetOfIsL2OnUnifChart
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
theorem _root_.GlobalTheory.T.isL2Metric_of_isUnifChart_of_isL2OnDiagonal : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (σ : k →+* ℂ) (A : Over S) (g D : ℕ) (L : HermLB (A.hom ≫ p)) (M : HermLB p) (ψ : toMod M.B ≅ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsUnifChart c τ ex → IsL2OnDiagonal L M ψ c τ ex → IsL2Metric L (.ofLB M) ψ c τ ex := by
  first | exact @GlobalTheory.TorsionForm.isL2Met_of_isL2On | exact GlobalTheory.TorsionForm.isL2Met_of_isL2On | (intros; apply GlobalTheory.TorsionForm.isL2Met_of_isL2On <;> assumption)
