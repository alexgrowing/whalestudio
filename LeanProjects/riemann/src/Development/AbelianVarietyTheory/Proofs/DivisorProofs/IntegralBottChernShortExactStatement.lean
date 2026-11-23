import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBottChernShortExact
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
theorem _root_.GlobalTheory.T.integral_bott_chern_short_exact : ∀ (B : CxForm.BottChern) (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (h : IsRegVar p 1) (S : ShortComplex X.Modules) (hS : S.ShortExact) (r s : ℕ) (g : VMetric p S.X₂ (r + s)) (G : g.IsCInf) (hi : VB.IsSubbundle S.f) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) (σ : k →+* ℂ), (g.met σ).bcMeas hS h₁ h₃ univ ≠ ⊤ → (h.atlas σ).integral (B.bc (h.seq hS (G.restrict hi h₁) G (G.quot hS h₁ h₃) σ)) = -((g.met σ).bcMeas hS h₁ h₃ univ).toReal := by
  first | exact @GlobalTheory.BcUnique.integral_bc_seq | exact GlobalTheory.BcUnique.integral_bc_seq | (intros; apply GlobalTheory.BcUnique.integral_bc_seq <;> assumption)
