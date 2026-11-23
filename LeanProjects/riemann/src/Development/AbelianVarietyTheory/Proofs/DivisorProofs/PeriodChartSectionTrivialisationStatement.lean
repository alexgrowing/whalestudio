import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartSectionTrivialisation
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
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
theorem _root_.GlobalTheory.T.period_chart_section_trivialisation : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex →
    ∀ (v : V D) (z : Fin g → ℂ), v ∈ c.e.target → ∀ (c₀ : GlobalTheory.VB.Chart (omega A) g) (W₁ : A.left.Opens)
      (hU : c₀.U ≤ unitSec A ⁻¹ᵁ W₁) (h : Fin g → Γ(A.left, W₁)), (∀ a, c₀.e a = dUnit A hU (h a)) →
      c.e.symm v ∈ ptsIn p σ c₀.U → ∀ (W : A.left.Opens) (F : Γ(A.left, W)), ex (v, z) ∈ ptsIn _ σ W →
      (Matrix.of fun i a => cot ex W₁ (h a) v i) *ᵥ
          ((c₀.pull w.isVB A.hom).map (GlobalTheory.RelCotAb.relCotIso A)).crd _ σ (dRel A.hom W F) (ex (v, z)) =
        cotAt ex W F (v, z) := by
  first | exact @GlobalTheory.RelCotAb.cot_mulVec_crd | exact GlobalTheory.RelCotAb.cot_mulVec_crd | (intros; apply GlobalTheory.RelCotAb.cot_mulVec_crd <;> assumption)
