import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticEquationLocus
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_equation_locus : ∀ {F : Type} [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) {e : ℕ} (c' : AlgChart Y.str σ e)
    (p0 : Y.pts σ), p0 ∈ c'.finChart.source → ∀ (Δ : Y.Dv) (a : Y.Fnˣ) (U : Y.X.Opens), under p0 ∈ U →
    (∀ y' ∈ U, Δ.IsEqn y' a) → ∀ f : Y.Fn, Δ.GeneratesAt (under p0) f →
    ∃ g : (Fin e → ℂ) → ℂ, g (c'.finChart p0) ≠ 0 ∧ ∀ᶠ v in 𝓝 (c'.finChart p0), AnalyticAt ℂ g v ∧
      c'.finChart.symm v ∈ Var.eqnSet σ Δ a ∧ ∀ m : (cxSt F).Met Y σ Δ,
        (cxSt F).pn Y σ Δ m ((cxSt F).cx Y σ f) (c'.finChart.symm v) = ‖g v‖ ^ 2 * m.h a (c'.finChart.symm v) := by
  first | exact @GlobalTheory.HodgeLocCoord.pn_eq_normSq_mul_near | exact GlobalTheory.HodgeLocCoord.pn_eq_normSq_mul_near | (intros; apply GlobalTheory.HodgeLocCoord.pn_eq_normSq_mul_near <;> assumption)
