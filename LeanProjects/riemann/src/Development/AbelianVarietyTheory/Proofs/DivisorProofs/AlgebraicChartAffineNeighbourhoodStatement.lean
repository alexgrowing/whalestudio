import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartAffineNeighbourhood
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinatesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_chart_affine_neighbourhood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (d : ℕ) (c' : AlgChart Y.Y.str σ d) (p0 : Y.Y.pts σ), p0 ∈ c'.finChart.source →
    ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1))
      (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (Am : ∀ τ : E →+* ℂ, (Fin d → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      under p0 ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ Y.down p0 ∈ ptsIn (genStr Z) (embOf e σ) V.1 ∧
      (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => Am τ w a b) v) ∧
        ∃ (hv : Y.down (c'.finChart.symm v) ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt (c'.finChart.symm v)),
          Y.Adapted _ t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = Am τ v := by
  first | exact @GlobalTheory.HodgeLocGeo.exists_frames_analytic_chart | exact GlobalTheory.HodgeLocGeo.exists_frames_analytic_chart | (intros; apply GlobalTheory.HodgeLocGeo.exists_frames_analytic_chart <;> assumption)
