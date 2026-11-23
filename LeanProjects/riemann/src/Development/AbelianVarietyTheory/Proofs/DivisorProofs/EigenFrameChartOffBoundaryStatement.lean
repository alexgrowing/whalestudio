import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameChartOffBoundary
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
theorem _root_.GlobalTheory.T.eigen_frame_chart_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c (embOf κ.e σ) → ∀ (d : ℕ) (c' : AlgChart (Φ.C k).Y.str σ d) (p0 : (Φ.C k).Y.pts σ), p0 ∈ c'.finChart.source → (Φ.C k).π (under p0) ∉ genBd s.T.Z →
    ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (Fr : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)),
    LogKS.chart V ≫ genStr s.T.Z = spMap φ → (Φ.C k).down p0 ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1 →
    ∃ (G : (Fin d → ℂ) → GlobalTheory.FlagBundle.Mat S.Dw.mult ℂ) (z : (Fin d → ℂ) → GlobalTheory.AllWt.Psi A.H → Matrix (Fin S.Dw.p) (Fin S.Dw.q) ℂ)
      (cc : (D.host.E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => G w τ a b) v) ∧
        (∀ τ a b, AnalyticAt ℂ (fun w => z w τ a b) v) ∧ (∀ τ, IsUnit (G v τ).det) ∧ GlobalTheory.PointChern.InDom (z v) ∧
        ∃ hv : (Φ.C k).down (c'.finChart.symm v) ∈ ptsIn (genStr s.T.Z) (embOf κ.e σ) V.1,
          ∀ f : (Φ.C k).FrameAt (c'.finChart.symm v), Fr.IsMap (evHom hv) f → ∀ τ,
            ((x.hodge (embOf κ.e σ)).gram ((Φ.C k).down (c'.finChart.symm v)) f τ)ᵀ =
              (cc τ : ℂ) • (G v τ * GlobalTheory.PointChern.modelGram A.H S.Dw (z v) τ * (G v τ)ᴴ) := by
  first | exact @GlobalTheory.HodgeFlagModel.hodge_gram_model_good | exact GlobalTheory.HodgeFlagModel.hodge_gram_model_good | (intros; apply GlobalTheory.HodgeFlagModel.hodge_gram_model_good <;> assumption)
