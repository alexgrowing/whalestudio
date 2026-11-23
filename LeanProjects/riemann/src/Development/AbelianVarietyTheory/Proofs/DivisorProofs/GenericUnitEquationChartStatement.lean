import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUnitEquationChart
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
theorem _root_.GlobalTheory.T.generic_unit_equation_chart : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag)
    (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (e : ℕ) (c' : AlgChart (Φ.C k).Y.str σ e) (p0 : (Φ.C k).Y.pts σ),
    p0 ∈ c'.finChart.source → (Φ.C k).π (under p0) ∉ genBd s.T.Z →
    ∃ (t : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Φ.C k).Y.Fnˣ) (U : (Φ.C k).Y.X.Opens)
      (Zm : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin j) (Fin (N - j)) ℂ)
      (GW : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin j) (Fin j) ℂ)
      (GΩ : D.what₂.Tau → (Fin e → ℂ) → Matrix (Fin (N - j)) (Fin (N - j)) ℂ) (cW cΩ : D.what₂.Tau → ℝ),
      under p0 ∈ U ∧ (∀ y' ∈ U, ∀ τ i, ((Φ.C k).gr τ i).IsEqn y' (t τ i)) ∧ (∀ τ, 0 < cW τ) ∧ (∀ τ, 0 < cΩ τ) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => Zm τ w a b) v) ∧
        (∀ τ a b, AnalyticAt ℂ (fun w => GW τ w a b) v) ∧ (∀ τ a b, AnalyticAt ℂ (fun w => GΩ τ w a b) v) ∧
        (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) ∧ (∀ τ, IsUnit (GW τ v).det) ∧ (∀ τ, IsUnit (GΩ τ v).det) ∧
        ∀ r : DV.Rt D.what₂.Tau N, (metsOf x Φ k none σ (rootEx S.Dw (DV.tauEmb D r.1) r.2)).h
            (prodPow t (rootEx S.Dw (DV.tauEmb D r.1) r.2)) (c'.finChart.symm v) =
          rootNorm N j (cW r.1) (cΩ r.1) (GW r.1 v) (GΩ r.1 v) (Zm r.1 v) r.2 := by
  first | exact @GlobalTheory.HodgeLocGeo.RootModel.hodge_root_norm_model | exact GlobalTheory.HodgeLocGeo.RootModel.hodge_root_norm_model | (intros; apply GlobalTheory.HodgeLocGeo.RootModel.hodge_root_norm_model <;> assumption)
