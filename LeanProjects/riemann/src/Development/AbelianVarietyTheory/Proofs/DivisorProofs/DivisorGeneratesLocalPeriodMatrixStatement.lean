import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratesLocalPeriodMatrix
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_generates_local_period_matrix : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) →
  ∃ (Zm : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin O.j) (Fin (O.N - O.j)) ℂ)
    (GW : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin O.j) (Fin O.j) ℂ)
    (GΩ : D.what₂.Tau → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (O.N - O.j)) (Fin (O.N - O.j)) ℂ)
    (cW cΩ : D.what₂.Tau → ℝ) (g : DV.Rt D.what₂.Tau O.N → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ℂ),
    (∀ τ, 0 < cW τ) ∧ (∀ τ, 0 < cΩ τ) ∧ (∀ x, g x y ≠ 0) ∧
    ∀ᶠ v in 𝓝 y, (∀ τ a b, AnalyticAt ℂ (fun w => Zm τ w a b) v) ∧ (∀ τ a b, AnalyticAt ℂ (fun w => GW τ w a b) v) ∧
      (∀ τ a b, AnalyticAt ℂ (fun w => GΩ τ w a b) v) ∧ (∀ x, AnalyticAt ℂ (g x) v) ∧
      (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) ∧ (∀ τ, IsUnit (GW τ v).det) ∧ (∀ τ, IsUnit (GΩ τ v).det) ∧
      ∀ x, GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v)) =
        Real.log ‖g x v‖ + Real.log (rootNorm O.N O.j (cW x.1) (cΩ x.1) (GW x.1 v) (GΩ x.1 v) (Zm x.1 v) x.2) / 2 := by
  first | exact @GlobalTheory.HodgeLocGeo.lnN_root_local | exact GlobalTheory.HodgeLocGeo.lnN_root_local | (intros; apply GlobalTheory.HodgeLocGeo.lnN_root_local <;> assumption)
