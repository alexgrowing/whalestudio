import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricBoundPuncturedPolydisc
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_metric_bound_punctured_polydisc : ∀ (e m n k : ℕ) (hk : k ≤ n) (σ : Fin m → Option (Fin e)) (ρ : ℝ) (φ : (Fin e → ℂ) → Fin n → ℂ), 0 < ρ → DifferentiableOn ℂ φ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) → (∀ z ∈ punct σ ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured hk 1) → ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ punct σ ρ', ∀ w, GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram k (φ z)) (fderiv ℂ φ z w) ≤ C * GlobalTheory.HermFrame.gnorm (modelGram σ z) w := by
  first | exact @GlobalTheory.CurvInterp.schwarz_punct | exact GlobalTheory.CurvInterp.schwarz_punct | (intros; apply GlobalTheory.CurvInterp.schwarz_punct <;> assumption)
