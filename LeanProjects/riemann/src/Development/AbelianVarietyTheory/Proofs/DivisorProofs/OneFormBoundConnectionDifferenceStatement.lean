import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormBoundConnectionDifference
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_form_bound_connection_difference : ∀ (e m n : ℕ) (σ : Fin m → Option (Fin e)) (ρ C : ℝ) (H₀ H : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), 0 < ρ → GlobalTheory.HermFrame.IsPosFrame (Metric.ball 0 ρ) H₀ → GlobalTheory.HermFrame.OneFormBound (punct σ ρ) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (modelGram σ) (GlobalTheory.HermFrame.conn H) C → ∃ ρ' C' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ GlobalTheory.HermFrame.OneFormBound (punct σ ρ') H₀ (modelGram σ) (fun z ξ => GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H₀ z ξ) C' ∧ GlobalTheory.HermFrame.TwoFormBound (punct σ ρ') H₀ (modelGram σ) (GlobalTheory.HermFrame.curv H₀) C' := by
  first | exact @GlobalTheory.CurvInterp.bound_conn_sub_curv | exact GlobalTheory.CurvInterp.bound_conn_sub_curv | (intros; apply GlobalTheory.CurvInterp.bound_conn_sub_curv <;> assumption)
