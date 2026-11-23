import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionFormCompactBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_form_compact_bound : ∀ (e n : ℕ) (U K : Set (Fin e → ℂ)) (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), GlobalTheory.HermFrame.IsPosFrame U H₀ → IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ ξ : Fin e → ℂ, ∑ a, ∑ b, ‖GlobalTheory.HermFrame.conn H₀ z ξ a b‖ ≤ B * ‖ξ‖ := by
  first | exact @GlobalTheory.HermFrame.conn_sum_bound_on_compact | exact GlobalTheory.HermFrame.conn_sum_bound_on_compact | (intros; apply GlobalTheory.HermFrame.conn_sum_bound_on_compact <;> assumption)
