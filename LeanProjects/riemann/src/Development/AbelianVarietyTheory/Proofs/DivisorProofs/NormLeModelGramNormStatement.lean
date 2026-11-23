import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeModelGramNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_model_gram_norm : ∀ (e m : ℕ) (σ : Fin m → Option (Fin e)) (z : Fin e → ℂ), z ∈ punct σ (1 / 2) → ∀ ξ : Fin e → ℂ, ‖ξ‖ ≤ GlobalTheory.HermFrame.gnorm (modelGram σ z) ξ := by
  first | exact @GlobalTheory.CurvInterp.norm_le_gnorm_modelGram | exact GlobalTheory.CurvInterp.norm_le_gnorm_modelGram | (intros; apply GlobalTheory.CurvInterp.norm_le_gnorm_modelGram <;> assumption)
