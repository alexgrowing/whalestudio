import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefContinuousCompactNormEquiv
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pos_def_continuous_compact_norm_equiv : ∀ (e n : ℕ) (K : Set (Fin e → ℂ)) (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), IsCompact K → ContinuousOn H₀ K → (∀ z ∈ K, (H₀ z).PosDef) → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ K, ∀ v : Fin n → ℂ, c * ‖v‖ ≤ GlobalTheory.HermFrame.gnorm (H₀ z) v ∧ GlobalTheory.HermFrame.gnorm (H₀ z) v ≤ C * ‖v‖ := by
  first | exact @GlobalTheory.posDef_family_gnorm_comparable | exact GlobalTheory.posDef_family_gnorm_comparable | (intros; apply GlobalTheory.posDef_family_gnorm_comparable <;> assumption)
