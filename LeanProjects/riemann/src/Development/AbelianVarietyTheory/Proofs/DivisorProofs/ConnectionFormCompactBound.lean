import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEntryContinuousOn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

theorem GlobalTheory.HermFrame.conn_sum_bound_on_compact : ∀ (e n : ℕ) (U K : Set (Fin e → ℂ)) (H₀ : (Fin e → ℂ) → Matrix (Fin n) (Fin n) ℂ), GlobalTheory.HermFrame.IsPosFrame U H₀ → IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ ξ : Fin e → ℂ, ∑ a, ∑ b, ‖GlobalTheory.HermFrame.conn H₀ z ξ a b‖ ≤ B * ‖ξ‖ := by
  intro e n U K H₀ hH hKc hKU
  obtain ⟨β, hβ⟩ := GlobalTheory.FrameCompact.exists_conn_bound hH hKU hKc
  refine ⟨(n : ℝ) * n * max β 0, by positivity, fun z hz ξ => ?_⟩
  have h1 : ∀ a b : Fin n, ‖GlobalTheory.HermFrame.conn H₀ z ξ a b‖ ≤ max β 0 * ‖ξ‖ := fun a b =>
    (hβ z hz ξ a b).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  calc ∑ a, ∑ b, ‖GlobalTheory.HermFrame.conn H₀ z ξ a b‖ ≤ ∑ _a : Fin n, ∑ _b : Fin n, max β 0 * ‖ξ‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 a b
    _ = (n : ℝ) * n * max β 0 * ‖ξ‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
