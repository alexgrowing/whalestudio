import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateFiniteDimMatrixCoefficient
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_finite_dim_matrix_coefficient : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (Fn : G → ℂ), (∀ s : G, Continuous fun t : G => t * s) → Continuous Fn → (∀ γ ∈ H, ∀ t, Fn (γ * t) = Fn t) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : G => fun t => Fn (t * s))) → ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (a : Fin d → Fin d → ℂ), (∀ γ ∈ H, ρ γ = 1) ∧ (∀ i j, Continuous fun s => ρ s i j) ∧ ∀ t, Fn t = ∑ i, ∑ j, a i j * ρ t i j := by
  first | exact @GlobalTheory.exists_matrix_rep_of_finiteDimensional_translates | exact GlobalTheory.exists_matrix_rep_of_finiteDimensional_translates | (intros; apply GlobalTheory.exists_matrix_rep_of_finiteDimensional_translates <;> assumption)
