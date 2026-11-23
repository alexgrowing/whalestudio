import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_generators_of_short_spanning_family : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) → (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L → Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) → ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧ abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧ n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  first | exact @GlobalTheory.exists_isShortGen_of_short_span | exact GlobalTheory.exists_isShortGen_of_short_span | (intros; apply GlobalTheory.exists_isShortGen_of_short_span <;> assumption)
