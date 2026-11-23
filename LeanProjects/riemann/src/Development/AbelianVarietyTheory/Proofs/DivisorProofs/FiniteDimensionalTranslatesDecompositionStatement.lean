import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalTranslatesDecomposition
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dimensional_translates_decomposition : ∀ (A : Type) [CommGroup A] (Fn : A → ℂ) (Γ U S : Set A) (C : Finset A), (∀ γ ∈ Γ, ∀ t, Fn (γ * t) = Fn t) → (∀ u ∈ U, ∀ t, Fn (t * u) = Fn t) → (∀ t, ∃ γ ∈ Γ, ∃ c ∈ C, ∃ a ∈ S, ∃ u ∈ U, t = γ * c * a * u) → (∀ b : A, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a : S => fun a' : S => Fn (b * a' * a)))) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun s : A => fun t => Fn (t * s))) := by
  first | exact @GlobalTheory.translates_span_finiteDimensional_of_double_coset | exact GlobalTheory.translates_span_finiteDimensional_of_double_coset | (intros; apply GlobalTheory.translates_span_finiteDimensional_of_double_coset <;> assumption)
