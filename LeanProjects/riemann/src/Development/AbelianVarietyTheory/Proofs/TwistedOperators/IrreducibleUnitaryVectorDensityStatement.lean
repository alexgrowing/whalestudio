import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryVectorDensity
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducibleUnitary_vector_density : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) → ∀ (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)), (∀ g, ∑ j, Λ j (π g (a j)) = 0) → ∀ φ u : H, ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  first | exact @GlobalTheory.irreducibleUnitary_density | exact GlobalTheory.irreducibleUnitary_density | (intros; apply GlobalTheory.irreducibleUnitary_density <;> assumption)
