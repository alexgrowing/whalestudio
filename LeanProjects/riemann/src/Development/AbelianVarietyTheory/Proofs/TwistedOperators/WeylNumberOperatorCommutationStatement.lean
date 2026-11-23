import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutation
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_number_operator_commutation_alt : ∀ (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A] [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A), (∀ x, J (J x) = -x) → (∀ u v, D (u + v) = D u + D v) → (∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v) → (∀ u v, D u * D v - D v * D u = (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1) → (∀ z, c z = D z - Complex.I • D (J z)) → (∀ z, a z = -(D z + Complex.I • D (J z))) → N = ∑ j, c (e j) * a (e j) → (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧ (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧ ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  first | exact @GlobalTheory.weyl_number_operator_commutation | exact GlobalTheory.weyl_number_operator_commutation | (intros; apply GlobalTheory.weyl_number_operator_commutation <;> assumption)
