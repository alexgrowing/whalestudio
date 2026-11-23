import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentFiniteOfTriangularSignedIndicators
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_finite_of_triangular_signed_indicators : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by
  first | exact @GlobalTheory.LaurentFinite.finite_of_triangular | exact GlobalTheory.LaurentFinite.finite_of_triangular | (intros; apply GlobalTheory.LaurentFinite.finite_of_triangular <;> assumption)
