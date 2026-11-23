import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicPeriodMatrix
import Mathlib
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_period_matrix : ∀ (n g : ℕ) (U : Set (Fin n → ℂ)) (E F : (Fin n → ℂ) → Fin g → Fin g → ℂ), DifferentiableOn ℂ E U → DifferentiableOn ℂ F U → (∀ s ∈ U, (Matrix.of fun k i => E s i k).det ≠ 0) → ∃ τ : (Fin n → ℂ) → Fin g → Fin g → ℂ, DifferentiableOn ℂ τ U ∧ ∀ s ∈ U, ∀ j, F s j = ∑ i, τ s i j • E s i := by
  first | exact @GlobalTheory.holomorphic_coordinates_in_holomorphic_frame | exact GlobalTheory.holomorphic_coordinates_in_holomorphic_frame | (intros; apply GlobalTheory.holomorphic_coordinates_in_holomorphic_frame <;> assumption)
