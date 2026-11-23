import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateProjectionComplex
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_projection_complex : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  first | exact @GlobalTheory.realDiag_conj_coordProj | exact GlobalTheory.realDiag_conj_coordProj | (intros; apply GlobalTheory.realDiag_conj_coordProj <;> assumption)
