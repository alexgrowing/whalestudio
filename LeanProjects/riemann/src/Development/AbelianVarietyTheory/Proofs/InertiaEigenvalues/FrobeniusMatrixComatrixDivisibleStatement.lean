import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisible
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow : ∀ {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R) (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R), ξ ≠ 0 → B * B' = 1 → c * c' = 1 → V₀ * V₀' = 1 → A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)) → N₀ ≤ N → (∀ i, |(p i : ℤ) - q| ≤ N₀) → (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  first | (exact @GlobalTheory.frobenius_matrix_comatrix_divisible) | (exact GlobalTheory.frobenius_matrix_comatrix_divisible) | (intros; apply GlobalTheory.frobenius_matrix_comatrix_divisible  <;> assumption)
