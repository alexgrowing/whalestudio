import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSquares
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_squares : ∀ {n : ℕ} (z : Fin n → ℂ), (Matrix.of fun i j : Fin n => (z i ^ 2) ^ (n - 1 - (j : ℕ))).det = (Matrix.of fun i j : Fin n => z i ^ (n - 1 - (j : ℕ))).det * ∏ p ∈ prs n, (z p.1 + z p.2) := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | exact GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq | (intros; apply GlobalTheory.CompanionTheory.CoefId.det_vandermonde_sq <;> assumption)
