import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SkewHermitianDiagonalizable
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_diagonalizable : ∀ (R : Type) [CommRing R] [StarRing R] [Finite (MaximalSpectrum R)] (n : ℕ) (G : Matrix (Fin n) (Fin n) R), Gᴴ = -G → IsUnit G.det → (∀ m : Ideal R, m.IsMaximal → ∃ a : R, a - star a ∉ m) → ∃ T : Matrix (Fin n) (Fin n) R, IsUnit T.det ∧ (T * G * Tᴴ).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag | exact GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag | (intros; apply GlobalTheory.CompanionTheory.CommAlg.skewHermitian_congr_diag <;> assumption)
