import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_points_stabilizer : ∀ τ₀ : ℍ, (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧ (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  first | exact @GlobalTheory.EllipticZero.elliptic_of_zero | exact GlobalTheory.EllipticZero.elliptic_of_zero | (intros; apply GlobalTheory.EllipticZero.elliptic_of_zero <;> assumption)
