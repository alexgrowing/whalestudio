import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoSmulInvOfMulTendstoInvertibleMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_smul_inv_of_mul_tendsto_invertible_matrix : ∀ (r : ℕ) (A U : ℍ → Matrix (Fin r) (Fin r) ℂ) (L : Matrix (Fin r) (Fin r) ℂ) (d : ℍ → ℂ), L.det ≠ 0 → Tendsto (fun τ => A τ * U τ) atImInfty (𝓝 L) → Tendsto (fun τ => d τ • U τ) atImInfty (𝓝 0) → Tendsto (fun τ => d τ • (A τ)⁻¹) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | exact GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible | (intros; apply GlobalTheory.OddFrame.tendsto_smul_inv_of_mul_tendsto_invertible <;> assumption)
