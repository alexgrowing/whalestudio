import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlock
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_extension_of_block : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ), s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' → b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | exact GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises | (intros; apply GlobalTheory.CompanionTheory.WittFrame.unitary_adapted_triangularises <;> assumption)
