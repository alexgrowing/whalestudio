import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LuDecompositionUnitriangularUnique
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_decomposition_unitriangular_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (A₁ A₂ N₁ U N₀ : Matrix (Fin m) (Fin m) R), (∀ i j, i < j → A₁ i j = 0) → (∀ i j, i < j → A₂ i j = 0) → (∀ i j, j < i → N₁ i j = 0) → (∀ i, N₁ i i = 1) → (∀ i j, j < i → U i j = 0) → (∀ i, U i i = 1) → (∀ i j, j < i → N₀ i j = 0) → (∀ i, N₀ i i = 1) → A₁ * A₂ * N₁ = U * N₀ → N₁ = U * N₀ := by
  first | exact @GlobalTheory.lu_unique | exact GlobalTheory.lu_unique | (intros; apply GlobalTheory.lu_unique <;> assumption)
