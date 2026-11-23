import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransform
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_modularS_transform : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → (∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) → cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  first | exact @GlobalTheory.Sieg.cth_modular_S | exact GlobalTheory.Sieg.cth_modular_S | (intros; apply GlobalTheory.Sieg.cth_modular_S <;> assumption)
