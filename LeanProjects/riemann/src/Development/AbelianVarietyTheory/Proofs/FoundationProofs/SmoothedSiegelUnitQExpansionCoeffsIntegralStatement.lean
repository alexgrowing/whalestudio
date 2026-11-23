import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral : ∀ (c M a : ℕ), 0 < M → a < M → ∃ k : ℤ, ∀ b : ℕ, admitted c ![(a : ℚ) / M, (b : ℚ) / M] → ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ A 0 ≠ 0 ∧ (∀ n, A n ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) ∧ (Nat.Coprime c M → ∀ n, A n ∈ Subring.closure {ee (1 / (M : ℂ))}) ∧ (b = 0 → ∀ n, ∃ z : ℤ, A n = z) := by
  first | exact @GlobalTheory.SiegQ.sg_expansion_int | exact GlobalTheory.SiegQ.sg_expansion_int | (intros; apply GlobalTheory.SiegQ.sg_expansion_int <;> assumption)
