import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (b : SL(2, ℤ) → ℕ → ℂ), 0 < M → IsReps Γ s → (∀ (x : SL(2, ℤ)) (n : ℕ), b (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * b x n) → (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), b (γ * x) n = b x n) → (∀ (x : SL(2, ℤ)) (n : ℕ), b (-x) n = -b x n) → (∀ i, ∑ n ∈ Finset.range M, b (s i) n = 0) → ∀ (x : SL(2, ℤ)) (n : ℕ), n < M → b x n = 0 := by
  first | exact @GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | exact GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero | (intros; apply GlobalTheory.OddFrame.coeff_eq_zero_of_sum_reps_eq_zero <;> assumption)
