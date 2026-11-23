import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumRowDegreeEqOfHarmonicHighestCasimir
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.JointHarm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_row_degree_eq_of_harmonic_highest_casimir : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (k l n : ℕ) (z : Fin k × Fin n → σ) (y : Fin l × Fin n → σ), Function.Injective z → Function.Injective y → (∀ u w, z u ≠ y w) → ∀ (P : MvPolynomial σ ℂ) (a : Fin k → ℕ) (b : Fin l → ℕ) (κ : Fin n → ℤ), P ≠ 0 → Antitone a → Antitone b → Antitone κ → (∀ i j, i < j → rowOp ℂ z i j P = 0) → (∀ i, rowOp ℂ z i i P = (a i : ℂ) • P) → (∀ i j, i < j → rowOp ℂ y i j P = 0) → (∀ i, rowOp ℂ y i i P = (b i : ℂ) • P) → (∀ i j, ∑ t, pderiv (z (i, t)) (pderiv (y (j, t)) P) = 0) → (∀ i j, i < j → mixedOp ℂ z y i j P = 0) → (∀ t, mixedOp ℂ z y t t P = (κ t : ℂ) • P) → ∑ i, (a i : ℤ) = ∑ t, max (κ t) 0 := by
  first | exact @GlobalTheory.HarmRowDegree.sum_row_degree_eq | exact GlobalTheory.HarmRowDegree.sum_row_degree_eq | (intros; apply GlobalTheory.HarmRowDegree.sum_row_degree_eq <;> assumption)
