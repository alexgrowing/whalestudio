import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingFunctionalLowDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_functional_low_degree : ∀ (n : ℕ) (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ), (∀ (σ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℝ), ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P) → ∀ (P : MvPolynomial (Fin n) ℝ) (d : ℕ), P.IsHomogeneous d → d < ∑ i : Fin n, (i : ℕ) → ψ P = 0 := by
  first | exact @GlobalTheory.AltLowDeg.alt_eq_zero_of_lt | exact GlobalTheory.AltLowDeg.alt_eq_zero_of_lt | (intros; apply GlobalTheory.AltLowDeg.alt_eq_zero_of_lt <;> assumption)
