import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPderivDifference
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_pderiv_difference : ∀ (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ), ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P) → ∀ (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin (n + 1)), (i' : ℕ) = i + 1 → ∀ J : MvPolynomial (Fin (n + 1)) ℝ, J.IsHomogeneous (∑ j : Fin (n + 1), (j : ℕ) + 1) → MvPolynomial.pderiv i' J - MvPolynomial.pderiv i J = (∏ j : Fin (n + 1), (-MvPolynomial.X (σ j)) ^ (n - (j : ℕ))) + (∏ j : Fin (n + 1), (-MvPolynomial.X (Equiv.swap i i' (σ j))) ^ (n - (j : ℕ))) → ψ J = ((Equiv.Perm.sign σ : ℤ) : ℝ) * (2 / ((n : ℝ) + 1)) * (((σ 0 : ℕ) : ℝ) - ((Equiv.swap i i' (σ 0) : ℕ) : ℝ)) * ψ ((∑ j : Fin (n + 1), MvPolynomial.X j) * ∏ j : Fin (n + 1), (-MvPolynomial.X j) ^ (n - (j : ℕ))) := by
  first | exact @GlobalTheory.AltPrim.alt_value | exact GlobalTheory.AltPrim.alt_value | (intros; apply GlobalTheory.AltPrim.alt_value <;> assumption)
