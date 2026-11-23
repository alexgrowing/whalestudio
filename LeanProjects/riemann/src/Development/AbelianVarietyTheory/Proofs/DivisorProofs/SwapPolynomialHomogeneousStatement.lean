import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapPolynomialHomogeneous
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_polynomial_homogeneous : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (x y : κ), x ≠ y → ∀ (φ ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (N : ℕ), (∀ (k d : ℕ) (M : MvPolynomial κ ℝ), M.IsHomogeneous d → 2 * k + d = N → φ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k) * mid x y M) = 1 / (2 * (2 * (k : ℝ) + 1)) * ψ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k + 1) * mid x y M)) → ∀ g : MvPolynomial κ ℝ, g.IsHomogeneous N → MvPolynomial.rename (Equiv.swap x y) g = g → ∃ J : MvPolynomial κ ℝ, J.IsHomogeneous (N + 1) ∧ MvPolynomial.pderiv y J - MvPolynomial.pderiv x J = g ∧ φ g = ψ J := by
  first | exact @GlobalTheory.BlockPoint.SymPrim.exists_primitive_symm | exact GlobalTheory.BlockPoint.SymPrim.exists_primitive_symm | (intros; apply GlobalTheory.BlockPoint.SymPrim.exists_primitive_symm <;> assumption)
