import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapPolynomialIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swap_polynomial_identity : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (x y : κ), x ≠ y → ∀ (D : ℕ) (Φ Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), (∀ (P : MvPolynomial κ ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0) → (∀ (P : MvPolynomial κ ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0) → (∀ n : κ → ℤ, Φ (lin (fun z => (n z : ℝ)) ^ (D + 1)) + Φ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (D + 1)) = Ψ (swapPol swapG D x y n)) → ∀ (k : ℕ) (M : MvPolynomial κ ℝ), Φ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k) * mid x y M) = oddHarm k * Ψ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k - 1) * mid x y M) := by
  first | exact @GlobalTheory.BlockPoint.swapPol_polar | exact GlobalTheory.BlockPoint.swapPol_polar | (intros; apply GlobalTheory.BlockPoint.swapPol_polar <;> assumption)
