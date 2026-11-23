import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SymmetricFormPolynomialCoeff
import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Top.FlDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_form_polynomial_coeff : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) (a : (Fin n → σ) → ℝ), (∀ (π : Equiv.Perm (Fin n)) (w : Fin n → σ), a (w ∘ π) = a w) → ∀ (w₀ : Fin n → σ) (m : σ →₀ ℕ), (∀ p, m p = (Finset.univ.filter fun r => w₀ r = p).card) → coeff m (PB.formPoly n a) * ∏ p, ((m p).factorial : ℝ) = (n.factorial : ℝ) * a w₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | exact GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.CoeffSym.coeff_formPoly_mul <;> assumption)
