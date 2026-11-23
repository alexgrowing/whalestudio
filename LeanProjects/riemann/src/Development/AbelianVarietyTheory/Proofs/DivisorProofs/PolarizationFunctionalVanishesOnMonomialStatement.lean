import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFunctionalVanishesOnMonomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open MvPolynomial GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_functional_vanishes_on_monomial : ∀ (D : ℕ) (Ψ : MvPolynomial (Fin D) ℝ →ₗ[ℝ] ℝ) (j : Fin D), (∀ n : Fin D → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = Ψ (lin (fun i => (Function.update n j 0 i : ℝ)) ^ D)) → Ψ (∏ k, MvPolynomial.X k) = 0 := by
  first | exact @GlobalTheory.Div.polar_prod_eq_zero | exact GlobalTheory.Div.polar_prod_eq_zero | (intros; apply GlobalTheory.Div.polar_prod_eq_zero <;> assumption)
