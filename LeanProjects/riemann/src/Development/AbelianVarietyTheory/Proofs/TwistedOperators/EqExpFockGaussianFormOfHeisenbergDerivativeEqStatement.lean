import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqExpFockGaussianFormOfHeisenbergDerivativeEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), IsUnit (GlobalTheory.FockFamily.blockB J) → ∀ g : V → ℂ, Differentiable ℝ g →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β J x x) := by
  first | exact @GlobalTheory.FockFamily.solution_eq_gauss | exact GlobalTheory.FockFamily.solution_eq_gauss | (intros; apply GlobalTheory.FockFamily.solution_eq_gauss <;> assumption)
