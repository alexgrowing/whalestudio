import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLe
import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_re_logDeriv_principalLFunction_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | exact GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | (intros; apply GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le <;> assumption)
