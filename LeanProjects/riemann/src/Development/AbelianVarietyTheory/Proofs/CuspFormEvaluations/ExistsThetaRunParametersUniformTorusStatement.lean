import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaRunParametersUniformTorus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaRunParameters_uniform_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r m : ℕ), 2 ≤ PT.f E * r → 1 ≤ m → m ^ 4 ≤ PT.f E → (PT.f E : ℝ) ≤ PT.rd E → (PT.f E : ℝ) ^ 2 ≤ PT.rd E → 16 ≤ PT.rd E → ∃ (q : ℕ) (R0 : ℝ), 0 < th (E := E) q R0 ∧ ∀ X : PT E, X.r = r → (∃ τ, X.dim τ ≤ m) → ∃ P : Par X 1, P.q = q ∧ P.R0 = R0 ∧ P.m = m := by
  first | exact @GlobalTheory.ThetaRunParameters.exists_par | exact GlobalTheory.ThetaRunParameters.exists_par | (intros; apply GlobalTheory.ThetaRunParameters.exists_par <;> assumption)
