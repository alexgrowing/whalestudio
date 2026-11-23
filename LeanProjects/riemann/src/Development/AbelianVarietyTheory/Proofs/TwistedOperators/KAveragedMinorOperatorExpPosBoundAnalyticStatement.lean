import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KAveragedMinorOperatorExpPosBoundAnalytic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kAveragedMinorOperator_exp_pos_bound_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ h : ℝ, GapAtLeast ε lam h → ∀ X, inP ε X → (∀ x : W, 0 ≤ ⟪x, ps ε lam τ w (NormedSpace.exp X) x⟫_ℂ) ∧ ‖ps ε lam τ w (NormedSpace.exp X)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) ∧ AnalyticAt ℂ (ps ε lam τ w) (NormedSpace.exp X) := by
  first | exact @GlobalTheory.SphJet.ps_exp_pos_bound_analytic | exact GlobalTheory.SphJet.ps_exp_pos_bound_analytic | (intros; apply GlobalTheory.SphJet.ps_exp_pos_bound_analytic <;> assumption)
