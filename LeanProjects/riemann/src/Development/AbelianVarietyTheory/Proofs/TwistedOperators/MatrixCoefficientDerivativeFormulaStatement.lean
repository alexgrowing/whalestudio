import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDerivativeFormula
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_derivative_formula : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g = ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  first | exact @GlobalTheory.MatCoefDeriv.Eab_coef | exact GlobalTheory.MatCoefDeriv.Eab_coef | (intros; apply GlobalTheory.MatCoefDeriv.Eab_coef <;> assumption)
