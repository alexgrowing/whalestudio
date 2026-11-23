import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitUpperRightBlockOfHeisenbergDerivativeSolut
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockFormApply
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ), Continuous g → g ≠ 0 →
    (∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) →
    IsUnit (GlobalTheory.FockFamily.blockB J) := by
  first | exact @GlobalTheory.FockFamily.isUnit_blockB_of_solution | exact GlobalTheory.FockFamily.isUnit_blockB_of_solution | (intros; apply GlobalTheory.FockFamily.isUnit_blockB_of_solution <;> assumption)
