import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspaces
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_ker_aeval_of_eigenspaces' : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M), (∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) → ∀ p : Polynomial ℂ, p ≠ 0 → FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  first | exact @GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | exact GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces | (intros; apply GlobalTheory.finiteDimensional_ker_aeval_of_eigenspaces <;> assumption)
