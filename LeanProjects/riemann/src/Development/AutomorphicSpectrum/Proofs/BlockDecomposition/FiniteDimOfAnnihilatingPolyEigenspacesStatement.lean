import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_of_annihilating_poly_eigenspaces : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M), (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 → (∀ v ∈ V, Polynomial.aeval T p v = 0) → (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | exact GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | (intros; apply GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces <;> assumption)
