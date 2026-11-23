import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticOrthogonalVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_orthogonal_vanishing : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H), (∀ k t, HasDerivAt (F k) (F (k + 1) t) t) → (∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ)) → (∀ k, inner ℂ u (F k 0) = 0) → ∀ t, inner ℂ u (F 0 t) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | exact GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | (intros; apply GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds <;> assumption)
