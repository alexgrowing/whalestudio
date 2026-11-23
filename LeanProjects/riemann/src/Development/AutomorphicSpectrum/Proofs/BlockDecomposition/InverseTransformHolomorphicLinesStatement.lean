import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformHolomorphicLines
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_transform_holomorphic_lines : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | exact GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.InvLine.inv_differentiable_line <;> assumption)
