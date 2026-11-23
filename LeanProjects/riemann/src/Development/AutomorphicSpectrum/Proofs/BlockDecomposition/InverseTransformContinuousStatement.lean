import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformContinuous
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ → Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) → Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | exact GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint <;> assumption)
