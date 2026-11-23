import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusWeightDecomposition
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_weight_decomposition : PositivityTheory.RgDs.K.TorW := by
  first | exact @GlobalTheory.CompanionTheory.RgDsTor.torW | exact GlobalTheory.CompanionTheory.RgDsTor.torW | (intros; apply GlobalTheory.CompanionTheory.RgDsTor.torW <;> assumption)
