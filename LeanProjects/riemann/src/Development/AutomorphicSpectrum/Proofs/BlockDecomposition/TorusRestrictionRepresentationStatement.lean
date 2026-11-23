import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRestrictionRepresentation
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_restriction_representation : PositivityTheory.RgDs.K.RhoTorus := by
  first | exact @GlobalTheory.CompanionTheory.RgTorus.rhoTorus | exact GlobalTheory.CompanionTheory.RgTorus.rhoTorus | (intros; apply GlobalTheory.CompanionTheory.RgTorus.rhoTorus <;> assumption)
