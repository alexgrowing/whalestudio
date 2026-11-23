import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapTorusSurjective
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_torus_surjective : PositivityTheory.Rg.Tf.Loc.T0 := by
  first | exact @GlobalTheory.CompanionTheory.LocTop.t0 | exact GlobalTheory.CompanionTheory.LocTop.t0 | (intros; apply GlobalTheory.CompanionTheory.LocTop.t0 <;> assumption)
