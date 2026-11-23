import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_third_property : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  first | exact @GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | exact GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective | (intros; apply GlobalTheory.CompanionTheory.UnitNorm.norm_units_surjective <;> assumption)
