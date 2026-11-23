import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapIntegralProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_integral_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement → PositivityTheory.Rg.Tf.Loc.N3 → PositivityTheory.Rg.Tf.Loc.N4 := by
  first | exact @GlobalTheory.CompanionTheory.UnitNorm.exists_integral_norm_of_unit_norm_surjective | exact GlobalTheory.CompanionTheory.UnitNorm.exists_integral_norm_of_unit_norm_surjective | (intros; apply GlobalTheory.CompanionTheory.UnitNorm.exists_integral_norm_of_unit_norm_surjective <;> assumption)
