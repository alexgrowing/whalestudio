import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFourthProperty
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.L4 := by
  first | exact @GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | exact GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent | (intros; apply GlobalTheory.CompanionTheory.UnitLattice.cstable_iff_and_twCent <;> assumption)
