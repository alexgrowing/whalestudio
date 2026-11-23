import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.GlobalTheory.T.greedy_splitting_principal_torus_exists : SplitStatement := by
  first | exact @GlobalTheory.greedy_splitting_exists | exact GlobalTheory.greedy_splitting_exists | (intros; apply GlobalTheory.greedy_splitting_exists <;> assumption)
