import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_change_of_variables : GlobalTheory.CompanionTheory.LocVan.NilChange := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag | exact GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag | (intros; apply GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag <;> assumption)
