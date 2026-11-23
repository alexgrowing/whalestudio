import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStep
import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_set_card_column_step : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | exact GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe <;> assumption)
