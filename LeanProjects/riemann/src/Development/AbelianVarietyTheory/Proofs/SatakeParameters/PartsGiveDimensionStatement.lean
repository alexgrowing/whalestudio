import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimension
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parts_give_dimension : ∀ D : D7, GlobalTheory.NRows.PartsGive D := by
  first | exact @GlobalTheory.NRows.Parts.main | exact GlobalTheory.NRows.Parts.main | (intros; apply GlobalTheory.NRows.Parts.main <;> assumption)
