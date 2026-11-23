import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_ratio_statement : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := by
  first | exact @GlobalTheory.MassAtRecord.massRatio_at_record | exact GlobalTheory.MassAtRecord.massRatio_at_record | (intros; apply GlobalTheory.MassAtRecord.massRatio_at_record <;> assumption)
