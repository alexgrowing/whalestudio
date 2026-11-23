import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_raw_mass_and_genus_mass : ∀ (D : D7) (u : D.what₂.Word), UnitaryVolumeMass.stLem3L0 D u := by
  first | exact @GlobalTheory.Mass.RowsRawMass.main | exact GlobalTheory.Mass.RowsRawMass.main | (intros; apply GlobalTheory.Mass.RowsRawMass.main <;> assumption)
