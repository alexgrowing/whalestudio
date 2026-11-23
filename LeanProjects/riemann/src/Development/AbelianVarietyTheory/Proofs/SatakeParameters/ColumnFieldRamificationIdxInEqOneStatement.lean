import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.Columns.BaseHost
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
