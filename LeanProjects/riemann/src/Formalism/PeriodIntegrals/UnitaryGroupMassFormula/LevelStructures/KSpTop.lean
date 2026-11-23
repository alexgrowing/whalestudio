import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.TypedNeOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem finiteDimensional_of_numberField (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : FiniteDimensional F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E

theorem kSpCompact_holds : KSpCompact := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isClosed_Ssub p.1 X.B.I.cm.sig X.B.I.J (frameOf X w)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (LatTop.isCompact_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J)

theorem kSpOpen_holds : KSpOpen := by
  intro D X w p
  have := finiteDimensional_of_numberField X.B.I.F X.B.I.E
  exact (LatTop.isOpen_Kv p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg X.B.I.cm.sig X.B.I.J).preimage
    continuous_subtype_val

theorem typedNe_holds : TypedNe := typedNe_of kSpCompact_holds kSpOpen_holds

end MassDataLevelSSteps
