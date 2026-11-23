import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlace
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_integration_formula_real_place : IwasawaFormula := by
  first | exact @GlobalTheory.FlagMeas.iwasawaFormula | exact GlobalTheory.FlagMeas.iwasawaFormula | (intros; apply GlobalTheory.FlagMeas.iwasawaFormula <;> assumption)
