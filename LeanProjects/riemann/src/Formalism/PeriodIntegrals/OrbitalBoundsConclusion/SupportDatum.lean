import Mathlib
import Formalism.PeriodIntegrals.SupportParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.ModKUnitMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.ExistsMulOfRangeLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Blocks
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.DeterminantFormIdentity

theorem support_vector_all : PI.SupportParts.SupportVecAll :=
  PI.SupportDatumW.supportVecAll_of
    (fun D δ M p _ T T' w w' hk c hw hw' =>
      PI.SupportDatumW.locStep_of PI.SupportDatumW.cokernel_determinant PI.SupportDatumW.determinant_form_identity
        PI.SupportDatumW.topNe D δ M p T T' w w' hk c hw hw')
    PI.SupportDatumW.topNe
