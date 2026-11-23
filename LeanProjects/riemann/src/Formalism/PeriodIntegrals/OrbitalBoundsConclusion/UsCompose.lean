import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.DegPderivMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand

theorem differential_operator_compose : Formalism.FourierDecayAlt.U.ComposeDD :=
  PI.UnitaryGroupMassFormula.UsCompose.composeDD_of (fun _ X q => PI.UnitaryGroupMassFormula.UsCompose.degDP X q)
    (fun k j ρ => PI.UnitaryGroupMassFormula.UsCompose.degD k j ρ) PI.UnitaryGroupMassFormula.UsCompose.expand
