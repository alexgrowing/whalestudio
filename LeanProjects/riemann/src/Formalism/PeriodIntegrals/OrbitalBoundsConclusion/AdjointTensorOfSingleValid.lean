import Mathlib
import Formalism.PeriodIntegrals.FockRBlock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.OkSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FilterConcatWLength
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.MultidegSingle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.NotMemVarsEmbS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.StepMonoFactor

theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
