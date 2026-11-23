import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.UnrealifyRL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.ChartZeroEqOneOfLongWeylSq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideAUnrealifyRL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideBUnrealifyRL

theorem sandwich_of_chart : PI.SwSand.SandwichOf :=
  PI.SwSandwichOfWork.sandwichOf_of_charts PI.SwSandwichOfWork.normRL PI.SwSandwichOfWork.logG
    PI.SwSandwichOfWork.chartFwd PI.SwSandwichOfWork.chartBwd PI.SwSandwichOfWork.sideB
    PI.SwSandwichOfWork.sideA
