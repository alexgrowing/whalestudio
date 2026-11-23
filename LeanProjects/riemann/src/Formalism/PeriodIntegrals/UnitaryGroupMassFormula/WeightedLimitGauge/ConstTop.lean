import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TransW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem constVal_of_unimodW_orbitPush (hU : UnimodW) (hO : OrbitPush) : ConstVal :=
  constVal_of_polarHyp rhsTest transW hU hO polarHyp

theorem constVal_of_orbit (hO : OrbitPush) : ConstVal :=
  constVal_of_unimodW_orbitPush unimodW hO

end PI.RhsWLim.W
