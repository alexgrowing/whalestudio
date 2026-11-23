import Mathlib
import Formalism.PeriodIntegrals.FinOrdRedOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderReduction.EqOneOfIsOfFinOrder
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteOrderReduction.Bridge

open NumberField IsDedekindDomain PI.FinOrdRedOne

theorem finite_order_reduction_one : PI.FinOrdRedOne := by
  intro E _ _ p hp hp3 hU P hpP N β hfin hred
  exact Core.eq_one_of_isOfFinOrder p hp hp3 (Bridge.natCast_ne_zero p hp hU P hpP)
    (Bridge.maximalIdeal_eq p hp hU P hpP) (Bridge.eq_zero_of_forall_dvd p hp hU P hpP) β hfin hred
