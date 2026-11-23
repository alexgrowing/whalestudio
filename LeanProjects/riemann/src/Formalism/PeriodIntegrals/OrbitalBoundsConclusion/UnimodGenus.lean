import Mathlib
import Formalism.PeriodIntegrals.UnimodGenus
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge

theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
