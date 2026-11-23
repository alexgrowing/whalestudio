import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarEquivalenceGenerators.ScalarEquivOfGen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scalar_equiv_of_general (h : PI.ScalPairs.ScalarEquivG) (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) :
    PI.ScalPairs.ScalarEquiv D u u' :=
  PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.scalarEquiv_of_gen h D u u'
