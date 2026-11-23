import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfDeep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem uJClassMass_of_open (s1 : LatStep) (s4 : SurjStep) : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_deep' PI.UnitaryGroupMassFormula.UJClassFin.rational_points_dense s1 s4

end PI.UnitaryGroupMassFormula.UJClassMass
