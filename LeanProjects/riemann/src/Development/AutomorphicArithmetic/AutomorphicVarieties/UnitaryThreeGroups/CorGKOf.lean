import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OneCharOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI

namespace UpperTheory.V.U3

theorem corGK_of (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : CorGK := corGK (propGK h.number (oneChar h ha))

theorem caseI (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : HV.CountI := countI (corGK_of h ha)

end UpperTheory.V.U3
