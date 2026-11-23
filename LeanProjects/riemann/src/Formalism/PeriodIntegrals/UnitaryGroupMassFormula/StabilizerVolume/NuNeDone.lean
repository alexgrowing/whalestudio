import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuNeFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStabFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnimodStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear

namespace PI.VolStabS

theorem nuNeZero_of_open (hLam : LamEx) (hFV : FinVolStab) (hIS : InvStab) (hAC : AdmCpt) (hS : SWeqOm) :
    NuNeZero :=
  nuNeZero_of_route hLam hFV hIS hAC exFDStab_holds hS witt_holds invInv_holds measOrb_holds
    measGrp_holds testNear_holds

end PI.VolStabS
