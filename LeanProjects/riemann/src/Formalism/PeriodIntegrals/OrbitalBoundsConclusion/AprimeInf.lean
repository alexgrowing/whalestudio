import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExEnd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.NuBridge

namespace PI.AprimeInfAsm

open PI.AprimeInfW

theorem aprimeInf_of_hinfCompact (hC : MassDataMassesW.HinfCompact) (hV : GaugeVolUD) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_grp hC (grpStd_full expProdU_holds hV) nuBridge placeJacAll_holds

theorem aprime_infinite_real (hC : MassDataMassesW.HinfCompact) (hV : GaugeVolUD) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_of_hinfCompact hC hV

end PI.AprimeInfAsm
