import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeUnipotentOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeQuotientHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProdHaar

namespace PI.VolSemiDirect.W

theorem volume_unipotent_of_adelic (hLC : LcscHA) (hD : DiscHA) (hCl : ClosedStep) (hSe : SemiStep)
    (hCo : ConjStep) : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  volume_unipotent_of_steps subgroup_locally_compact_holds fundamental_domain_exists product_haar_measure_holds volume_quotient_holds hLC hD hCl hSe hCo

end PI.VolSemiDirect.W
