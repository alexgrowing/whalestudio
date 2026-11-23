import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.DiscAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.StabilizerFixesFrameVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ConjInvOfExists

namespace PI.VolSemiDirect.W

theorem volume_unipotent_of_modulus_one (hM : Cj.ModOne) (hC : PiCont) (hR : PiRat) : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  volume_unipotent_of_adelic Lc.locally_compact_adelic_unitary discrete_adelic_unitary closed_subgroup_holds
    (semiStep_of Lc.locally_compact_adelic_unitary normal_subgroup_holds (projStep_of hC hR)) (Cj.conjStep_of hM)

end PI.VolSemiDirect.W
