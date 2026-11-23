import Mathlib
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes

namespace GlobalTheory.St

theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
