import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.VolumeUnipotentOfModulusOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjContAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjRat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HasStableRangeOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CoordW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CoordAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ModOne

theorem volume_unipotent_all_cm : PI.VolSemiDirect.VolumeUnipotentAllCM :=
  PI.VolSemiDirect.W.volume_unipotent_of_modulus_one
    (PI.VolSemiDirect.W.Md.modOne_of PI.VolSemiDirect.W.Md.heisenberg_coordinates_holds
      (PI.VolSemiDirect.W.Md.wMod_of
        (PI.VolSemiDirect.W.Cj.unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles)))
    PI.VolSemiDirect.W.representation_continuous PI.VolSemiDirect.W.projection_preserves_rational
