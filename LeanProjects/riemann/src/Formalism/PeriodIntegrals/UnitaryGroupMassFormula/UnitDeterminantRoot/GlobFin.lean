import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobVol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitDeterminantRoot.GlobTop

noncomputable section
open scoped NumberField

namespace PI.UnitaryGroupMassFormula.UnitDetRoot

open PI

theorem globalLUnit : GlobalLUnit :=
  globalLUnit_of
    (fun F _ _ _ _ _ c h => vol_smul_le F c h)
    (fun F _ _ _ δ Λ => vol_img F δ Λ)
    (fun _ _ _ _ _ _ _ _ _ _ _ hok => vol_std_le hok)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => vol_std_ne_bot)

end PI.UnitaryGroupMassFormula.UnitDetRoot
