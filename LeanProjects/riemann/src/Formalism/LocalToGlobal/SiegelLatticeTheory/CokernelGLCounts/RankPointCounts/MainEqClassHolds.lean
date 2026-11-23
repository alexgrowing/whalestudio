import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqClass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictAll

noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc
  Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

theorem liftIotaEqC_holds : LiftIotaEqC :=
  fun _ _ Y u _ s₁ s₂ _ _ _ _ hr =>
    Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (lam_eq Y u hr) (lam'_eq Y u hr) (congrArg (fun r => r.2.2) hr)

theorem stepClassG_holds : StepClassG := stepClassG_of_liftIota liftIotaEqC_holds

end Formalism.L2.SG.Pf
