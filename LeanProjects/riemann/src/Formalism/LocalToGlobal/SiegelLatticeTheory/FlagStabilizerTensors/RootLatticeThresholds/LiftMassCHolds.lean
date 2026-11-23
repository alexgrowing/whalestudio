import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LiftMassCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem LiftMassC_holds {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) :
    Formalism.L2.SG.Pf.RowForm.LiftMassC X Y u u' :=
  liftMassC_of (Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK)

end Formalism.L2.SG.Pf.FibreCounting
