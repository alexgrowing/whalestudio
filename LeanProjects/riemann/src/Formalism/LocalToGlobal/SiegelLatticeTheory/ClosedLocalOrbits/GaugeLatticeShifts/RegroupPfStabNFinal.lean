import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabFlag

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions Formalism.L2.SG.Full

theorem stabilizer_of_neat_level
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabNC :=
  stabNC_of lattice_stabilizer_holds flag_stabilizer_holds (orthogonal_stabilizer_of_neat hN)

end Formalism.L2.SG.Pf.RegroupPf
