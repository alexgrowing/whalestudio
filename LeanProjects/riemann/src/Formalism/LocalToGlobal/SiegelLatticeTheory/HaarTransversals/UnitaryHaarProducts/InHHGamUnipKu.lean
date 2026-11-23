import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuGlob

namespace Formalism.L2.SG.PoincareInHH.Cut

open Formalism.L2.SG.Pf.Level

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem gamUnipKu_holds {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) : GamUnipKu X u hK :=
  GU.gamUnipKu_of_projModG X u hK (GU.projModG_holds X) (GU.coreOfProj X) (GU.globStep_holds X u hK)
    (latOfLattice_holds X u)

end Formalism.L2.SG.PoincareInHH.Cut
