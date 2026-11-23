import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory

theorem columnLevel_stabTriv :
    ∀ (D : D7) (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) := by
  intro D X hK u h γ hγ

  have hfin : IsOfFinOrder γ :=
    Formalism.L2.SG.PoincareInHH.Cut.gamFinKu_of X u hK
      (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) h γ hγ
  exact Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK h γ hγ hfin

end GlobalTheory
