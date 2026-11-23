import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem rowDict_goodOp_nonempty :
    ∀ (D : D7) (X : HidaSetting D), Nonempty (Formalism.L2.SG.RowDict.GoodOp X) :=
  fun _ X => Formalism.L2.SG.Pf.rowDictGoodOp_exists X

end GlobalTheory
