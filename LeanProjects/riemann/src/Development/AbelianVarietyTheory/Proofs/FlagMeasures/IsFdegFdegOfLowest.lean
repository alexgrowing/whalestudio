import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfOfIsDS
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.LowestVectorDegree

theorem isFdeg_fdegOf_lowest : ∀ (D : D7) (X : HidaSetting D) (v : InfinitePlace X.B.I.F),
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) :=
  fun _ X v => isFdeg_fdegOf_of_isDS (X.ds v) (X.low v).1

end GlobalTheory.LowestVectorDegree
