import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.AllJoin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders

variable {D : D7}

def LevelSharp (A : AllRows D) : Prop :=
  ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k), A.eVec k v = eJk D k (ψ₀ k)

structure AllJoinA (A : AllRows D) : Prop where

  bundle : Formalism.MainNotions.PlaceDegreeData.RowsTie D A.B

  level : LevelSharp A

end Formalism.L2.GlobalTheoryTheory.AllJoin

end
