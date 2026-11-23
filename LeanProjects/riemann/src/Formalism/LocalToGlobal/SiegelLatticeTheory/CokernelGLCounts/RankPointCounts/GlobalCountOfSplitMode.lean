import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ModSideUL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobalCountOfModule

namespace Formalism.L2.SG.LsDatumA

def ModSide0G : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n true)

def ModSideUG : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n true)

theorem modSide0_mode (h0G : ModSide0G) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSide0L F E M hM r n
  · exact h0G F E M hM r n

theorem modSideU_mode (hUG : ModSideUG) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSideUL F E M hM r n
  · exact hUG F E M hM r n

theorem globalCount_of_split_mode (D : Formalism.BasicNotions.D7) (h0G : ModSide0G) (hUG : ModSideUG) : Formalism.MainNotions.ThinScalesBound.T2 D :=
  globalCount_of_module D (fun F _ _ _ E _ _ _ _ M hM => modSide0_mode h0G F E M hM _ _)
    (fun F _ _ _ E _ _ _ _ M hM => modSideU_mode hUG F E M hM _ _)

end Formalism.L2.SG.LsDatumA
