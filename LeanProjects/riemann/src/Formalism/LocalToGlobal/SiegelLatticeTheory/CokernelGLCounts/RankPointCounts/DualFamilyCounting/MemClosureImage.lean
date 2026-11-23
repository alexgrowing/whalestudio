import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibT
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

theorem mem_closure_image {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (H : AddSubgroup A)
    (y : B) : y ∈ AddSubgroup.closure (f '' (H : Set A)) ↔ ∃ t ∈ H, f t = y := by
  rw [← AddSubgroup.coe_map, AddSubgroup.closure_eq, AddSubgroup.mem_map]

variable {D : D7} (X : HidaSetting D)

def embHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' x y := by funext v; simp [embV]

theorem mem_cl_emb (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (y : InfinitePlace X.B.I.F → ℂ) :
    y ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embV X t = y := by
  have := mem_closure_image (embHom X) ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) y
  exact this

theorem theta_spec (D : D7) : IsIntegral ℤ (theta D) ∧ theta D + D.host.conj (theta D) = 1 := by
  have h := thetaEx_holds D
  unfold theta
  rw [dif_pos h]
  exact h.choose_spec

end Onto

end Formalism.L2.SG.Pf.NcReal.JX.NOf
