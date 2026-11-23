import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MuFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SecondConstantHolds

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_top (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hSp : Sq.SqSplit B) : B.EqP χ :=
  Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ hSp (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

theorem polFam_inhabited : Sq.PolFam (0 : Formalism.L2.Th1.H.Sesq ℂ) (fun _ => (1 : ℂ)) (fun _ : Bool => (⊤ : AddSubgroup ℂ))
    ⊤ ⊥ where
  meet _ _ _ _ := AddSubgroup.mem_top _
  dec _ x _ := ⟨x, AddSubgroup.mem_top _, 0, AddSubgroup.zero_mem _, AddSubgroup.mem_top _, AddSubgroup.zero_mem _, by simp⟩
  semiA _ _ _ _ _ _ _ _ _ _ := by simp [Formalism.L2.Th1.H.altE]
  semiA' _ _ _ _ _ _ _ _ _ _ := by simp [Formalism.L2.Th1.H.altE]

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq
