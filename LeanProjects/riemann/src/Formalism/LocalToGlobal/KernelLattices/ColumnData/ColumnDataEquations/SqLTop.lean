import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLMain
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.PolFamInhabited

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions

variable {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Cd.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ := by
  exact Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)
    (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
