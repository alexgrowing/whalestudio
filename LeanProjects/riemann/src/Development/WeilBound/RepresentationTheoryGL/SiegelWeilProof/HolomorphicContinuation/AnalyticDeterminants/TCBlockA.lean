import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TopCompS

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def embL (s : Finset (Fin n)) : Matrix s s ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := embOn s
      map_add' := fun T T' => by
        ext a b
        simp only [embOn, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun x T => by
        ext a b
        simp only [embOn, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

def bdL (j : ℕ) (c c' : ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := bdiag j c c'
      map_add' := fun T T' => by
        ext a b
        simp only [bdiag, Matrix.add_apply]
        split_ifs <;> ring
      map_smul' := fun x T => by
        ext a b
        simp only [bdiag, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> ring }

theorem bdL_apply (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) : bdL j c c' t = bdiag j c c' t := rfl

theorem mem_blkB (j : ℕ) (r : Fin n) : r ∈ blkB (n := n) j ↔ r ∉ blkA (n := n) j := by
  simp [blkB]

end PositivityTheory.Rg.Sw.LVs.TC
