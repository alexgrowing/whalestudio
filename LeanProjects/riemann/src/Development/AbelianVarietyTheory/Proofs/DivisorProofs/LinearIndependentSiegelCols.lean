import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstTermIsoCst

def siegelCols (D : D7) (n : ℕ) : Matrix (Fin (n + n)) (Fin n) D.host.E :=
  Matrix.of fun i j => if i = finSumFinEquiv (Sum.inl j) then 1 else 0

variable (D : D7) {n : ℕ}

theorem siegelCols_castAdd (i j : Fin n) : siegelCols D n (Fin.castAdd n i) j = if i = j then 1 else 0 := by
  simp [siegelCols, Fin.castAdd_inj]

theorem siegelCols_natAdd (i j : Fin n) : siegelCols D n (Fin.natAdd n i) j = 0 := by
  simp [siegelCols, Fin.ext_iff]
  omega

theorem jst_cc (i k : Fin n) : StdUnn.Jst D n (Fin.castAdd n i) (Fin.castAdd n k) = 0 := by
  simp only [StdUnn.Jst, StdUnn.blk4, Matrix.submatrix_apply]
  rw [show finSumFinEquiv.symm (Fin.castAdd n i) = Sum.inl i from finSumFinEquiv_symm_apply_castAdd i,
    show finSumFinEquiv.symm (Fin.castAdd n k) = Sum.inl k from finSumFinEquiv_symm_apply_castAdd k]
  simp

theorem linearIndependent_siegelCols : LinearIndependent D.host.E (siegelCols D n).transpose := by
  change LinearIndependent D.host.E (fun j i => siegelCols D n i j)
  refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
  have := congrFun hc (Fin.castAdd n j)
  simpa [Finset.sum_apply, Matrix.transpose_apply, siegelCols_castAdd, eq_comm] using this

theorem siegelCols_isotropic :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (siegelCols D n) * StdUnn.Jst D n * siegelCols D n = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_add, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, siegelCols_castAdd,
    siegelCols_natAdd, jst_cc, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp

end GlobalTheory.FirstTermIsoCst

end
