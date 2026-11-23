import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.Development
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.XflagEqMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.ExistsUpUni

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n : ℕ} {K : Type*} [Field K] [StarRing K]

theorem det_upUni {N : Matrix (Fin n) (Fin n) K} (h : IsUpUni N) : N.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem det_loUni {L : Matrix (Fin n) (Fin n) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => (h i j).1 (OrderDual.toDual_lt_toDual.1 hij))]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem loUni_conjTranspose {N : Matrix (Fin n) (Fin n) K} (h : IsUpUni N) : IsLoUni N.conjTranspose := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · simp [Matrix.conjTranspose_apply, (h j i).1 hij]
  · subst hij
    simp [Matrix.conjTranspose_apply, (h i i).2 rfl]

def unitOf (A : Matrix (Fin n) (Fin n) K) (h : A.det = 1) : Matrix.GeneralLinearGroup (Fin n) K :=
  Matrix.nonsingInvUnit A (by rw [h]; exact isUnit_one)

theorem conj_key (l1 l2 v : Matrix.GeneralLinearGroup (Fin n) K) (X : Matrix (Fin n) (Fin n) K) :
    ((l2⁻¹ * v⁻¹ * l1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((l1⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) * X * (l1 : Matrix (Fin n) (Fin n) K)) *
        (((l2⁻¹ * v⁻¹ * l1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (l2⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) *
        ((v⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) * X * (v : Matrix (Fin n) (Fin n) K)) *
        (l2 : Matrix (Fin n) (Fin n) K) := by
  simp [mul_inv_rev, mul_assoc]

theorem conj_key' (l1 l2 v : Matrix.GeneralLinearGroup (Fin n) K) (X : Matrix (Fin n) (Fin n) K) :
    (((l2⁻¹ * v⁻¹ * l1)⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((l2⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) * X * (l2 : Matrix (Fin n) (Fin n) K)) *
        ((l2⁻¹ * v⁻¹ * l1 : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (l1⁻¹ : Matrix.GeneralLinearGroup (Fin n) K) *
        ((v : Matrix (Fin n) (Fin n) K) * X * (v⁻¹ : Matrix.GeneralLinearGroup (Fin n) K)) *
        (l1 : Matrix (Fin n) (Fin n) K) := by
  simp [mul_inv_rev, mul_assoc]

end Mat

end Formalism.L2.SG.Pf.RelativeIndexFlags
