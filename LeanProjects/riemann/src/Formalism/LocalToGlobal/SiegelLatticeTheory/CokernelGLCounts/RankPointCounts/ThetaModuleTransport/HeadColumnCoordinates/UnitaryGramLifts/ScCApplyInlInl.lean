import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaGC

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA

variable {E : Type} [CommRing E] (cj : E →+* E) (qi : E) {r : ℕ}

def scC (r : ℕ) (α β : E) : Matrix (Ix r) (Ix r) E :=
  Matrix.fromBlocks 1 (β • liftE r) 0 (dlast r α)

theorem scC_apply_inl_inl (α β : E) (a b : Fin (r + 1)) : scC r α β (Sum.inl a) (Sum.inl b) = if a = b then 1 else 0 := by
  simp [scC, Matrix.one_apply]
theorem scC_apply_inl_inr (α β : E) (a b : Fin (r + 1)) :
    scC r α β (Sum.inl a) (Sum.inr b) = if a = Fin.last r ∧ b = Fin.last r then β else 0 := by
  simp [scC, liftE, smul_ite]
theorem scC_apply_inr_inl (α β : E) (a b : Fin (r + 1)) : scC r α β (Sum.inr a) (Sum.inl b) = 0 := by
  simp [scC]
theorem scC_apply_inr_inr (α β : E) (a b : Fin (r + 1)) :
    scC r α β (Sum.inr a) (Sum.inr b) = if a = b then (if a = Fin.last r then α else 1) else 0 := by
  simp [scC, dlast, Matrix.diagonal_apply]

theorem scC_left_inl (α β : E) (G : Matrix (Ix r) (Ix r) E) (a : Fin (r + 1)) (j : Ix r) :
    ((scC r α β).transpose * G) (Sum.inl a) j = G (Sum.inl a) j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, scC_apply_inl_inl, scC_apply_inr_inl,
    zero_mul, Finset.sum_const_zero, add_zero, ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem scC_left_inr (α β : E) (G : Matrix (Ix r) (Ix r) E) (a : Fin (r + 1)) (j : Ix r) :
    ((scC r α β).transpose * G) (Sum.inr a) j =
      (if a = Fin.last r then α else 1) * G (Sum.inr a) j +
        (if a = Fin.last r then β * G (Sum.inl (Fin.last r)) j else 0) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, scC_apply_inl_inr, scC_apply_inr_inr]
  by_cases ha : a = Fin.last r
  · subst ha
    simp [ite_mul, Finset.sum_ite_eq', add_comm]
  · simp [ha, ite_mul, Finset.sum_ite_eq]

theorem scC_right_inl (α β : E) (X : Matrix (Ix r) (Ix r) E) (i : Ix r) (b : Fin (r + 1)) :
    (X * (scC r α β).map cj) i (Sum.inl b) = X i (Sum.inl b) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inl, scC_apply_inr_inl, map_zero,
    mul_zero, Finset.sum_const_zero, add_zero, apply_ite cj, map_one, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem scC_right_inr (α β : E) (X : Matrix (Ix r) (Ix r) E) (i : Ix r) (b : Fin (r + 1)) :
    (X * (scC r α β).map cj) i (Sum.inr b) =
      X i (Sum.inr b) * cj (if b = Fin.last r then α else 1) +
        (if b = Fin.last r then X i (Sum.inl (Fin.last r)) * cj β else 0) := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inr, scC_apply_inr_inr]
  by_cases hb : b = Fin.last r
  · subst hb
    simp [apply_ite cj, mul_ite, Finset.sum_ite_eq', add_comm]
  · simp [hb, apply_ite cj, mul_ite, Finset.sum_ite_eq']

theorem gramG_scale (hcj : ∀ x, cj (cj x) = x) (α T T' : E) (hα : α * cj α = 1)
    (hqi : cj qi = qi) (hT : cj T = T) (hT' : cj T' = T') (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    gramG cj qi (Zh * dlast r α) T T' =
      (scC r α ((α - 1) * qi)).transpose * gramG cj qi Zh T T' * (scC r α ((α - 1) * qi)).map cj := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · rw [scC_right_inl, scC_left_inl]
    simp [gramG]
  · rw [scC_right_inr, scC_left_inl, scC_left_inl]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb, map_mul, map_sub, map_add, hqi, hT] <;> ring
  · rw [scC_right_inl, scC_left_inr]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb] <;> ring
  · rw [scC_right_inr, scC_left_inr, scC_left_inr]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;>
      simp [gramG, cor, dlast, Matrix.mul_diagonal, ha, hb, map_mul, map_sub, map_add, map_neg, hqi, hT, hT',
        hcj] <;> first | ring1 | linear_combination (qi ^ 2 * T') * hα | linear_combination (qi * qi * T') * hα | linear_combination (-(qi ^ 2 * T')) * hα

end ScaleA

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
