import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.FGInvariant

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA4

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) (qi : E) {r : ℕ}

structure ScHyp (O : Subring E) (cj : E →+* E) (qi T T' α : E) : Prop where
  cjcj : ∀ x, cj (cj x) = x
  cjO : ∀ x ∈ O, cj x ∈ O
  qic : cj qi = qi
  Tc : cj T = T
  T'c : cj T' = T'
  αO : α ∈ O
  αn : α * cj α = 1
  βO : (α - 1) * qi ∈ O

variable {O cj qi} {T T' α : E}

theorem ScHyp.cα_mem (h : ScHyp O cj qi T T' α) : cj α ∈ O := h.cjO α h.αO
theorem ScHyp.β'_mem (h : ScHyp O cj qi T T' α) : -((α - 1) * qi * cj α) ∈ O :=
  O.neg_mem (O.mul_mem h.βO h.cα_mem)

theorem ScHyp.C_mul (h : ScHyp O cj qi T T' α) :
    scC r α ((α - 1) * qi) * scC r (cj α) (-((α - 1) * qi * cj α)) = 1 :=
  scC_mul_inv α _ (cj α) _ h.αn rfl

theorem ScHyp.C'_mul (h : ScHyp O cj qi T T' α) :
    scC r (cj α) (-((α - 1) * qi * cj α)) * scC r α ((α - 1) * qi) = 1 := by
  have hc : cj α * α = 1 := by rw [mul_comm]; exact h.αn
  exact scC_mul_inv (cj α) _ α _ hc (by linear_combination (-((α - 1) * qi)) * hc)

def scA (h : ScHyp O cj qi T T' α) : Matrix (Ix r) (Ix r) O :=
  toOm O ((scC r α ((α - 1) * qi)).map cj) fun i j => h.cjO _ (scC_mem O α _ h.αO h.βO i j)

def scA' (h : ScHyp O cj qi T T' α) : Matrix (Ix r) (Ix r) O :=
  toOm O ((scC r (cj α) (-((α - 1) * qi * cj α))).map cj) fun i j =>
    h.cjO _ (scC_mem O _ _ h.cα_mem h.β'_mem i j)

theorem scA_mul (h : ScHyp O cj qi T T' α) : scA (r := r) h * scA' h = 1 := by
  refine Matrix.map_injective (f := O.subtype) Subtype.val_injective ?_
  show (scA h * scA' h).map O.subtype = (1 : Matrix (Ix r) (Ix r) O).map O.subtype
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : (scA (r := r) h).map O.subtype = (scC r α ((α - 1) * qi)).map cj := by
    ext i j
    rfl
  have e2 : (scA' (r := r) h).map O.subtype = (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    ext i j
    rfl
  rw [e1, e2, ← Matrix.map_mul, h.C_mul, Matrix.map_one _ (map_zero cj) (map_one cj)]

theorem scA'_mul (h : ScHyp O cj qi T T' α) : scA' (r := r) h * scA h = 1 := by
  refine Matrix.map_injective (f := O.subtype) Subtype.val_injective ?_
  show (scA' h * scA h).map O.subtype = (1 : Matrix (Ix r) (Ix r) O).map O.subtype
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have e1 : (scA (r := r) h).map O.subtype = (scC r α ((α - 1) * qi)).map cj := by
    ext i j
    rfl
  have e2 : (scA' (r := r) h).map O.subtype = (scC r (cj α) (-((α - 1) * qi * cj α))).map cj := by
    ext i j
    rfl
  rw [e1, e2, ← Matrix.map_mul, h.C'_mul, Matrix.map_one _ (map_zero cj) (map_one cj)]

def scPhi (h : ScHyp O cj qi T T' α) : (Ix r → O) ≃ₗ[O] (Ix r → O) :=
  phiEq O (scA h) (scA' h) (scA_mul h) (scA'_mul h)

theorem scPhi_coe (h : ScHyp O cj qi T T' α) (Y : Ix r → O) (j : Ix r) :
    ((scPhi (r := r) h Y j : O) : E) = Matrix.vecMul (fun i => (Y i : E)) ((scC r α ((α - 1) * qi)).map cj) j := by
  show ((Matrix.vecMul Y (scA h) j : O) : E) = _
  simp [Matrix.vecMul, dotProduct, scA, toOm]

theorem vecMul_scC_inl (α β : E) (Y : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul Y ((scC r α β).map cj) (Sum.inl b) = Y (Sum.inl b) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inl,
    scC_apply_inr_inl, map_zero, mul_zero, Finset.sum_const_zero, add_zero]
  simp [apply_ite cj, mul_ite, Finset.sum_ite_eq']

theorem vecMul_scC_inr (α β : E) (Y : Ix r → E) (b : Fin (r + 1)) :
    Matrix.vecMul Y ((scC r α β).map cj) (Sum.inr b) =
      Y (Sum.inr b) * cj (if b = Fin.last r then α else 1) +
        (if b = Fin.last r then Y (Sum.inl (Fin.last r)) * cj β else 0) := by
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, scC_apply_inl_inr,
    scC_apply_inr_inr]
  by_cases hb : b = Fin.last r
  · subst hb
    simp [apply_ite cj, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  · simp [hb, apply_ite cj, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

end ScaleA4

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
