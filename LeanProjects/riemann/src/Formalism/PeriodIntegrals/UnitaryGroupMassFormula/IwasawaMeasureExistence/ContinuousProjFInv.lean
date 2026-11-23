import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt

noncomputable section

namespace PI.IwaMeasEx.AfT

open NumberField Matrix Topology Filter
open scoped TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.WittLeviSubgroups

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

end Alg

section Top

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T1Space R] {n : ℕ}

variable {X : Type} [TopologicalSpace X] (m : X → GL (Fin n) R)
  (hm : Continuous fun x => (m x : Matrix (Fin n) (Fin n) R))
  (hmi : Continuous fun x => (((m x)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
include hm hmi

variable {ι : Type} [Fintype ι] (b : ι → (Fin n → R)) (lev : ι → ℕ) (e : ι ≃ Fin n)
  (P Q : Matrix (Fin n) (Fin n) R) (hQP : Q * P = 1) (hPQ : P * Q = 1) (hb : ∀ r i, b r i = P i (e r))
include hQP hPQ hb

end Top

variable (I : AutInst)

variable {I} {J : ℕ} (Fr : WittFrame I J)

def frF : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  (Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

def frFi : Matrix (Fin I.n) (Fin I.n) (AEf I) :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem frFi_mul : frFi Fr * frF Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frF_mul : frF Fr * frFi Fr = 1 := by
  rw [frFi, frF, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

def frVi (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  ((Fr.B⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v

theorem frVi_mul (v : InfinitePlace I.F) : frVi Fr v * Fr.frV v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), Matrix.mul_nonsing_inv _ hP,
    Matrix.one_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem frV_mul (v : InfinitePlace I.F) : Fr.frV v * frVi Fr v = 1 := by
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [frVi, WittFrame.frV, Matrix.mul_assoc, ← Matrix.mul_assoc ((Fr.B : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)),
    ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ hP]

variable (c : Composition J)

def parA : Subgroup I.GA :=
  (parGL Fr.colF (levW c)).comap (projF I) ⊓ ⨅ v, (parGL (Fr.colV v) (levW c)).comap (projV I v)

end PI.IwaMeasEx.AfT
