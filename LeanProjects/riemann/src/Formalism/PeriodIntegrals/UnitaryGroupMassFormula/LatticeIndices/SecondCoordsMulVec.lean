import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

theorem frA_reindex_mul {R m n : Type} [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A B : Matrix m m R) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  (Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm).symm

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem secondCoords_mulVec (hθ : IsSplitEquiv X p θ) (x : HAp X p) (Z : Matrix (IdxD D) (IdxD D) (FpX X p))
    (hZ : Z * (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      Matrix.reindex (idxEquiv X) (idxEquiv X) (cmp1 X.B.I.cm.sig X.B.I.J θ x) *
        (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) = 1) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) *ᵥ v) = Zᵀ *ᵥ crd2 X p θ Q v := by
  set e := idxEquiv X
  set M1 := Matrix.reindex e e (cmp1 X.B.I.cm.sig X.B.I.J θ x) with hM1
  set M2 := Matrix.reindex e e (cmp2 X.B.I.cm.sig X.B.I.J θ x) with hM2
  set J' := Matrix.reindex e e (jm1 X.B.I.J θ) with hJ'
  set Qm := (Q : Matrix (IdxD D) (IdxD D) (FpX X p))
  set Qi := ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hU : M1ᵀ * (J'ᵀ * M2) = J'ᵀ := by
    have h0 := cmp_unit X.B.I.cm.sig X.B.I.J θ hθ x
    have h1 := congrArg (fun A => Matrix.reindex e e Aᵀ) h0
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h1
    rw [frA_reindex_mul, frA_reindex_mul] at h1
    simpa [hM1, hM2, hJ', Matrix.transpose_reindex] using h1
  have hYZ : (Qi * M1 * Qm) * Z = 1 := mul_eq_one_comm.mp hZ
  have hQY : Qm * (Qi * M1 * Qm) = M1 * Qm := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have key : Qmᵀ * (J'ᵀ * M2) = Zᵀ * (Qmᵀ * J'ᵀ) := by
    calc Qmᵀ * (J'ᵀ * M2) = ((Qi * M1 * Qm) * Z)ᵀ * (Qmᵀ * (J'ᵀ * M2)) := by
          rw [hYZ, Matrix.transpose_one, Matrix.one_mul]
      _ = Zᵀ * ((Qm * (Qi * M1 * Qm))ᵀ * (J'ᵀ * M2)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul Qm]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * (M1ᵀ * (J'ᵀ * M2))) := by
          rw [hQY, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Zᵀ * (Qmᵀ * J'ᵀ) := by rw [hU]
  unfold crd2
  rw [secondProj_split_mulVec]
  have hr : ((((HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J x : GL (Fin X.B.I.n) (TpX X p)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)).map fun t => (θ t).2) *ᵥ pr2 θ v) ∘ e.symm =
      M2 *ᵥ (pr2 θ v ∘ e.symm) := by
    rw [hM2, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    have : (pr2 θ v ∘ e.symm) ∘ e.symm.symm = pr2 θ v := by funext i; simp
    rw [this]; rfl
  have key' : Qmᵀ * J'ᵀ * M2 = Zᵀ * Qmᵀ * J'ᵀ := by rw [Matrix.mul_assoc, key, Matrix.mul_assoc]
  rw [hr, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun A => A *ᵥ (pr2 θ v ∘ e.symm)) key'

end Loc

end MassDataIdxSteps
