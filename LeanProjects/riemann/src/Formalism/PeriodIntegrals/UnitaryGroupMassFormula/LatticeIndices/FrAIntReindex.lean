import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsSmulInteger
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulVec

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

theorem frA_int_reindex {F : Type} [Field F] (O : ValuationSubring F) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix n n F) (w : m → F) :
    (∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i ∈ O) ↔ ∀ i, (A *ᵥ (w ∘ e.symm)) i ∈ O := by
  have h : ∀ i, ((Matrix.reindex e.symm e.symm A) *ᵥ w) i = (A *ᵥ (w ∘ e.symm)) (e i) := by
    intro i
    simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Equiv.symm_symm, Function.comp_apply]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  simp only [h]
  constructor
  · intro H j
    simpa using H (e.symm j)
  · intro H i
    exact H (e i)

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem latCrd_of (hL : LatBasis X p θ (reindex₂ X p Q)) (x : Fin X.B.I.n → TpX X p) :
    x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have hPi : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        (((Q⁻¹ : GL (IdxD D) (FpX X p))) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hP : ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := rfl
  have hJ : J1 X p θ = jm1 X.B.I.J θ := rfl
  have hv : ∀ w : Fin X.B.I.n → FpX X p,
      (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (w ∘ (idxEquiv X).symm) =
        ((jm1 X.B.I.J θ)ᵀ *ᵥ w) ∘ (idxEquiv X).symm := by
    intro w
    rw [Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    funext j
    simp
  rw [hL x]
  unfold IntVec crd1 crd2
  rw [hPi, frA_int_reindex, ← Matrix.mulVec_mulVec, hP, Matrix.transpose_reindex, frA_int_reindex, hJ, ← hv]
  rfl

end Loc

end MassDataIdxSteps
