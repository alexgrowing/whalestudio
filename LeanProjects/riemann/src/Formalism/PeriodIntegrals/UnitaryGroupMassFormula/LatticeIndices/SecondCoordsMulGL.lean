import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGlOfLeftInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrAIntReindex

noncomputable section

namespace MassDataIdxAdA

open Matrix

variable {K : Type*} [Field K] (O : ValuationSubring K) {ι : Type*} [Fintype ι] [DecidableEq ι]

def glK (c : GL ι O) : GL ι K := Units.map (RingHom.mapMatrix O.subtype).toMonoidHom c

theorem glK_val (c : GL ι O) : ((glK O c : GL ι K) : Matrix ι ι K) = (c : Matrix ι ι O).map O.subtype := rfl

theorem glK_inv (c : GL ι O) : (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) = ((c⁻¹ : GL ι O) : Matrix ι ι O).map O.subtype := by
  rw [glK, ← map_inv]; rfl

theorem intVec_mulVec {M : Matrix ι ι K} (hM : ∀ i j, M i j ∈ O) {w : ι → K} (hw : ∀ i, w i ∈ O) (i : ι) :
    (M *ᵥ w) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hw j)

theorem glK_int (c : GL ι O) (i j : ι) : ((glK O c : GL ι K) : Matrix ι ι K) i j ∈ O := by
  rw [glK_val]; exact ((c : Matrix ι ι O) i j).2

theorem glK_inv_int (c : GL ι O) (i j : ι) : (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) i j ∈ O := by
  rw [glK_inv]; exact (((c⁻¹ : GL ι O) : Matrix ι ι O) i j).2

theorem intVec_inv_iff (c : GL ι O) (w : ι → K) :
    (∀ i, ((((glK O c)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) i ∈ O) ↔ ∀ i, w i ∈ O := by
  constructor
  · intro h i
    have := intVec_mulVec O (glK_int O c) h i
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro h i
    exact intVec_mulVec O (glK_inv_int O c) h i

theorem intVec_tr_iff (c : GL ι O) (w : ι → K) :
    (∀ i, (((glK O c : GL ι K) : Matrix ι ι K)ᵀ *ᵥ w) i ∈ O) ↔ ∀ i, w i ∈ O := by
  constructor
  · intro h i
    have := intVec_mulVec O (M := (((glK O c)⁻¹ : GL ι K) : Matrix ι ι K)ᵀ) (fun a b => glK_inv_int O c b a) h i
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.one_mulVec] at this
  · intro h i
    exact intVec_mulVec O (M := (((glK O c : GL ι K) : Matrix ι ι K))ᵀ) (fun a b => glK_int O c b a) h i

end MassDataIdxAdA

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_mul_GL (c : GL (IdxD D) (OvA X p)) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c)⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ crd1 X p θ Q v := by
  unfold crd1
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem secondCoords_mul_GL (c : GL (IdxD D) (OvA X p)) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ (Q * glK (OvA X p) c) v =
      ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ crd2 X p θ Q v := by
  unfold crd2
  rw [Units.val_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

theorem latRhs_iff (x : Fin X.B.I.n → TpX X p) :
    ((∀ i, (Matrix.mulVec (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p))
        fun j => th1 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F) ∧
    (∀ i, (Matrix.mulVec (Matrix.transpose ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
        Matrix.transpose (J1 X p θ))
        fun j => th2 X p θ (x j)) i ∈ p.1.adicCompletionIntegers X.B.I.F)) ↔
      IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x) := by
  have h1 : (((reindex₂ X p Q)⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) := by
    unfold reindex₂; rw [← map_inv]; rfl
  have h2 : Matrix.transpose ((reindex₂ X p Q : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *
      Matrix.transpose (J1 X p θ) =
      Matrix.reindex (idxEquiv X).symm (idxEquiv X).symm
        ((Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *
          (Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ) := by
    rw [frA_reindex_mul, ← Matrix.transpose_reindex, ← Matrix.transpose_reindex]
    congr 2
    ext i j
    simp [Matrix.reindex_apply, J1, jm1, JR, th1]
  rw [h1, h2, frA_int_reindex, frA_int_reindex]
  unfold crd1 crd2 IntVec
  rw [Matrix.mulVec_mulVec]
  rfl

theorem latBasis_of_crd (h : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    IntVec (OvA X p) (crd1 X p θ Q x) ∧ IntVec (OvA X p) (crd2 X p θ Q x)) : LatBasis X p θ (reindex₂ X p Q) := by
  intro x
  rw [h x, latRhs_iff]

theorem latBasis_mulGL (hL : LatBasis X p θ (reindex₂ X p Q)) (c : GL (IdxD D) (OvA X p)) :
    LatBasis X p θ (reindex₂ X p (Q * glK (OvA X p) c)) := by
  apply latBasis_of_crd
  intro x
  rw [latCrd_of X p θ Q hL x]
  unfold IntVec
  rw [firstCoords_mul_GL, secondCoords_mul_GL, intVec_inv_iff, intVec_tr_iff]

end Loc

end MassDataIdxSteps
