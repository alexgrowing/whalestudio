import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfTransitive
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CongSpanSingleIff

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

abbrev IdxD (D : D7) : Type := Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

abbrev OvA : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

abbrev gA : OvA X p := ((gOf p : ℕ) : OvA X p)

def crd1 (v : Fin X.B.I.n → TpX X p) : IdxD D → FpX X p :=
  ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ (pr1 θ v ∘ (idxEquiv X).symm)

def crd2 (v : Fin X.B.I.n → TpX X p) : IdxD D → FpX X p :=
  (Q : Matrix (IdxD D) (IdxD D) (FpX X p))ᵀ *ᵥ
    ((Matrix.reindex (idxEquiv X) (idxEquiv X) (jm1 X.B.I.J θ))ᵀ *ᵥ (pr2 θ v ∘ (idxEquiv X).symm))

def SplitA : Prop :=
  ∀ (S : Set (Fin X.B.I.n → TpX X p)) (y : Fin X.B.I.n → TpX X p),
    InModP X p (gOf p) S y ↔
      MassDataIdxFrA.CongSpan (OvA X p) (gA X p) (crd1 X p θ Q '' S) (crd1 X p θ Q y) ∧
      MassDataIdxFrA.CongSpan (OvA X p) (gA X p) (crd2 X p θ Q '' S) (crd2 X p θ Q y)

def CongG (v w : IdxD D → FpX X p) : Prop :=
  ∃ z, MassDataIdxFrA.IntVec (OvA X p) z ∧ v = w + ((gA X p : OvA X p) : FpX X p) • z

def AdaptA : Prop :=
  (∀ a : Fin D.R.rS, CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 a))) (Pi.single (Sum.inl a) 1)) ∧
  CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) (Pi.single zI 1) ∧
  (∀ i : Fin D.R.k, CongG X p (crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.bw i))) (Pi.single (wI i) 1)) ∧
  (∀ a : Fin D.R.rS, CongG X p (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 (X.e0 a)))
    (Pi.single (Sum.inr (Sum.inr (Fin.rev a))) 1)) ∧
  CongG X p (crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 X.z0)) (-Pi.single zI 1) ∧
  ∀ i : Fin D.R.k, pr2 θ (PI.FinKW.vecV X.B.I p.1 (X.bw i)) = 0

theorem firstCoords_mulVec (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (TpX X p)) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (M *ᵥ v) =
      (((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *
        Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *
          (Q : Matrix (IdxD D) (IdxD D) (FpX X p))) *ᵥ crd1 X p θ Q v := by

  have key : ∀ j, (pr1 θ (M *ᵥ v)) j = ((M.map fun t => (θ t).1) *ᵥ pr1 θ v) j := by
    intro j
    change (θ ((M *ᵥ v) j)).1 = ∑ k, (θ (M j k)).1 * (θ (v k)).1
    simp [Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum]
  have key2 : pr1 θ (M *ᵥ v) ∘ (idxEquiv X).symm =
      Matrix.reindex (idxEquiv X) (idxEquiv X) (M.map fun t => (θ t).1) *ᵥ
        (pr1 θ v ∘ (idxEquiv X).symm) := by
    funext i
    rw [Function.comp_apply, key]
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact (Fintype.sum_equiv (idxEquiv X).symm _ _ (fun _ => rfl)).symm
  have hQ : (Q : Matrix (IdxD D) (IdxD D) (FpX X p)) *
      ((Q⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = 1 :=
    Units.mul_inv Q
  simp only [crd1]
  rw [key2]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one]

end Loc

end MassDataIdxSteps
