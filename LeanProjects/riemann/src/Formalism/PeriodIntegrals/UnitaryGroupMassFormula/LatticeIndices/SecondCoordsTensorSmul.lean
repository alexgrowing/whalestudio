import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstCoordsMulVec

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_add (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a + b) = crd1 X p θ Q a + crd1 X p θ Q b := by
  unfold crd1
  rw [map_add, show (pr1 θ a + pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm + pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add]

theorem secondCoords_add (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a + b) = crd2 X p θ Q a + crd2 X p θ Q b := by
  unfold crd2
  rw [map_add, show (pr2 θ a + pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm + pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_add, Matrix.mulVec_add]

theorem firstCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q (t • v) = (θ t).1 • crd1 X p θ Q v := by
  unfold crd1
  have : pr1 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).1 • (pr1 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).1 = (θ t).1 * (θ (v ((idxEquiv X).symm i))).1
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul]

theorem secondCoords_tensor_smul (t : TpX X p) (v : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (t • v) = (θ t).2 • crd2 X p θ Q v := by
  unfold crd2
  have : pr2 θ (t • v : Fin X.B.I.n → TpX X p) ∘ (idxEquiv X).symm = (θ t).2 • (pr2 θ v ∘ (idxEquiv X).symm) := by
    funext i
    show (θ (t * v ((idxEquiv X).symm i))).2 = (θ t).2 * (θ (v ((idxEquiv X).symm i))).2
    rw [map_mul]; rfl
  rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem smulO_eq (c : OvA X p) (v : Fin X.B.I.n → TpX X p) :
    c • v = ((c : FpX X p) • v) := rfl

end Loc

end MassDataIdxSteps
