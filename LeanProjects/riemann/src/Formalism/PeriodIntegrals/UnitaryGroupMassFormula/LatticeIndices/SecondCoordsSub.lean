import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Imports

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

def fposA (a : Fin D.R.rS) : IdxD D := Sum.inr (Sum.inr (Fin.rev a))

def EntA (π : Op X p →+* ZMod (gOf p)) (Y : GL (IdxD D) (Op X p)) : Prop :=
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (Sum.inl '' {b : Fin D.R.rS | b.1 < a.1} : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (Sum.inl a)) = if i = Sum.inl a then 1 else 0) ∧
  (∀ i, i ∉ (Sum.inl '' Set.univ : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i zI) = if i = zI then 1 else 0) ∧
  (∀ j : Fin D.R.k, ∀ i, i ∉ (posW (r := D.R.rS) j : Set (IdxD D)) →
    π ((Y : Matrix (IdxD D) (IdxD D) (Op X p)) i (wI j)) = if i = wI j then 1 else 0) ∧
  (∀ a : Fin D.R.rS, ∀ i, i ∉ (fposA (D := D) '' {b : Fin D.R.rS | b.1 < a.1}) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) (fposA a) i) =
      if i = fposA a then 1 else 0) ∧
  (∀ i, i ∉ (fposA (D := D) '' Set.univ) →
    π (((Y⁻¹ : GL (IdxD D) (Op X p)) : Matrix (IdxD D) (IdxD D) (Op X p)) zI i) = if i = zI then 1 else 0)

theorem firstCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd1 X p θ Q (a - b) = crd1 X p θ Q a - crd1 X p θ Q b := by
  unfold crd1
  rw [map_sub, show (pr1 θ a - pr1 θ b) ∘ (idxEquiv X).symm =
    pr1 θ a ∘ (idxEquiv X).symm - pr1 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub]

theorem secondCoords_sub (a b : Fin X.B.I.n → TpX X p) : crd2 X p θ Q (a - b) = crd2 X p θ Q a - crd2 X p θ Q b := by
  unfold crd2
  rw [map_sub, show (pr2 θ a - pr2 θ b) ∘ (idxEquiv X).symm =
    pr2 θ a ∘ (idxEquiv X).symm - pr2 θ b ∘ (idxEquiv X).symm from rfl, Matrix.mulVec_sub, Matrix.mulVec_sub]

end Loc

end MassDataIdxSteps
