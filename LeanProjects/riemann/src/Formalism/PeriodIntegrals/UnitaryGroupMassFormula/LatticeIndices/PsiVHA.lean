import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsMulGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondEmbeddingEqStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem pair_sum (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w =
      ∑ i, ∑ j, (θ (v i)).2 * ((θ (inclR (FpX X p) (X.B.I.J i j))).1 * (θ (w j)).1) := by
  unfold crd1 crd2
  rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply]
  rw [← Equiv.sum_comp (idxEquiv X).symm.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.symm_symm, Equiv.symm_apply_apply, fst_apply_alt, snd_apply_alt, jm1, JR, Matrix.map_apply]
  rw [Finset.mul_sum]

theorem pair1 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).1 := by
  rw [pair_sum]
  simp only [hR, Formalism.UG.hform, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.fst_swap]
  ring

theorem pair2 (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q v ⬝ᵥ crd2 X p θ Q w = (θ (hR (FpX X p) X.B.I.cm.sig X.B.I.J v w)).2 := by
  rw [dotProduct_comm, pair_sum]
  simp only [hR, Formalism.UG.hform, map_sum, Prod.snd_sum, map_mul, Prod.snd_mul, JR, Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hθ (v i), Prod.snd_swap]
  have h := secondEmbedding_eq_star X p θ hθ (X.B.I.J i j)
  rw [herm_entry] at h
  have h' : (θ (inclR (FpX X p) (X.B.I.J i j))).2 = (θ (inclR (FpX X p) (X.B.I.J j i))).1 := h
  rw [h']
  ring

theorem psiV_hA' (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    PI.FinKW.psiV X.B.I p.1 (hA X.B.I x y) =
      hR (FpX X p) X.B.I.cm.sig X.B.I.J (PI.FinKW.vecV X.B.I p.1 x) (PI.FinKW.vecV X.B.I p.1 y) := by
  have hi : ∀ a : X.B.I.E, PI.FinKW.psiV X.B.I p.1 (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) a) =
      inclR (FpX X p) a := by
    intro a
    show (Algebra.TensorProduct.map (evalV X.B.I.F p.1) (AlgHom.id X.B.I.F X.B.I.E))
        ((Algebra.TensorProduct.comm X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (a ⊗ₜ[X.B.I.F] (1 : Formalism.MainNotions.S.Af X.B.I.F))) =
      (1 : FpX X p) ⊗ₜ[X.B.I.F] a
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hs := PIW.MassDataColumns.psiV_sigA X p
  simp only [hA, hR, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, JR, PI.FinKW.vecV]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hs, hi]

end Loc

end MassDataIdxSteps
