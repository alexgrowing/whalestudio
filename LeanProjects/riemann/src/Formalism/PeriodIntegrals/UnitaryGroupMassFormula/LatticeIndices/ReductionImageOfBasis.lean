import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ReductionImageOfAdaptedMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.ThetaEpsCases

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem oEpSplit_holds (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    OEpSplit X p θ := by
  have hone : θ.symm (1, 1) = 1 := by rw [Prod.mk_one_one, map_one]
  have hsub : ∀ a b : FpX X p × FpX X p, θ.symm (a - b) = θ.symm a - θ.symm b := fun a b => map_sub _ _ _
  have hm : 1 - epsP X p ∈ OEp X p := imA_OEp_sub X p (imA_OEp_one X p) (imA_eps_mem X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ hθ with h | h
  · have e1 : θ.symm (1, 0) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (0, 1) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e1 ▸ imA_eps_mem X p, e2 ▸ hm⟩
  · have e1 : θ.symm (0, 1) = epsP X p := by rw [← h, AlgEquiv.symm_apply_apply]
    have e2 : θ.symm (1, 0) = 1 - epsP X p := by
      rw [← hone, ← e1, ← hsub]; congr 1; ext <;> simp
    exact ⟨e2 ▸ hm, e1 ▸ imA_eps_mem X p⟩

def StAdaptBasisA : Prop :=
  ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ ∧
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) ∧ AdaptA X p θ Q

theorem reduction_image_of_basis (hb : AdBridgeIso X.B.I) (h : StAdaptBasisA X p) : LevelReductionImage X hb p := by
  obtain ⟨θ, hθ, Q, hL, hA⟩ := h
  exact reduction_image_of_adapted_mod X p hb latCoreX_holds ⟨θ, hθ, oEpSplit_holds X p θ hθ, Q, hL, hA⟩

end Loc

end MassDataIdxSteps
