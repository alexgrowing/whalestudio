import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PsiVHA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.TwoPrimes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.SecondProjWeightVectorZero

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)
  (Q : GL (IdxD D) (FpX X p))

theorem zmod_comp (hL : LatBasis X p θ (reindex₂ X p Q)) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hc : ZMod' X.B.I X.B.g c) :
    (∃ y : OvA X p, (θ (PI.FinKW.psiV X.B.I p.1 c)).1 = ((gOf p : ℕ) : FpX X p) * (y : FpX X p)) ∧
    (∃ y : OvA X p, (θ (PI.FinKW.psiV X.B.I p.1 c)).2 = ((gOf p : ℕ) : FpX X p) * (y : FpX X p)) := by
  obtain ⟨t, ht, rfl⟩ := hc
  have hs : PI.FinKW.psiV X.B.I p.1 t ∈ OEp X p := ⟨t, ht, rfl⟩
  obtain ⟨h1, h2⟩ := oEp_int X p θ Q hL _ hs
  rw [map_mul, map_natCast, map_mul, map_natCast, imA_g_eq_mul X p]
  refine ⟨⟨((gOth X p : ℕ) : OvA X p) * ⟨_, h1⟩, ?_⟩, ⟨((gOth X p : ℕ) : OvA X p) * ⟨_, h2⟩, ?_⟩⟩
  · simp only [Prod.fst_mul, Prod.fst_natCast]
    push_cast
    ring
  · simp only [Prod.snd_mul, Prod.snd_natCast]
    push_cast
    ring

theorem cong_dir (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q))
    (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) (d : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ZMod' X.B.I X.B.g (hA X.B.I x y - d)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      (θ (PI.FinKW.psiV X.B.I p.1 d)).1 + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := (zmod_comp X p θ Q hL _ h).1
  refine ⟨z, ?_⟩
  rw [pair1 X p θ Q hθ, ← psiV_hA']
  rw [map_sub, map_sub, Prod.fst_sub] at hz
  linear_combination hz

theorem cong_sym (hθ : IsSplitEquiv X p θ) (hL : LatBasis X p θ (reindex₂ X p Q))
    (x y : Formalism.L2.SG.HidaSetting.VA X.B.I) (d : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ZMod' X.B.I X.B.g (hA X.B.I y x - d)) :
    ∃ z : OvA X p, crd2 X p θ Q (PI.FinKW.vecV X.B.I p.1 x) ⬝ᵥ crd1 X p θ Q (PI.FinKW.vecV X.B.I p.1 y) =
      (θ (PI.FinKW.psiV X.B.I p.1 d)).2 + ((gOf p : ℕ) : FpX X p) * (z : FpX X p) := by
  obtain ⟨z, hz⟩ := (zmod_comp X p θ Q hL _ h).2
  refine ⟨z, ?_⟩
  rw [dotProduct_comm, pair2 X p θ Q hθ, ← psiV_hA']
  rw [map_sub, map_sub, Prod.snd_sub] at hz
  linear_combination hz

end Loc

section Orient

variable {D : D7} (X : HidaSetting D) (p : TypX X)

def swapA : (FpX X p × FpX X p) ≃ₐ[FpX X p] (FpX X p × FpX X p) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.prodComm) (fun _ => rfl)

theorem exists_split_eps : ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p,
    IsSplitEquiv X p θ ∧ θ (epsP X p) = (1, 0) := by
  obtain ⟨θ₀, h₀⟩ := splitTheta_of X p (embP_holds X p)
  rcases PIW.MassDataColumns.theta_eps_cases X p θ₀ h₀ with h | h
  · exact ⟨θ₀, h₀, h⟩
  · refine ⟨θ₀.trans (swapA X p), ?_, ?_⟩
    · intro t
      rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, h₀ t]
      rfl
    · rw [AlgEquiv.trans_apply, h]
      rfl

theorem exists_GL_latBasis_of_isSplitEquiv (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (hθ : IsSplitEquiv X p θ) :
    ∃ Q : GL (IdxD D) (FpX X p), LatBasis X p θ (reindex₂ X p Q) := by
  obtain ⟨P, hP⟩ := latBasisAll_holds' X p θ hθ
  refine ⟨Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X)).toMonoidHom P, ?_⟩
  have e : reindex₂ X p (Units.map (Matrix.reindexAlgEquiv (FpX X p) (FpX X p) (idxEquiv X)).toMonoidHom P) = P := by
    ext i j
    simp [reindex₂]
  rw [e]
  exact hP

end Orient

end MassDataIdxSteps
