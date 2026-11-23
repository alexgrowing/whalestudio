import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondCoordsCongruentMod

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA PIW.MassDataColumns
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

theorem firstCoords_adapted_column (c : GL (IdxD D) (OvA X p))
    (hc : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = adqC X hb u p θ Q)
    (v : Fin X.B.I.n → TpX X p) (t : IdxD D) (hv : crd1 X p θ Q v = adqCol X hb u p θ Q t) :
    crd1 X p θ (Q * glK (OvA X p) c) v = Pi.single t 1 := by
  have e1 : crd1 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c)⁻¹ : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        crd1 X p θ Q v := by
    simp only [crd1, _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : adqCol X hb u p θ Q t =
      ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) *ᵥ
        Pi.single t 1 := by
    rw [hc]
    funext i
    simp [adqC, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e1, hv, e2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem secondCoords_adapted_column (c : GL (IdxD D) (OvA X p))
    (hc : ((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)) = adqC X hb u p θ Q)
    (v : Fin X.B.I.n → TpX X p) (t : IdxD D) :
    crd2 X p θ (Q * glK (OvA X p) c) v t = crd2 X p θ Q v ⬝ᵥ adqCol X hb u p θ Q t := by
  have e1 : crd2 X p θ (Q * glK (OvA X p) c) v =
      (((glK (OvA X p) c : GL (IdxD D) (FpX X p)) : Matrix (IdxD D) (IdxD D) (FpX X p)))ᵀ *ᵥ
        crd2 X p θ Q v := by
    simp only [crd2, Units.val_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, hc]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, adqC]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem frame_castSucc_vector_eq (a : Fin D.R.rS) :
    F0 (frameOf X u) (Fin.castSucc a) = crdOf X.B.I X.ιE X.bas (X.eX a) := by
  first
  | rfl
  | simp [F0, frameOf]

theorem frame_last_vector_eq : F0 (frameOf X u) (Fin.last D.R.rS) = crdOf X.B.I X.ιE X.bas (X.zu u) := by
  first
  | rfl
  | simp [F0, frameOf]

end Loc

theorem stAdaptQ_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    StAdaptQ X u p := by
  obtain ⟨θ, hθ, hε⟩ := exists_split_eps X p
  obtain ⟨Q, hL⟩ := exists_GL_latBasis_of_isSplitEquiv X p θ hθ
  obtain ⟨c, hc⟩ := adq_gl X hb u p θ Q hθ hε hL
  have hτ := (adq_tau_inv X hb u p θ Q hθ hL).2
  refine ⟨θ, hθ, Q * glK (OvA X p) c, Fin.lastCases (adqTau X u p θ Q) (fun _ => 1), ?_, ?_, ?_,
    latBasis_mulGL X p θ Q hL c⟩
  · intro b
    induction b using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last]; exact hτ
    | cast a => dsimp only; rw [Fin.lastCases_castSucc]; exact one_ne_zero
  · intro b
    show crd1 X p θ (Q * glK (OvA X p) c) _ = _
    induction b using Fin.lastCases with
    | last =>
      rw [frame_last_vector_eq]
      have hp : pe (k := D.R.k) (Fin.last D.R.rS) = zI := by simp [pe]
      rw [hp]
      exact firstCoords_adapted_column X hb u p θ Q c hc _ zI rfl
    | cast a =>
      rw [frame_castSucc_vector_eq]
      have hp : pe (k := D.R.k) (Fin.castSucc a) = Sum.inl a := by simp [pe]
      rw [hp]
      exact firstCoords_adapted_column X hb u p θ Q c hc _ (Sum.inl a) rfl
  · intro b
    show crd2 X p θ (Q * glK (OvA X p) c) _ = _
    funext t
    rw [secondCoords_adapted_column X hb u p θ Q c hc]
    induction b using Fin.lastCases with
    | last =>
      rw [frame_last_vector_eq]
      dsimp only
      rw [Fin.lastCases_last]
      have hp : pf (k := D.R.k) (Fin.last D.R.rS) = zI := by simp [pf]
      rw [hp]
      rcases t with a | ((i | v) | c')
      · rw [show adqCol X hb u p θ Q (Sum.inl a) = crd1 X p θ Q (adqE X p a) from rfl]
        rw [adq_ze X u p θ Q hθ]
        simp [zI]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inl i))) = adqProj X u p θ Q
          (crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) from rfl]
        rw [secondCoords_projection_orth X u p θ Q hθ hτ]
        simp [zI]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inr v))) = crd1 X p θ Q (adqZ X u p) from rfl]
        have hv : v = () := rfl
        subst hv
        simp [zI, adqTau]
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inr c')) = crd1 X p θ Q (adqF X p (Fin.rev c')) from rfl]
        rw [adq_zf X u p θ Q hθ]
        simp [zI]
    | cast b =>
      rw [frame_castSucc_vector_eq]
      dsimp only
      rw [Fin.lastCases_castSucc]
      have hp : pf (k := D.R.k) (Fin.castSucc b) = Sum.inr (Sum.inr (Fin.rev b)) := by simp [pf]
      rw [hp]
      rcases t with a | ((i | v) | c')
      · rw [show adqCol X hb u p θ Q (Sum.inl a) = crd1 X p θ Q (adqE X p a) from rfl]
        rw [adq_ee X p θ Q u hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inl i))) = adqProj X u p θ Q
          (crd1 X p θ Q (adqM X hb u p *ᵥ PI.FinKW.vecV X.B.I p.1 (X.bw i))) from rfl]
        rw [adq_proj_e X u p θ Q hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inl (Sum.inr v))) = crd1 X p θ Q (adqZ X u p) from rfl]
        rw [adq_ez X u p θ Q hθ]
        simp
      · rw [show adqCol X hb u p θ Q (Sum.inr (Sum.inr c')) = crd1 X p θ Q (adqF X p (Fin.rev c')) from rfl]
        rw [adq_ef X p θ Q u hθ]
        by_cases h : c' = Fin.rev b
        · subst h
          simp
        · have h' : b ≠ Fin.rev c' := fun e => h (by rw [e, Fin.rev_rev])
          simp [h, h']

end MassDataIdxSteps
