import Formalism.UnipotentAdelicQuotients.EllReg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open MeasureTheory
open scoped ContDiff

def EllRegBridge : Prop := ZetaZeros.D.EllReg.Internal → EllRegW

section bridge

variable {d : ℕ}

noncomputable abbrev brT (d : ℕ) : ZetaZeros.D.EllReg.E d ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ

lemma brT_ev (j : Fin d) : brT d (ZetaZeros.D.EllReg.ev j) = Pi.single j 1 := by
  unfold ZetaZeros.D.EllReg.ev
  rfl

lemma dw_comp_brT (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    ZetaZeros.D.EllReg.dw w (f ∘ brT d) = pdc w f ∘ brT d := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (ZetaZeros.D.EllReg.dw w (f ∘ brT d)) x (ZetaZeros.D.EllReg.ev j) =
      fderiv ℝ (pdc w f) (brT d x) (Pi.single j 1)
    rw [ih, (brT d).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, brT_ev]

noncomputable def brSys {ι : Type} (P : ι → SOp d) : ZetaZeros.D.EllReg.Sys d ι where
  ord i := (P i).ord
  a i n w := if h : n < (P i).ord + 1 then (P i).a ⟨n, h⟩ w ∘ brT d else 0

lemma brSys_tr {ι : Type} (P : ι → SOp d) (i : ι) (φ : (Fin d → ℝ) → ℂ) (x : ZetaZeros.D.EllReg.E d) :
    (brSys P).tr i (φ ∘ brT d) x = (P i).tr φ (brT d x) := by
  unfold ZetaZeros.D.EllReg.Sys.tr ZetaZeros.D.EllReg.trOp SOp.tr
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have e : (fun y => (brSys P).a i k w y * (φ ∘ brT d) y) =
      (fun y' => (P i).a k w y' * φ y') ∘ brT d := by
    funext y
    simp only [brSys, Function.comp_apply]
    rw [dif_pos (show (k : ℕ) < (P i).ord + 1 from k.isLt)]
    rfl
  rw [e, dw_comp_brT]
  rfl

lemma brSys_symb {ι : Type} (P : ι → SOp d) (i : ι) (x ξ : ZetaZeros.D.EllReg.E d) :
    (brSys P).symb i x ξ = (P i).symb (brT d x) (brT d ξ) := by
  unfold ZetaZeros.D.EllReg.Sys.symb SOp.symb
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [brSys, dif_pos (Nat.lt_succ_self _)]
  rw [mul_comm]
  rfl

end bridge

theorem elliptic_regularity_transfer_holds : EllRegBridge := by
  intro hI d ι _ P U u hU ha hu hweak hsymb
  have hHyp : ZetaZeros.D.EllReg.Hyp (brSys P) (brT d ⁻¹' U) (u ∘ brT d) := by
    refine ⟨hU.preimage (brT d).continuous, ?_, ?_, hu.comp (brT d).continuous.continuousOn (fun x hx => hx), ?_⟩
    · intro i n w
      simp only [brSys]
      split_ifs with h
      · exact (ha i ⟨n, h⟩ w).comp_continuousLinearMap ((brT d : ZetaZeros.D.EllReg.E d →L[ℝ] (Fin d → ℝ)))
      · exact contDiffOn_const
    · intro x hx ξ hξ
      have hξ' : brT d ξ ≠ 0 := fun h => hξ ((brT d).injective (h.trans (map_zero (brT d)).symm))
      obtain ⟨i, hi⟩ := hsymb (brT d x) hx (brT d ξ) hξ'
      exact ⟨i, by rw [brSys_symb]; exact hi⟩
    · intro i φ hφ hφc hφU
      have hψ : ContDiff ℝ ∞ (φ ∘ (brT d).symm) := hφ.comp (brT d).symm.contDiff
      have hψc : HasCompactSupport (φ ∘ (brT d).symm) := hφc.comp_homeomorph (brT d).symm.toHomeomorph
      have hψU : tsupport (φ ∘ (brT d).symm) ⊆ U := by
        intro y hy
        have hy' : y ∈ tsupport (φ ∘ (brT d).symm.toHomeomorph) := hy
        rw [tsupport_comp_eq_preimage φ (brT d).symm.toHomeomorph] at hy'
        have h1 := hφU hy'
        have h2 : brT d ((brT d).symm y) ∈ U := h1
        rwa [ContinuousLinearEquiv.apply_symm_apply] at h2
      have hφeq : φ = (φ ∘ (brT d).symm) ∘ brT d := by
        funext x
        simp
      have h1 := hweak i (φ ∘ (brT d).symm) hψ hψc hψU
      rw [hφeq]
      simp_rw [brSys_tr]
      rw [← h1]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
        (fun y => u y * (P i).tr (φ ∘ (brT d).symm) y)
  have key := hI d ι (brSys P) (brT d ⁻¹' U) (u ∘ brT d) hHyp
  have h2 := key.comp_continuousLinearMap (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d))
  have e1 : (u ∘ brT d) ∘ (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) = u := by
    funext x
    show u (brT d ((brT d).symm x)) = u x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have e2 : (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) ⁻¹' (brT d ⁻¹' U) = U := by
    ext x
    show brT d ((brT d).symm x) ∈ U ↔ x ∈ U
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [e1, e2] at h2
  exact h2

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
