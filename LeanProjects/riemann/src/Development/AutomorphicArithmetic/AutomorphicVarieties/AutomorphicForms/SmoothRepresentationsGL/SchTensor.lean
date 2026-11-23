import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTensor :
    UpperTheory.V.Af.Smo.SchOfClosed → UpperTheory.V.Af.Smo.SchTensor := by
  intro hS V M _ _ _ _ _ _ h hh hhc α
  classical
  let S : Set (V × M → ℂ) := {F | ∃ (f : V → ℂ) (β : 𝓢(M, ℂ)), ContDiff ℝ ∞ f ∧
    HasCompactSupport f ∧ F = fun p => f p.1 * β p.2}
  let A : Set (V × M → ℂ) := (Submodule.span ℂ S : Set (V × M → ℂ))
  have hgen : ∀ F ∈ S, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    rintro F ⟨f, β, hf, hfc, rfl⟩
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨Cf, hCf⟩ := hfc.exists_bound_of_continuous hf.continuous
      obtain ⟨Cb, hCb⟩ : ∃ C, ∀ y, ‖β y‖ ≤ C :=
        ⟨‖β.toBoundedContinuousFunction‖, fun y => by
          simpa using β.toBoundedContinuousFunction.norm_coe_le_norm y⟩
      refine ⟨Cf * Cb, fun p => ?_⟩
      rw [norm_mul]
      exact mul_le_mul (hCf _) (hCb _) (norm_nonneg _) (le_trans (norm_nonneg _) (hCf p.1))
    · exact (hfd.comp differentiable_fst).mul (β.differentiable.comp differentiable_snd)
    · intro v
      have hder : ∀ p : V × M, fderiv ℝ (fun p : V × M => f p.1 * β p.2) p v =
          fderiv ℝ f p.1 v.1 * β p.2 + f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2 := by
        intro p
        have h1 : HasFDerivAt (fun p : V × M => f p.1)
            ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ V M)) p :=
          (hfd p.1).hasFDerivAt.comp p hasFDerivAt_fst
        have h2 : HasFDerivAt (fun p : V × M => β p.2)
            ((fderiv ℝ β p.2).comp (ContinuousLinearMap.snd ℝ V M)) p :=
          (β.differentiableAt).hasFDerivAt.comp p hasFDerivAt_snd
        rw [show (fun p : V × M => f p.1 * β p.2) = (fun p => f p.1) * (fun p => β p.2) from rfl,
          (h1.mul h2).fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          smul_eq_mul]
        ring
      have hfe : (fun x => fderiv ℝ (fun p : V × M => f p.1 * β p.2) x v) =
          (fun p : V × M => (fun ξ => fderiv ℝ f ξ v.1) p.1 * β p.2) +
          (fun p : V × M => f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2) := by
        ext p
        rw [hder]
        rfl
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => fderiv ℝ f ξ v.1, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, LineDeriv.lineDerivOp v.2 β, hf, hfc, rfl⟩)
      · exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
      · exact (hfc.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℂ => L v.1) (by simp)
    · intro l
      let l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M)
      let l2 : M →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inr ℝ V M)
      have hl : ∀ p : V × M, l p = l1 p.1 + l2 p.2 := by
        intro p
        simp only [l1, l2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply]
        rw [← map_add]
        congr 1
        ext <;> simp
      have htg : Function.HasTemperateGrowth (fun y : M => ((l2 y : ℝ) : ℂ)) := by
        fun_prop
      have hfe : (fun x : V × M => (l x : ℂ) * (f x.1 * β x.2)) =
          (fun p : V × M => (fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ) p.1 * β p.2) +
          (fun p : V × M => f p.1 *
            (SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β) p.2) := by
        ext p
        simp only [Pi.add_apply, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul, hl p]
        push_cast
        ring
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β,
          hf, hfc, rfl⟩)
      · exact (Complex.ofRealCLM.contDiff.comp l1.contDiff).mul hf
      · exact hfc.mul_left
  have hclosed : ∀ F ∈ A, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hgen F hF
    | zero =>
      refine ⟨⟨0, fun x => by simp⟩, differentiable_const 0, fun v => ?_, fun l => ?_⟩
      · have h0 : (fun x => fderiv ℝ (0 : V × M → ℂ) x v) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
      · have h0 : (fun x => (l x : ℂ) * (0 : V × M → ℂ) x) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
    | add F G _ _ hF hG =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      obtain ⟨⟨C2, hC2⟩, hd2, hv2, hl2⟩ := hG
      refine ⟨⟨C1 + C2, fun x => (norm_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩,
        hd1.add hd2, fun v => ?_, fun l => ?_⟩
      · have he : (fun x => fderiv ℝ (F + G) x v) =
            (fun x => fderiv ℝ F x v) + (fun x => fderiv ℝ G x v) := by
          ext x
          rw [fderiv_add (hd1 x) (hd2 x)]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hv1 v) (hv2 v)
      · have he : (fun x => (l x : ℂ) * (F + G) x) =
            (fun x => (l x : ℂ) * F x) + (fun x => (l x : ℂ) * G x) := by
          ext x
          simp [mul_add]
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hl1 l) (hl2 l)
    | smul c F _ hF =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      refine ⟨⟨‖c‖ * C1, fun x => ?_⟩, hd1.const_smul c, fun v => ?_, fun l => ?_⟩
      · rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hC1 x) (norm_nonneg _)
      · have he : (fun x => fderiv ℝ (c • F) x v) = c • (fun x => fderiv ℝ F x v) := by
          ext x
          rw [fderiv_const_smul (hd1 x) c]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hv1 v)
      · have he : (fun x => (l x : ℂ) * (c • F) x) = c • (fun x => (l x : ℂ) * F x) := by
          ext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hl1 l)
  obtain ⟨G, hG⟩ := hS (V × M) A hclosed _ (Submodule.subset_span ⟨h, α, hh, hhc, rfl⟩)
  exact ⟨G, fun ξ y => by rw [hG]⟩
