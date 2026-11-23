import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveClosedOneFormStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory

open Complex

theorem exists_differentiableOn_re_eq_of_ddc_eq_zero {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set (Pt E g)} (u : Pt E g → ℝ)
    (hU : IsOpen U) (hsc : SimplyConnectedSpace U) (hu : ContDiffOn ℝ ∞ u U)
    (hddc : ∀ P ∈ U, ∀ v w : Pt E g, ddc u P v w = 0) :
    ∃ F : Pt E g → ℂ, DifferentiableOn ℂ F U ∧ ∀ P ∈ U, (F P).re = u P := by
  have hua : ∀ a ∈ U, ContDiffAt ℝ 2 u a := fun a ha =>
    (hu.contDiffAt (hU.mem_nhds ha)).of_le (WithTop.coe_le_coe.2 le_top)
  set e : StrongDual ℝ (Pt E g) ≃L[ℝ] StrongDual ℂ (Pt E g) := StrongDual.extendRCLikeL with he
  have he' : ∀ (l : StrongDual ℝ (Pt E g)) (v : Pt E g), e l v = l v - I * l (I • v) :=
    fun l v => rfl
  set R : (Pt E g →L[ℂ] ℂ) →L[ℝ] (Pt E g →L[ℝ] ℂ) :=
    ContinuousLinearMap.restrictScalarsL ℂ (Pt E g) ℂ ℝ ℝ with hR
  set L : StrongDual ℝ (Pt E g) →L[ℝ] (Pt E g →L[ℝ] ℂ) :=
    R.comp (e : StrongDual ℝ (Pt E g) →L[ℝ] StrongDual ℂ (Pt E g)) with hL
  have hLv : ∀ (l : StrongDual ℝ (Pt E g)) (v : Pt E g), L l v = l v - I * l (I • v) :=
    fun l v => rfl
  have hD : ∀ a ∈ U, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) a) a := fun a ha =>
    (((hua a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
  have hω : ∀ a ∈ U, HasFDerivAt (fun x => L (fderiv ℝ u x)) (L.comp (fderiv ℝ (fderiv ℝ u) a)) a :=
    fun a ha => L.hasFDerivAt.comp a (hD a ha)
  have hωc : ContDiffOn ℝ 1 (fun x => L (fderiv ℝ u x)) U :=
    L.contDiff.comp_contDiffOn (hu.fderiv_of_isOpen hU (WithTop.coe_le_coe.2 le_top))
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_primitive_closed_one_form (fun x => L (fderiv ℝ u x)) hU hsc hωc fun a ha x y => by
    rw [(hω a ha).fderiv]
    set B := fderiv ℝ (fderiv ℝ u) a with hB
    have hsym : ∀ x y, B x y = B y x := (hua a ha).isSymmSndFDerivAt (by simp)
    have hdir : ∀ v c, fderiv ℝ (fun Q => fderiv ℝ u Q c) a v = B v c := fun v c => by
      rw [((hD a ha).clm_apply (hasFDerivAt_const c a)).fderiv]
      simp [hB]
    have h4 : B x (I • y) = B y (I • x) := by
      have := hddc a ha y x
      simp only [ddc, hdir] at this
      have hπ : (1 / (4 * π) : ℝ) ≠ 0 := by positivity
      have := (mul_eq_zero.1 this).resolve_left hπ
      linarith
    simp only [ContinuousLinearMap.comp_apply, hLv]
    rw [h4, hsym x y]
  have hFc : ∀ a ∈ U, HasFDerivAt F (e (fderiv ℝ u a)) a := fun a ha =>
    hasFDerivAt_of_restrictScalars ℝ (hF a ha) rfl
  have hG : ∀ a ∈ U, HasFDerivAt (fun x => (F x).re - u x) (0 : Pt E g →L[ℝ] ℝ) a :=
    fun a ha => by
      have h1 := (reCLM.hasFDerivAt.comp a (hF a ha)).sub
        ((hua a ha).differentiableAt (by simp)).hasFDerivAt
      refine h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
      simp [hLv]
  have hpc : IsPreconnected U := by
    haveI : ConnectedSpace U := inferInstance
    exact isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨c, hc⟩ := hU.exists_is_const_of_fderiv_eq_zero (𝕜 := ℝ) hpc
    (fun a ha => (hG a ha).differentiableAt.differentiableWithinAt) fun a ha => (hG a ha).fderiv
  refine ⟨fun x => F x - c, fun a ha =>
    ((hFc a ha).differentiableAt.sub_const _).differentiableWithinAt, fun x hx => ?_⟩
  have := hc x hx
  simp only [sub_re, ofReal_re]
  linarith

end GlobalTheory
