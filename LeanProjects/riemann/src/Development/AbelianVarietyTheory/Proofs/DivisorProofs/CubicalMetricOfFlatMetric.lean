import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormMulPullZeroSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqHolomorphicDdcZeroStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.NormCubical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem ddc_congr {u u' : Pt E g → ℝ} {P : Pt E g} (h : u =ᶠ[nhds P] u') (v w : Pt E g) :
    ddc u P v w = ddc u' P v w := by
  have key : ∀ a : Pt E g, (fun Q => fderiv ℝ u Q a) =ᶠ[nhds P] (fun Q => fderiv ℝ u' Q a) := by
    intro a
    filter_upwards [h.eventuallyEq_nhds] with Q hQ
    rw [hQ.fderiv_eq]
  simp only [ddc, (key _).fderiv_eq]

theorem diff_fderiv_apply {u : Pt E g → ℝ} {P : Pt E g} (hu : ContDiffAt ℝ 2 u P) (a : Pt E g) :
    DifferentiableAt ℝ (fun Q => fderiv ℝ u Q a) P := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) P := hu.fderiv_right (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const a)

theorem ddc_sub {u₁ u₂ : Pt E g → ℝ} {P : Pt E g} (h₁ : ContDiffAt ℝ 2 u₁ P)
    (h₂ : ContDiffAt ℝ 2 u₂ P) (v w : Pt E g) :
    ddc (fun Q => u₁ Q - u₂ Q) P v w = ddc u₁ P v w - ddc u₂ P v w := by
  have ev : ∀ a : Pt E g, (fun Q => fderiv ℝ (fun Q => u₁ Q - u₂ Q) Q a) =ᶠ[nhds P]
      (fun Q => fderiv ℝ u₁ Q a - fderiv ℝ u₂ Q a) := by
    intro a
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with Q hQ₁ hQ₂
    exact congrArg (fun f => f a) ((hQ₁.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hQ₂.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  simp only [ddc, (ev _).fderiv_eq]
  have e : ∀ a : Pt E g, fderiv ℝ (fun Q => fderiv ℝ u₁ Q a - fderiv ℝ u₂ Q a) P =
      fderiv ℝ (fun Q => fderiv ℝ u₁ Q a) P - fderiv ℝ (fun Q => fderiv ℝ u₂ Q a) P := fun a =>
    ((diff_fderiv_apply h₁ a).hasFDerivAt.sub (diff_fderiv_apply h₂ a).hasFDerivAt).fderiv
  rw [e, e]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem ddc_comp_clm (L : Pt E g →L[ℂ] Pt E g) {u : Pt E g → ℝ} {P : Pt E g}
    (hu : ContDiffAt ℝ 2 u (L P)) (v w : Pt E g) :
    ddc (fun Q => u (L Q)) P v w = ddc u (L P) (L v) (L w) := by
  have hL : Continuous L := L.continuous
  have ev : ∀ a : Pt E g, (fun Q => fderiv ℝ (fun Q => u (L Q)) Q (Complex.I • a)) =ᶠ[nhds P]
      (fun Q => fderiv ℝ u (L Q) (Complex.I • L a)) := by
    intro a
    have : ∀ᶠ Q in nhds P, ContDiffAt ℝ 2 u (L Q) :=
      hL.continuousAt.eventually (hu.eventually (by simp))
    filter_upwards [this] with Q hQ
    have hd : HasFDerivAt (fun Q => u (L Q)) ((fderiv ℝ u (L Q)).comp (L.restrictScalars ℝ)) Q :=
      (hQ.differentiableAt (by norm_num)).hasFDerivAt.comp Q (L.restrictScalars ℝ).hasFDerivAt
    rw [hd.fderiv]
    simp
  have hψ : ∀ a : Pt E g, DifferentiableAt ℝ (fun R => fderiv ℝ u R (Complex.I • L a)) (L P) :=
    fun a => diff_fderiv_apply hu _
  have hc : ∀ a b : Pt E g, fderiv ℝ (fun Q => fderiv ℝ u (L Q) (Complex.I • L a)) P b =
      fderiv ℝ (fun R => fderiv ℝ u R (Complex.I • L a)) (L P) (L b) := by
    intro a b
    have hd := (hψ a).hasFDerivAt.comp P (L.restrictScalars ℝ).hasFDerivAt
    rw [show (fun Q => fderiv ℝ u (L Q) (Complex.I • L a)) =
      (fun R => fderiv ℝ u R (Complex.I • L a)) ∘ L from rfl, hd.fderiv]
    rfl
  simp only [ddc, (ev _).fderiv_eq, hc]

theorem normalise_cubical : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) (r : E → ℂ), IsMetric B τ (stdLat g) j h → ChernIsFlat B τ h → IsRigidification B r → IsCubicalMetric B τ j r (fun P => h P / (h (zeroSec g P.1) * ‖r P.1‖ ^ 2)) := by
  intro g E _ _ _ B τ hτ j h r hM hC hR
  have hB : IsOpen B := hτ.1
  have hU : IsOpen (cov B g) := hB.prod isOpen_univ
  have hzs : ∀ b ∈ B, zeroSec g b ∈ cov B g := fun b hb => ⟨hb, trivial⟩
  have hrpos : ∀ b ∈ B, 0 < ‖r b‖ ^ 2 := fun b hb => pow_pos (norm_pos_iff.2 (hR.2 b hb)) 2
  have hDpos : ∀ b ∈ B, 0 < h (zeroSec g b) * ‖r b‖ ^ 2 := fun b hb =>
    mul_pos (hM.2.1 _ (hzs b hb)) (hrpos b hb)
  have two_le : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hr : ContDiffOn ℝ ∞ (fun b => ‖r b‖ ^ 2) B := by
    have h1 : ContDiffOn ℂ ∞ r B :=
      (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hB hR.1).contDiffOn hB.uniqueDiffOn
    exact (contDiff_norm_sq ℝ).comp_contDiffOn (h1.restrict_scalars ℝ)
  have hzsm : ContDiff ℝ ∞ (fun P : Pt E g => zeroSec g P.1) :=
    contDiff_fst.prodMk contDiff_const
  have hh0 : ContDiffOn ℝ ∞ (fun P : Pt E g => h (zeroSec g P.1)) (cov B g) :=
    hM.1.comp hzsm.contDiffOn fun P hP => hzs P.1 hP.1
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hM.1.div (hh0.mul (hr.comp contDiffOn_fst fun P hP => hP.1))
      fun P hP => ne_of_gt (hDpos P.1 hP.1)
  · intro P hP
    exact div_pos (hM.2.1 P hP) (hDpos P.1 hP.1)
  · intro l hl P hP
    show h (transl τ l P) / (h (zeroSec g P.1) * ‖r P.1‖ ^ 2) * ‖j l P‖ ^ 2 =
      h P / (h (zeroSec g P.1) * ‖r P.1‖ ^ 2)
    rw [div_mul_eq_mul_div, hM.2.2 l hl P hP]
  · intro P hP v w
    have hP1 : P.1 ∈ B := hP.1
    let L : Pt E g →L[ℂ] Pt E g :=
      (ContinuousLinearMap.inl ℂ E (Fin g → ℂ)).comp (ContinuousLinearMap.fst ℂ E (Fin g → ℂ))
    have hLQ : ∀ Q : Pt E g, L Q = zeroSec g Q.1 := fun Q => by simp [L, zeroSec]
    have hu1 : ∀ Q ∈ cov B g, ContDiffAt ℝ 2 (fun Q => Real.log (h Q)) Q := fun Q hQ =>
      ((hM.1.contDiffAt (hU.mem_nhds hQ)).log (ne_of_gt (hM.2.1 Q hQ))).of_le two_le
    have hu2 : ContDiffAt ℝ 2 (fun Q : Pt E g => Real.log (h (zeroSec g Q.1))) P := by
      have := (hu1 _ (hzs P.1 hP1)).comp P (hzsm.of_le two_le).contDiffAt
      exact this
    have hu3 : ContDiffAt ℝ 2 (fun Q : Pt E g => Real.log (‖r Q.1‖ ^ 2)) P :=
      (((hr.contDiffAt (hB.mem_nhds hP1)).comp P contDiffAt_fst).log
        (ne_of_gt (hrpos P.1 hP1))).of_le two_le
    have heq : (fun Q => Real.log (h Q / (h (zeroSec g Q.1) * ‖r Q.1‖ ^ 2))) =ᶠ[nhds P]
        fun Q => (Real.log (h Q) - Real.log (h (zeroSec g Q.1))) - Real.log (‖r Q.1‖ ^ 2) := by
      filter_upwards [hU.mem_nhds hP] with Q hQ
      rw [Real.log_div (ne_of_gt (hM.2.1 Q hQ)) (ne_of_gt (hDpos _ hQ.1)),
        Real.log_mul (ne_of_gt (hM.2.1 _ (hzs _ hQ.1))) (ne_of_gt (hrpos _ hQ.1)), sub_sub]
    rw [ddc_congr heq, ddc_sub ((hu1 P hP).sub hu2) hu3, ddc_sub (hu1 P hP) hu2]
    have h3 : ddc (fun Q : Pt E g => Real.log (‖r Q.1‖ ^ 2)) P v w = 0 :=
      GlobalTheory.T.log_norm_sq_holomorphic_ddc_zero (cov B g) (fun Q => r Q.1) hU
        (hR.1.comp differentiableOn_fst fun Q hQ => hQ.1) (fun Q hQ => hR.2 _ hQ.1) P hP v w
    have h2 : ddc (fun Q : Pt E g => Real.log (h (zeroSec g Q.1))) P v w = 0 := by
      have e1 : (fun Q : Pt E g => Real.log (h (zeroSec g Q.1))) =
          fun Q => (fun R => Real.log (h R)) (L Q) := by
        funext Q; rw [hLQ]
      rw [e1, ddc_comp_clm L (u := fun R => Real.log (h R)) (by rw [hLQ]; exact hu1 _ (hzs P.1 hP1)) v w]
      have hc := hC (L P) (by rw [hLQ]; exact hzs P.1 hP1) (L v) (L w)
      have hfz : fderiv ℝ (zeroSec g) P.1 = ContinuousLinearMap.inl ℝ E (Fin g → ℂ) := by
        have : zeroSec g = ⇑(ContinuousLinearMap.inl ℝ E (Fin g → ℂ)) := by
          funext b; simp [zeroSec]
        rw [this, ContinuousLinearMap.fderiv]
      have ev : (⇑(ContinuousLinearMap.inl ℝ E (Fin g → ℂ)) ∘ ![v.1, w.1]) = ![L v, L w] := by
        funext i; fin_cases i <;> simp [hLQ, zeroSec]
      have h0 : om0 τ (zeroSec g P.1) ![L v, L w] = 0 := by
        have h00 := congrArg (fun f => f ![v.1, w.1]) ((GlobalTheory.T.flat_form_mul_pull_zero_section hτ).2 P.1 hP1)
        simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hfz] at h00
        rw [← ev]
        exact h00
      rw [← hLQ P] at h0
      linarith
    rw [h2, h3, sub_zero, sub_zero]
    exact hC P hP v w
  · intro b hb
    show h (zeroSec g b) / (h (zeroSec g b) * ‖r b‖ ^ 2) * ‖r b‖ ^ 2 = 1
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq (ne_of_gt (hDpos b hb))]

end GlobalTheory.NormCubical
