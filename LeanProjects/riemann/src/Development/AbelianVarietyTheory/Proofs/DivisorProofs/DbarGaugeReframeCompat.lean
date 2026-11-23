import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReframeVerticalDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapWedgeCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFrameAtStatement
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorsionForm.Gauge

section Helpers

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {m : ℕ}

private theorem d01_zero_direction_eq_zero (f : Pt E g → Ext m) (Q : Pt E g) : d01 f Q 0 = 0 := by
  simp [d01]

private theorem d01_sum_direction_eq_sum (f : Pt E g → Ext m) (Q : Pt E g) {ι : Type} (t : Finset ι) (v : ι → Pt E g) :
    d01 f Q (∑ i ∈ t, v i) = ∑ i ∈ t, d01 f Q (v i) := by
  induction t using Finset.cons_induction with
  | empty => simp [d01_zero_direction_eq_zero]
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, Pullback.dbar_add_vector, ih]

private theorem d01_csmul (f : Pt E g → Ext m) (Q v : Pt E g) (z : ℂ) :
    d01 f Q (z • v) = star z • d01 f Q v := by
  have hz : z • v = z.re • v + z.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hz, Pullback.dbar_add_vector, Pullback.dbar_real_smul, Pullback.dbar_real_smul, Pullback.dbar_smul_I]
  conv_rhs => rw [← Complex.re_add_im (star z)]
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, add_smul, mul_smul, Complex.coe_smul]
  simp only [Complex.ofReal_neg, neg_smul, smul_neg, smul_comm (z.im) Complex.I, neg_smul]

private theorem wedge_sum' (i : Fin m) {ι : Type} (t : Finset ι) (w : ι → Ext m) :
    wedge i (∑ j ∈ t, w j) = ∑ j ∈ t, wedge i (w j) := by
  induction t using Finset.cons_induction with
  | empty => simp [Pullback.wedge_zero]
  | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, Pullback.wedge_add, ih]

end Helpers

theorem dbarV_gauge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → DifferentiableOn ℝ s (cov B g) → ∀ P ∈ cov B g, dbarV (gauge n τ γ s) P = frameAt n τ γ P.1 (dbarV s (reframe τ γ P)) := by
  intro E _ _ _ g n B τ γ s hτ hτ' hs P hP
  obtain ⟨hR, hRv⟩ := GlobalTheory.T.reframe_vertical_derivative B τ γ hτ hτ' P hP
  have hB : IsOpen B := hτ.1
  have hcov : IsOpen (cov B g) := hB.prod isOpen_univ
  have hRP : reframe τ γ P ∈ cov B g := ⟨hP.1, trivial⟩
  have hsR : DifferentiableAt ℝ s (reframe τ γ P) := (hs _ hRP).differentiableAt (hcov.mem_nhds hRP)
  have hR' : DifferentiableAt ℝ (reframe τ γ) P := hR.restrictScalars ℝ
  have hΦ : DifferentiableAt ℝ (fun b => frameAt n τ γ b) P.1 :=
    ((GlobalTheory.T.contDiffOn_frameAt_of_isPeriodMap n B τ γ hτ hτ').differentiableOn (by simp) _ hP.1).differentiableAt (hB.mem_nhds hP.1)
  set L := ContinuousLinearMap.restrictScalarsL ℂ (Ext (n + n + g)) (Ext (n + n + g)) ℝ ℝ with hL
  set c : Pt E g → (Ext (n + n + g) →L[ℝ] Ext (n + n + g)) := fun Q => L (frameAt n τ γ Q.1) with hc
  have hc' : DifferentiableAt ℝ c P := L.differentiableAt.comp P (hΦ.comp P differentiableAt_fst)
  have hu : DifferentiableAt ℝ (fun Q => s (reframe τ γ Q)) P := hsR.comp P hR'
  have hcv : ∀ v : Pt E g, v.1 = 0 → fderiv ℝ c P v = 0 := by
    intro v hv
    have : c = (fun b => L (frameAt n τ γ b)) ∘ Prod.fst := rfl
    have hd : DifferentiableAt ℝ (fun b => L (frameAt n τ γ b)) P.1 := L.differentiableAt.comp P.1 hΦ
    rw [this, fderiv_comp P hd differentiableAt_fst, fderiv_fst]
    simp [hv]
  have key : ∀ v : Pt E g, v.1 = 0 → fderiv ℝ (gauge n τ γ s) P v =
      frameAt n τ γ P.1 (fderiv ℝ s (reframe τ γ P) (fderiv ℝ (reframe τ γ) P v)) := by
    intro v hv
    have : gauge n τ γ s = fun Q => c Q (s (reframe τ γ Q)) := rfl
    rw [this, fderiv_clm_apply hc' hu]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, hcv v hv, ContinuousLinearMap.zero_apply, add_zero]
    rw [show (fun Q => s (reframe τ γ Q)) = s ∘ reframe τ γ from rfl, fderiv_comp P hsR hR']
    rfl
  have hRI : ∀ v : Pt E g, fderiv ℝ (reframe τ γ) P (Complex.I • v) =
      Complex.I • fderiv ℝ (reframe τ γ) P v := by
    intro v
    rw [hR.fderiv_restrictScalars ℝ]
    simp
  have hvert : ∀ a : Fin g, d01 (gauge n τ γ s) P (vert E a) =
      frameAt n τ γ P.1 (d01 s (reframe τ γ P) (fderiv ℝ (reframe τ γ) P (vert E a))) := by
    intro a
    have h0 : (vert E a).1 = 0 := rfl
    have h1 : (Complex.I • vert E a).1 = 0 := by simp [vert]
    simp only [d01, key _ h0, key _ h1, hRI, map_add, map_smul]
  simp only [dbarV, map_sum, hvert, hRv, d01_sum_direction_eq_sum, d01_csmul, wedge_sum', map_smul, Pullback.wedge_smul]
  have hfw := fun c w => ((GlobalTheory.T.frameMap_wedge_compat n (den γ (τ P.1)) w).1 c)
  simp only [frameAt_apply] at *
  simp only [hfw]
  exact Finset.sum_comm
end GlobalTheory.TorsionForm.Gauge
