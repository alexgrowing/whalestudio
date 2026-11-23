import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReQuad

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.ThetaMet
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.ThetaMetDdc

theorem chernIsFlat_exp_quad :
    ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
      {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ContDiffOn ℝ ∞ (flat τ) (cov B g) →
      ContDiffOn ℝ ∞ (quad τ) (cov B g) → ContDiffOn ℝ ∞ (reQuad τ) (cov B g) →
      (∀ P ∈ cov B g, ∀ v : Pt E g, fderiv ℝ (quad τ) P (Complex.I • v) =
        fderiv ℝ (reQuad τ) P v + 2 * ∑ i, flat τ P (Sum.inl i) * dflat τ P v (Sum.inr i)) →
      ChernIsFlat B τ (fun P => Real.exp (-2 * π * quad τ P)) := by
  intro g E _ _ B τ hτ hflat hquad hreQ hdc
  unfold ChernIsFlat
  intro P hP v w
  have hS : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have h1 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have h2 : minSmoothness ℝ 2 ≤ ∞ := by simp [minSmoothness]; exact WithTop.coe_le_coe.2 le_top
  have hR : ContDiffAt ℝ ∞ (reQuad τ) P := hreQ.contDiffAt (hS.mem_nhds hP)
  have hF : ContDiffAt ℝ ∞ (flat τ) P := hflat.contDiffAt (hS.mem_nhds hP)
  have hRd : DifferentiableAt ℝ (fderiv ℝ (reQuad τ)) P :=
    (hR.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableAt one_ne_zero
  have hFd : DifferentiableAt ℝ (fderiv ℝ (flat τ)) P :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 le_top)).differentiableAt one_ne_zero
  have hFa : DifferentiableAt ℝ (flat τ) P := hF.differentiableAt h1
  have hsR := hR.isSymmSndFDerivAt h2
  have hsF := hF.isSymmSndFDerivAt h2
  have hdq : ∀ Q ∈ cov B g, fderiv ℝ (fun Q => -2 * π * quad τ Q) Q =
      (-2 * π) • fderiv ℝ (quad τ) Q := fun Q hQ =>
    fderiv_const_mul ((hquad.contDiffAt (hS.mem_nhds hQ)).differentiableAt h1) _
  have hev : ∀ v : Pt E g, (fun Q => fderiv ℝ (fun Q => -2 * π * quad τ Q) Q (Complex.I • v))
      =ᶠ[nhds P] fun Q => -2 * π * (fderiv ℝ (reQuad τ) Q v +
        2 * ∑ i, flat τ Q (Sum.inl i) * fderiv ℝ (flat τ) Q v (Sum.inr i)) := by
    intro v
    filter_upwards [hS.mem_nhds hP] with Q hQ
    rw [hdq Q hQ, ContinuousLinearMap.smul_apply, hdc Q hQ v, smul_eq_mul]
    rfl
  have key : ∀ v w : Pt E g, fderiv ℝ (fun Q => -2 * π * (fderiv ℝ (reQuad τ) Q v +
        2 * ∑ i, flat τ Q (Sum.inl i) * fderiv ℝ (flat τ) Q v (Sum.inr i))) P w =
      -2 * π * (fderiv ℝ (fderiv ℝ (reQuad τ)) P w v + 2 * ∑ i,
        (flat τ P (Sum.inl i) * fderiv ℝ (fderiv ℝ (flat τ)) P w v (Sum.inr i) +
          fderiv ℝ (flat τ) P v (Sum.inr i) * fderiv ℝ (flat τ) P w (Sum.inl i))) := by
    intro v w
    have e1 : HasFDerivAt (fun Q => fderiv ℝ (reQuad τ) Q v)
        ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (reQuad τ)) P)) P :=
      (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp P hRd.hasFDerivAt
    have e2 : ∀ i, HasFDerivAt (fun Q => flat τ Q (Sum.inl i))
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inl i)).comp
          (fderiv ℝ (flat τ) P)) P := fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inl i)).hasFDerivAt.comp
        P hFa.hasFDerivAt
    have e3 : ∀ i, HasFDerivAt (fun Q => fderiv ℝ (flat τ) Q v (Sum.inr i))
        (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ) (Sum.inr i)).comp
          (ContinuousLinearMap.apply ℝ (Fl g) v)).comp (fderiv ℝ (fderiv ℝ (flat τ)) P)) P :=
      fun i => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g ⊕ Fin g => ℝ)
        (Sum.inr i)).comp (ContinuousLinearMap.apply ℝ (Fl g) v)).hasFDerivAt.comp P hFd.hasFDerivAt
    have hD := ((e1.fun_add ((HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (e2 i).fun_mul (e3 i)).const_mul 2)).const_mul (-2 * π))
    have e : fderiv ℝ (fun Q => -2 * π * (fderiv ℝ (reQuad τ) Q v +
        2 * ∑ i, flat τ Q (Sum.inl i) * fderiv ℝ (flat τ) Q v (Sum.inr i))) P = _ := hD.fderiv
    rw [e]
    clear hev hdq hsR hsF hdc hquad hreQ hflat e e1 e2 e3 hD
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hom : om0 τ P ![v, w] = riem (dflat τ P v) (dflat τ P w) := rfl
  simp only [ddc, Real.log_exp]
  rw [(hev v).fderiv_eq, (hev w).fderiv_eq, key v w, key w v, hom, hsR w v]
  simp only [hsF w v, riem, dflat]
  have aux : ∀ a s t : ℝ, -(1 / (4 * π) * (-2 * π * (a + 2 * s) - -2 * π * (a + 2 * t))) =
      s - t := by
    intro a s t
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [aux, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ThetaMetDdc
