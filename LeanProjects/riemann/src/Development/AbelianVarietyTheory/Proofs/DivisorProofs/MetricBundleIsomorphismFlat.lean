import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSqHolomorphicDdcZeroStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff Topology

noncomputable section

namespace GlobalTheory.BundleIsoMetric

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ddc_eq_sub_of_eqOn {U : Set (Pt E g)} (hU : IsOpen U) {u u₁ u₂ : Pt E g → ℝ}
    (h₁ : ContDiffOn ℝ ∞ u₁ U) (h₂ : ContDiffOn ℝ ∞ u₂ U)
    (hu : ∀ Q ∈ U, u Q = u₁ Q - u₂ Q) {P : Pt E g} (hP : P ∈ U) (v w : Pt E g) :
    ddc u P v w = ddc u₁ P v w - ddc u₂ P v w := by
  have hD : ∀ Q ∈ U, fderiv ℝ u Q = fderiv ℝ u₁ Q - fderiv ℝ u₂ Q := by
    intro Q hQ
    have heq : u =ᶠ[𝓝 Q] u₁ - u₂ :=
      Filter.eventually_of_mem (hU.mem_nhds hQ) fun R hR => hu R hR
    rw [heq.fderiv_eq]
    exact fderiv_sub ((h₁.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hQ))
      ((h₂.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hQ))
  have hd₁ : DifferentiableOn ℝ (fun Q => fderiv ℝ u₁ Q) U :=
    (h₁.fderiv_of_isOpen hU (m := 1) (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (WithTop.coe_le_coe.2 (le_top : ((2:ℕ):ℕ∞) ≤ ⊤)) | exact (WithTop.coe_le_coe.2 (ENat.coe_le_top _)))).differentiableOn (by simp)
  have hd₂ : DifferentiableOn ℝ (fun Q => fderiv ℝ u₂ Q) U :=
    (h₂.fderiv_of_isOpen hU (m := 1) (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (WithTop.coe_le_coe.2 (le_top : ((2:ℕ):ℕ∞) ≤ ⊤)) | exact (WithTop.coe_le_coe.2 (ENat.coe_le_top _)))).differentiableOn (by simp)
  have key : ∀ x : Pt E g, fderiv ℝ (fun Q => fderiv ℝ u Q x) P =
      fderiv ℝ (fun Q => fderiv ℝ u₁ Q x) P - fderiv ℝ (fun Q => fderiv ℝ u₂ Q x) P := by
    intro x
    have heq : (fun Q => fderiv ℝ u Q x) =ᶠ[𝓝 P]
        (fun Q => fderiv ℝ u₁ Q x) - (fun Q => fderiv ℝ u₂ Q x) :=
      Filter.eventually_of_mem (hU.mem_nhds hP) fun R hR => by simp [hD R hR]
    rw [heq.fderiv_eq]
    exact fderiv_sub (((hd₁ P hP).differentiableAt (hU.mem_nhds hP)).clm_apply
        (differentiableAt_const x))
      (((hd₂ P hP).differentiableAt (hU.mem_nhds hP)).clm_apply (differentiableAt_const x))
  simp only [ddc, key, ContinuousLinearMap.sub_apply]
  ring

end GlobalTheory.BundleIsoMetric

namespace GlobalTheory.BundleIsoMetric

theorem div_normSq_isMetric_chernIsFlat : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap B τ → ∀ (M : Submodule ℤ (Fl g)) (j j' : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ)
    (φ : Pt E g → ℂ), IsMetric B τ M j h → ChernIsFlat B τ h → IsBundleIso B τ M j j' φ →
    IsMetric B τ M j' (fun P => h P / ‖φ P‖ ^ 2) ∧
      ChernIsFlat B τ (fun P => h P / ‖φ P‖ ^ 2) := by
  intro g E _ _ _ B τ hτ M j j' h φ hm hc hi
  obtain ⟨hsm, hpos, haut⟩ := hm
  obtain ⟨hφd, hφ0, hφa⟩ := hi
  have hU : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hφc : ContDiffOn ℂ ∞ φ (cov B g) := GlobalTheory.SCV.contDiffOn_of_differentiableOn hU hφd ∞
  have hφs : ContDiffOn ℝ ∞ φ (cov B g) := hφc.restrict_scalars ℝ
  have hn : ContDiffOn ℝ ∞ (fun P => ‖φ P‖ ^ 2) (cov B g) :=
    (contDiff_norm_sq ℝ).comp_contDiffOn hφs
  have hnpos : ∀ P ∈ cov B g, 0 < ‖φ P‖ ^ 2 := fun P hP =>
    pow_pos (norm_pos_iff.2 (hφ0 P hP)) 2
  have htr : ∀ l P, P ∈ cov B g → transl τ l P ∈ cov B g := fun l P hP =>
    ⟨hP.1, Set.mem_univ _⟩
  refine ⟨⟨hsm.div hn fun P hP => (hnpos P hP).ne', fun P hP => div_pos (hpos P hP) (hnpos P hP),
    ?_⟩, ?_⟩
  · intro l hl P hP
    have e1 := haut l hl P hP
    have e2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hφa l hl P hP)
    simp only [norm_mul, mul_pow] at e2
    have a := hnpos _ (htr l P hP)
    have b := hnpos P hP
    rw [div_mul_eq_mul_div, div_eq_div_iff a.ne' b.ne']
    linear_combination (-h (transl τ l P)) * e2 + ‖φ (transl τ l P)‖ ^ 2 * e1
  · intro P hP v w
    have hlog := ddc_eq_sub_of_eqOn hU (u := fun Q => Real.log (h Q / ‖φ Q‖ ^ 2))
      (u₁ := fun Q => Real.log (h Q)) (u₂ := fun Q => Real.log (‖φ Q‖ ^ 2))
      (hsm.log fun Q hQ => (hpos Q hQ).ne') (hn.log fun Q hQ => (hnpos Q hQ).ne')
      (fun Q hQ => Real.log_div (hpos Q hQ).ne' (hnpos Q hQ).ne') hP v w
    rw [hlog, GlobalTheory.T.log_norm_sq_holomorphic_ddc_zero _ φ hU hφd hφ0 P hP v w, sub_zero]
    exact hc P hP v w

end GlobalTheory.BundleIsoMetric
