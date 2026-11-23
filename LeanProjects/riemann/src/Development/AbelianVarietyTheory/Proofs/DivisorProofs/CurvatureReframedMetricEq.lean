import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaGaugeReframeCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGaugeReframeCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAdjointGaugeReframeCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnFibreAgreementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnSuperconnOfPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReframeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFrameAtStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Gauge

theorem gauge_superconn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ)
    (β : Fin n → E) (u : ℝ) (s : Pt E g → Ext (n + n + g))
    (hτ : IsPeriodMap B τ) (hτ' : IsPeriodMap B (fun b => moeb γ (τ b)))
    (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P)
    (hs : DifferentiableOn ℝ s (cov B g)) (P : Pt E g) (hP : P ∈ cov B g) :
    superconn τ (fun Q => h (reframe τ γ Q)) β u (gauge n τ γ s) P =
      frameAt n τ γ P.1 (superconn (fun b => moeb γ (τ b)) h β u s (reframe τ γ P)) := by
  simp only [superconn, map_add, map_smul]
  rw [GlobalTheory.T.nabla_gauge_reframe_compat B τ γ h β s hτ hτ' hh hpos hs P hP, GlobalTheory.T.dbar_gauge_reframe_compat B τ γ s hτ hτ' hs P hP,
    GlobalTheory.T.dbar_adjoint_gauge_reframe_compat B τ γ h s hτ hτ' hh hpos hs P hP]

theorem curv_reframe_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ)
    (β : Fin n → E) (b : E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g))
    (hτ : IsPeriodMap B τ) (hτ' : IsPeriodMap B (fun b => moeb γ (τ b)))
    (hh : ContDiffOn ℝ ∞ h (cov B g)) (hpos : ∀ P ∈ cov B g, 0 < h P) (hb : b ∈ B)
    (hf : ContDiff ℝ ∞ f) (z : Fin g → ℂ) :
    curv τ (fun P => h (reframe τ γ P)) β b u
        (fun y => frameMap n (den γ (τ b)) (f (y ᵥ* (den γ (τ b))⁻¹))) z =
      frameMap n (den γ (τ b)) (curv (fun b => moeb γ (τ b)) h β b u f (z ᵥ* (den γ (τ b))⁻¹)) := by
  have hcov : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hR := GlobalTheory.T.contDiffOn_reframe B τ γ hτ hτ'
  have hmaps : MapsTo (reframe τ γ) (cov B g) (cov B g) := fun P hP => ⟨hP.1, trivial⟩
  have hh₁ : ContDiffOn ℝ ∞ (fun P => h (reframe τ γ P)) (cov B g) := hh.comp hR hmaps
  have hpos₁ : ∀ P ∈ cov B g, 0 < h (reframe τ γ P) := fun P hP => hpos _ (hmaps hP)
  have hc₁ : ContDiffOn ℝ ∞ (fun P : Pt E g => f P.2) (cov B g) := (hf.comp contDiff_snd).contDiffOn
  have hΨ : ContDiffOn ℝ ∞ (gauge n τ γ (fun P : Pt E g => f P.2)) (cov B g) := by
    have hF : ContDiffOn ℝ ∞ (fun P : Pt E g => frameAt n τ γ P.1) (cov B g) :=
      (GlobalTheory.T.contDiffOn_frameAt_of_isPeriodMap n B τ γ hτ hτ').comp contDiffOn_fst (fun (P : Pt E g) (hP : P ∈ cov B g) => hP.1)
    have hF' : ContDiffOn ℝ ∞ (fun P : Pt E g => (frameAt n τ γ P.1).restrictScalars ℝ) (cov B g) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Ext (n + n + g)) (Ext (n + n + g)) ℝ ℝ).contDiff.comp_contDiffOn hF
    exact hF'.clm_apply (hc₁.comp hR hmaps)
  have hlin : ContDiff ℝ ∞ (fun y : Fin g → ℂ => y ᵥ* (den γ (τ b))⁻¹) :=
    ((Matrix.vecMulLinear (den γ (τ b))⁻¹).restrictScalars ℝ).toContinuousLinearMap.contDiff
  have hc : ContDiffOn ℝ ∞ (fun P : Pt E g => frameMap n (den γ (τ b)) (f (P.2 ᵥ* (den γ (τ b))⁻¹))) (cov B g) :=
    (((frameMap n (den γ (τ b))).restrictScalars ℝ).contDiff.comp (hf.comp (hlin.comp contDiff_snd))).contDiffOn
  have hB := GlobalTheory.T.superconn_fibre_agreement B τ (fun P => h (reframe τ γ P)) β u _ _ hτ hh₁ hpos₁ hc hΨ b hb (fun z => rfl) z
  unfold curv
  rw [hB]
  have hev : superconn τ (fun P => h (reframe τ γ P)) β u (gauge n τ γ (fun P : Pt E g => f P.2)) =ᶠ[𝓝 (b, z)]
      gauge n τ γ (superconn (fun b => moeb γ (τ b)) h β u (fun P : Pt E g => f P.2)) := by
    filter_upwards [hcov.mem_nhds (show (b, z) ∈ cov B g from ⟨hb, trivial⟩)] with Q hQ
    exact gauge_superconn B τ γ h β u _ hτ hτ' hh hpos (hc₁.differentiableOn (by simp)) Q hQ
  rw [Pullback.superconn_congr τ _ β u hev]
  rw [gauge_superconn B τ γ h β u _ hτ hτ' hh hpos ((GlobalTheory.T.contDiffOn_superconn_of_period B _ h β u _ hτ' hh hpos hc₁).differentiableOn (by simp)) (b, z) ⟨hb, trivial⟩]
  rfl

theorem curv_conj_closed : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ) (β : Fin n → E) (b : E) (u : ℝ) (f : (Fin g → ℂ) → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → b ∈ B → ContDiff ℝ ∞ f → ∀ z, curv τ (fun P => h (reframe τ γ P)) β b u (fun y => frameMap n (den γ (τ b)) (f (y ᵥ* (den γ (τ b))⁻¹))) z = frameMap n (den γ (τ b)) (curv (fun b => moeb γ (τ b)) h β b u f (z ᵥ* (den γ (τ b))⁻¹)) :=
  fun B τ γ h β b u f hτ hτ' hh hpos hb hf z => curv_reframe_conj B τ γ h β b u f hτ hτ' hh hpos hb hf z

end GlobalTheory.TorsionForm.Gauge
