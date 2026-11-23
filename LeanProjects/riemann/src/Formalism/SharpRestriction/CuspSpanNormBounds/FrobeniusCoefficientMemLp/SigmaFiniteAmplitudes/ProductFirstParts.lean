import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.ProductFirstZerothParts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem qG_invM (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x a : Mt k r) :
    qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a) = Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x) := rfl

theorem qG_inv_mem {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {x a : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) (ha : Matrix.of a ∈ UH (Hpk k r)) :
    Matrix.of (qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∈ UH (Hpk k r) := by
  rw [qG_invM, Equiv.apply_symm_apply]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
    (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha)) hγ) hx

section Cell

variable (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
  {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μG μR νR : Measure (Mt k r)}

theorem PsiM_stab (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) {p : PairSp k r} (hp : InPair L p)
    {a : Mt k r} (ha : Matrix.of a ∈ RStab k r γ) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) = PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) := by
  have hq := qG_inv_mem hγ hx ha.1.1
  rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hq, qG_invM]
  show PsiM L w0 v v' ξ ξ' γ (stabAct γ (Matrix.of a) p, x) = _
  rw [PsiM_eq L w0 v v' ξ ξ' hγ (inPair_stab L hp ha) hx, Psi_stab L w0 v v' ξ ξ' hγ hrel hp ha x]

theorem lint_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR =
      ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hmeasP : Measurable (fun y : Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ) :=
    ((sm_PsiM L w0 v v' ξ ξ' γ).measurable.comp measurable_prodMk_left).enorm
  have hmeasQ : Measurable (fun q : Mt k r × Mt k r => ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ) :=
    hmeasP.comp (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  calc ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x)‖ₑ ∂νR ∂μR
      = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a))‖ₑ ∂νR ∂μR := by
        refine lintegral_congr_ae (hR.mono (fun a ha => ?_))
        refine lintegral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫⁻ a, ∫⁻ x, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂νR ∂μR :=
        hinv.lintegral_comp hmeasQ.lintegral_prod_left'
    _ = ∫⁻ x, ∫⁻ a, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a))‖ₑ ∂μR ∂νR :=
        lintegral_lintegral_swap (hmeasQ.comp measurable_swap).aemeasurable
    _ = ∫⁻ q, ‖PsiM L w0 v v' ξ ξ' γ (p, qG γ q)‖ₑ ∂(νR.prod μR) :=
        (lintegral_prod _ hmeasQ.aemeasurable).symm
    _ = ∫⁻ y, ‖PsiM L w0 v v' ξ ξ' γ (p, y)‖ₑ ∂μG := by
        rw [muG_eq_map hμR hQ, lintegral_map hmeasP (continuous_qG γ).measurable]
    _ = ∫⁻ y, ‖Psi L w0 v v' ξ ξ' γ p y‖ₑ ∂μG := by
        have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
        refine lintegral_congr_ae (hG.mono (fun y hy => ?_))
        dsimp only
        rw [PsiM_eq L w0 v v' ξ ξ' hγ hp hy]

theorem int_cell (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ) (hμG : IsHaarOn (UH (Hpk k r)) μG)
    (hμR : IsHaarOn (RStab k r γ) μR) (hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR)
    (hQ : PI.BesselPeriodGGP.IsQuotMeas μG (μR.map (fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j)) νR)
    {p : PairSp k r} (hp : InPair L p) (hint : Integrable (fun y => Psi L w0 v v' ξ ξ' γ p y) μG) :
    ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := by
  haveI : SigmaFinite μR := hμR.1
  haveI : SigmaFinite νR := sigmaFinite_nuR hμG hμR hQ
  have hsmP : StronglyMeasurable (fun y : Mt k r => PsiM L w0 v v' ξ ξ' γ (p, y)) :=
    (sm_PsiM L w0 v v' ξ ξ' γ).comp_measurable measurable_prodMk_left
  have hsmQ : StronglyMeasurable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) :=
    hsmP.comp_measurable (continuous_qG γ).measurable
  have hR : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := ae_iff.mpr hμR.2.2.1
  have hU := ae_uh_nuR hγ hμG hμR hQ
  have hG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := ae_iff.mpr hμG.2.2.1
  have hGeq : (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) =ᵐ[μG] fun y => Psi L w0 v v' ξ ξ' γ p y :=
    hG.mono (fun y hy => PsiM_eq L w0 v v' ξ ξ' hγ hp hy)
  have hintP : Integrable (fun y => PsiM L w0 v v' ξ ξ' γ (p, y)) μG := hint.congr hGeq.symm
  have hμ := muG_eq_map hμR hQ
  have hintQ : Integrable (fun q : Mt k r × Mt k r => PsiM L w0 v v' ξ ξ' γ (p, qG γ q)) (νR.prod μR) := by
    rw [hμ] at hintP
    exact (integrable_map_measure hsmP.aestronglyMeasurable (continuous_qG γ).measurable.aemeasurable).mp hintP
  have hsmA : StronglyMeasurable (fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR) :=
    hsmQ.integral_prod_left
  calc ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (mStab γ (p, a), x) ∂νR ∂μR
      = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, Formalism.FourierDecayAlt.P.B7.invM a)) ∂νR ∂μR := by
        refine integral_congr_ae (hR.mono (fun a ha => ?_))
        refine integral_congr_ae (hU.mono (fun x hx => ?_))
        dsimp only
        rw [PsiM_stab L w0 v v' ξ ξ' hγ hrel hp ha hx]
    _ = ∫ a, ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR ∂μR := by
        have h := integral_map (μ := μR) hinv.measurable.aemeasurable
          (f := fun a => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂νR)
          (by rw [hinv.map_eq]; exact hsmA.aestronglyMeasurable)
        rw [hinv.map_eq] at h
        exact h.symm
    _ = ∫ x, ∫ a, PsiM L w0 v v' ξ ξ' γ (p, qG γ (x, a)) ∂μR ∂νR :=
        integral_integral_swap hintQ.swap
    _ = ∫ q, PsiM L w0 v v' ξ ξ' γ (p, qG γ q) ∂(νR.prod μR) := (integral_prod _ hintQ).symm
    _ = ∫ y, PsiM L w0 v v' ξ ξ' γ (p, y) ∂μG := by
        rw [hμ, integral_map (continuous_qG γ).measurable.aemeasurable hsmP.aestronglyMeasurable]
    _ = ∫ y, Psi L w0 v v' ξ ξ' γ p y ∂μG := integral_congr_ae hGeq

end Cell

end Formalism.MainNotions.S.Pv.AmpDDPf
