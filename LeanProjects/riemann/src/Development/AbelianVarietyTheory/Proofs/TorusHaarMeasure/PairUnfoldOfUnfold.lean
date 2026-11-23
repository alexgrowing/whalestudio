import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PairUnfold

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def pairDens {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) :
    Frame X.Ψ r → ℂ :=
  fun y => X.dom.piecewise (fun y => P y * (starRingEnd ℂ) (f0 y)) 0 y * ((W y).toReal : ℂ)

theorem pairDens_dom {r : ℕ} (X : Data E r) (P f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W x = P x * (starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ) := by
  simp [pairDens, Set.piecewise, hx]

theorem pairDens_meas {r : ℕ} (X : Data E r) {P f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ContinuousOn P X.dom) (hf : ContinuousOn f0 X.dom) (hW : Measurable W) :
    Measurable (pairDens X P f0 W) := by
  classical
  unfold pairDens
  exact (ContinuousOn.measurable_piecewise
    (hP.mul (Complex.continuous_conj.comp_continuousOn hf)) continuousOn_const
    (FourierCoefficientDomain.isOpen_dom X).measurableSet).mul
    (Complex.measurable_ofReal.comp hW.ennreal_toReal)

theorem pairDens_rmul {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hP : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x)
    (hf : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) :
    ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, pairDens X P f0 W (rmul x b) = pairDens X P f0 W x := by
  intro x hx b hb
  have h0 := OntoE.bchar_ne X la hb
  have h1 : (starRingEnd ℂ) (bchar la b) ≠ 0 := by simpa using h0
  rw [pairDens_dom X P f0 W (OntoS.dom_rmul X hx hb), pairDens_dom X P f0 W hx, hP x hx b hb,
    hf x hx b hb, hW.2.1 x hx b hb, ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg _), map_mul]
  push_cast
  rw [← Complex.mul_conj']
  field_simp

theorem pairDens_lact {r : ℕ} (X : Data E r) {la : Wt X.Ψ r} {P f0 : Frame X.Ψ r → ℂ}
    {W : Frame X.Ψ r → ℝ≥0∞}
    (hf : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    pairDens X P f0 W (lact γ x) =
      (X.χ la γ)⁻¹ * P (lact γ x) * ((starRingEnd ℂ) (f0 x) * ((W x).toReal : ℂ)) := by
  rw [pairDens_dom X P f0 W (OntoS.dom_lact X hγ hx), hf γ hγ x hx, hW.2.2 γ hγ x hx, map_mul,
    Complex.inv_eq_conj (OntoE.chi_norm X la hγ)]
  ring

theorem kaF_meas {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaF X x0 bb) := by
  unfold kaF rhF
  refine Real.measurable_exp.comp (measurable_const.mul (Measurable.neg ?_))
  refine Finset.measurable_fun_sum _ fun τ _ => Real.measurable_log.comp ?_
  exact (OntoB.cd_dmin X x0 τ _).continuous.norm.measurable

theorem enorm_le {k : ℝ} (hk : 0 < k) (u g : ℂ) (w : ℝ≥0∞) :
    ‖u * (starRingEnd ℂ) g * (w.toReal : ℂ)‖ₑ ≤
      ENNReal.ofReal (‖u‖ ^ 2 / k) * w + ENNReal.ofReal k * (ENNReal.ofReal (‖g‖ ^ 2) * w) := by
  have h1 := OntoG.amgm (x := ‖u‖) (y := ‖g‖) hk
  have h2 : ‖u‖ * ‖g‖ ≤ ‖u‖ ^ 2 / k + k * ‖g‖ ^ 2 := by
    have : 0 ≤ ‖u‖ * ‖g‖ := by positivity
    linarith
  rw [← ofReal_norm_eq_enorm, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul (by positivity),
    ← mul_assoc, ← ENNReal.ofReal_mul hk.le, ← add_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal h2) ENNReal.ofReal_toReal_le

theorem pairUnfold_of_unfold :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (KaUnfoldStatement (E := E)) → (PairUnfoldStatement (E := E)) := by
  intro hU hKa r X x0 hx0 hPD la W bb hW _ hbb F P _ hIn hP hPF FF hFF f0 hf0 hfF
  have hsec := hf0.1.1
  obtain ⟨C, hCt, hC⟩ := hKa r X x0 hx0 hPD FF hFF bb hbb
  have hφm := OntoE.phiF_meas X hsec.1.continuousOn hW.1
  have hφ := hC (OntoE.phiF X f0 W) hφm (OntoE.phiF_B X hsec.2.1 hW) (OntoE.phiF_G X hsec.2.2 hW)
  have hFFeq : ∫⁻ z in FF, OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ENNReal.ofReal (‖f0 (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 :=
    setLIntegral_congr_fun hFF.1 (fun z hz => OntoE.phiF_dom X f0 W (hFF.2.1 hz))
  have hI : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine hφ.trans_lt (ENNReal.mul_lt_top hCt ?_)
    rw [hFFeq]; exact hfF
  have hcm : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hae := FundSetPf.ae_OmF' X x0
  have hm := pairDens_meas X hP.1.continuousOn hsec.1.continuousOn hW.1
  have hint : Integrable (fun z => pairDens X P f0 W (cpt X x0 z)) (muF X x0) := by
    refine ⟨(hm.comp hcm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ z, ‖pairDens X P f0 W (cpt X x0 z)‖ₑ ∂muF X x0
        ≤ ∫⁻ z, (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) +
            ENNReal.ofReal (kaF X x0 bb z) * OntoE.phiF X f0 W (cpt X x0 z)) ∂muF X x0 := by
          refine lintegral_mono_ae (hae.mono fun z hz => ?_)
          rw [pairDens_dom X P f0 W hz, OntoE.phiF_dom X f0 W hz, hPF z hz]
          exact enorm_le (Real.exp_pos _) _ _ _
      _ < ⊤ := by
          have hB : Measurable fun z => ENNReal.ofReal (kaF X x0 bb z) *
              OntoE.phiF X f0 W (cpt X x0 z) :=
            (ENNReal.measurable_ofReal.comp (kaF_meas X x0 bb)).mul (hφm.comp hcm)
          rw [lintegral_add_right _ hB]
          exact ENNReal.add_lt_top.2 ⟨hIn, hI⟩
  have key := hU r X x0 hx0 FF hFF _ hm (pairDens_rmul X hP.2 hsec.2.1 hW) hint
  calc _ = ∫ z in FF, ∑' γ : X.Γ, pairDens X P f0 W (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
        refine setIntegral_congr_fun hFF.1 fun z hz => ?_
        have hz' : cpt X x0 z ∈ X.dom := hFF.2.1 hz
        simp only [poin]
        rw [mul_assoc, ← tsum_mul_right]
        exact tsum_congr fun γ => (pairDens_lact X hsec.2.2 hW γ.2 hz').symm
    _ = _ := by
        rw [← key]
        refine integral_congr_ae (hae.mono fun z hz => ?_)
        simp only
        rw [pairDens_dom X P f0 W hz, hPF z hz]

end

end GlobalTheory.PairUnfold
