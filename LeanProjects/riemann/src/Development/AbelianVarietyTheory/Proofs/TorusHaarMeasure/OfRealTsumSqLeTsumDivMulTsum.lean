import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ofReal_tsum_sq_le_tsum_div_mul_tsum {ι : Type*} (a k : ι → ℝ) (hs : Summable a)
    (hk : ∀ i, 0 < k i) :
    ENNReal.ofReal ((∑' i, a i) ^ 2) ≤
      (∑' i, ENNReal.ofReal (a i ^ 2 / k i)) * ∑' i, ENNReal.ofReal (k i) := by
  have ht : Filter.Tendsto (fun s : Finset ι => ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal ((∑' i, a i) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (Filter.Tendsto.pow hs.hasSum 2)
  refine le_of_tendsto' ht fun s => ?_
  have h1 : (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i := by
    have h0 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => a i / Real.sqrt (k i))
      (fun i => Real.sqrt (k i))
    have e1 : ∀ i, a i / Real.sqrt (k i) * Real.sqrt (k i) = a i := fun i =>
      div_mul_cancel₀ _ (Real.sqrt_pos.2 (hk i)).ne'
    have e2 : ∀ i, Real.sqrt (k i) ^ 2 = k i := fun i => Real.sq_sqrt (hk i).le
    simp only [e1, div_pow, e2] at h0
    exact h0
  have hd : ∀ i, 0 ≤ a i ^ 2 / k i := fun i => div_nonneg (sq_nonneg _) (hk i).le
  calc ENNReal.ofReal ((∑ i ∈ s, a i) ^ 2)
      ≤ ENNReal.ofReal ((∑ i ∈ s, a i ^ 2 / k i) * ∑ i ∈ s, k i) := ENNReal.ofReal_le_ofReal h1
    _ = (∑ i ∈ s, ENNReal.ofReal (a i ^ 2 / k i)) * ∑ i ∈ s, ENNReal.ofReal (k i) := by
      rw [ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => hd i),
        ENNReal.ofReal_sum_of_nonneg fun i _ => hd i,
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hk i).le]
    _ ≤ _ := mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s)

theorem ae_mem_OmF_muF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (OntoB.isOpen_OmF X x0).measurableSet)

theorem poincare_sqIntegrable_fundSet :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) := by
  intro hunf r X x0 hx0 la W bb κ hκ hW _ F P hF hP hPF hsum FF hFF
  obtain ⟨hκm, hκp, hκB, hκa, ⟨C, hC, hκC⟩, -⟩ := hκ
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => OntoE.phiF X P W y * ENNReal.ofReal (κ y)⁻¹ with hψ
  have hψm : Measurable ψ :=
    (OntoE.phiF_meas X hP.1.continuousOn hW.1).mul hκm.inv.ennreal_ofReal
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [hψ, OntoE.phiF_B X hP.2 hW x hx b hb, hκB x hx b hb]
  have hψd : ∀ x ∈ X.dom, ψ x = ENNReal.ofReal (‖P x‖ ^ 2 / κ x) * W x := by
    intro x hx
    simp only [hψ, OntoE.phiF_dom X P W hx]
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hfin : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hF
    filter_upwards [ae_mem_OmF_muF X x0] with z hz
    rw [hψd _ hz, hPF z hz, hκa z hz]
  rw [hunf r X x0 hx0 FF hFF ψ hψm hψB] at hfin
  have hpt : ∀ x ∈ X.dom, ENNReal.ofReal (‖poin X la P x‖ ^ 2) * W x ≤
      C * ∑' γ : X.Γ, ψ (lact γ.1 x) := by
    intro x hx
    have hγx : ∀ γ : X.Γ, lact γ.1 x ∈ X.dom := fun γ => OntoS.dom_lact X γ.2 hx
    have hn : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ = ‖P (lact γ.1 x)‖ := by
      intro γ
      rw [norm_mul, norm_inv, OntoE.chi_norm X la γ.2, inv_one, one_mul]
    have h1 : ‖poin X la P x‖ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ :=
      norm_tsum_le_tsum_norm (hsum x hx)
    have h2 := ofReal_tsum_sq_le_tsum_div_mul_tsum _ (fun γ : X.Γ => κ (lact γ.1 x)) (hsum x hx)
      fun γ => (hκp _ (hγx γ)).1
    have h3 : ∑' γ : X.Γ, ENNReal.ofReal (κ (lact γ.1 x)) ≤ C := by
      refine le_trans (ENNReal.tsum_le_tsum fun γ => ENNReal.ofReal_le_ofReal ?_) (hκC x hx)
      obtain ⟨h0, h1⟩ := hκp _ (hγx γ)
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith
    have h4 : ∑' γ : X.Γ, ψ (lact γ.1 x) =
        (∑' γ : X.Γ, ENNReal.ofReal (‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ ^ 2 / κ (lact γ.1 x))) *
          W x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [hψd _ (hγx γ), hn, hW.2.2 γ.1 γ.2 x hx]
    rw [h4, ← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    calc ENNReal.ofReal (‖poin X la P x‖ ^ 2)
        ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)
      _ ≤ _ := h2
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul' h3 le_rfl
  unfold InFF
  calc _ ≤ ∫⁻ z in FF, C * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 fun z hz => hpt _ (hFF.2.1 hz)
    _ = C * ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 :=
        lintegral_const_mul' _ _ hC.ne
    _ < ⊤ := ENNReal.mul_lt_top hC hfin

end GlobalTheory
