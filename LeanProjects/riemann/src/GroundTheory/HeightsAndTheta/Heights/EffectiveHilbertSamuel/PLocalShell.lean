import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsLocalShell
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShellPolar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology

noncomputable section

theorem localShell_tendsto_of_param_sandwich {α : Type*} {l : Filter α} {I : α → ENNReal}
    {lo hi : ℝ → ENNReal} {L : ENNReal} (hlo : Tendsto lo (𝓝[>] 0) (𝓝 L))
    (hhi : Tendsto hi (𝓝[>] 0) (𝓝 L))
    (h : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ᶠ x in l, lo τ ≤ I x ∧ I x ≤ hi τ) : Tendsto I l (𝓝 L) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨τ, hτ1, hτ2⟩ := ((hlo.eventually (lt_mem_nhds ha)).and h).exists
    filter_upwards [hτ2] with x hx using lt_of_lt_of_le hτ1 hx.1
  · obtain ⟨τ, hτ1, hτ2⟩ := ((hhi.eventually (gt_mem_nhds ha)).and h).exists
    filter_upwards [hτ2] with x hx using lt_of_le_of_lt hx.2 hτ1

theorem localShell_lintegral_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {N : Set E} {f : E → E} {f' : E → E →L[ℝ] E} (hN : MeasurableSet N)
    (hf' : ∀ z ∈ N, HasFDerivWithinAt f (f' z) N z) (hf : InjOn f N) {j : ℝ} (hj : 0 < j)
    (hJ : ∀ z ∈ N, j ≤ |(f' z).det|) (g : E → ENNReal) :
    ∫⁻ z in N, g (f z) ∂μ ≤ ENNReal.ofReal j⁻¹ * ∫⁻ u in f '' N, g u ∂μ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hN hf' hf g]
  calc ∫⁻ z in N, g (f z) ∂μ
      = ENNReal.ofReal j⁻¹ * (ENNReal.ofReal j * ∫⁻ z in N, g (f z) ∂μ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hj.le), inv_mul_cancel₀ hj.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal j⁻¹ * ∫⁻ z in N, ENNReal.ofReal |(f' z).det| * g (f z) ∂μ := by
        gcongr
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact setLIntegral_mono' hN fun z hz => by gcongr; exact hJ z hz

theorem localShell_lintegral_image_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {N : Set E} {f : E → E} {f' : E → E →L[ℝ] E} (hN : MeasurableSet N)
    (hf' : ∀ z ∈ N, HasFDerivWithinAt f (f' z) N z) (hf : InjOn f N) {j : ℝ}
    (hJ : ∀ z ∈ N, |(f' z).det| ≤ j) (g : E → ENNReal) :
    ∫⁻ u in f '' N, g u ∂μ ≤ ENNReal.ofReal j * ∫⁻ z in N, g (f z) ∂μ := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hN hf' hf g,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono' hN fun z hz => by gcongr; exact hJ z hz

theorem localShell_det_restrictScalars {D : ℕ} (A : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) :
    |(A.restrictScalars ℝ).det| = ‖LinearMap.det (A : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 := by
  have : (A.restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (A : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
      LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [this, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

def localShellSq {D : ℕ} (u : Fin D → ℂ) : ℝ := ∑ i, ‖u i‖ ^ 2

theorem localShellSq_nonneg {D : ℕ} (u : Fin D → ℂ) : 0 ≤ localShellSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem localShell_norm_le_sqrt {D : ℕ} (u : Fin D → ℂ) : ‖u‖ ≤ Real.sqrt (localShellSq u) :=
  (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => by
    have h : ‖u i‖ ^ 2 ≤ localShellSq u :=
      Finset.single_le_sum (f := fun j => ‖u j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h

theorem localShell_pointwise_upper (D : ℕ) {F σ q ε F₀ σ₀ τ : ℝ} (hF : 0 ≤ F) (hF' : F ≤ F₀ + τ)
    (hσl : 0 < σ₀ - τ) (hσ1 : σ₀ - τ ≤ σ) (hσ2 : σ ≤ σ₀ + τ) (hq : 0 ≤ q) (hε : 0 < ε) :
    ENNReal.ofReal (F * ((q * σ) ^ D)⁻¹ * extShell ε (q * σ)) ≤
      ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹) *
        (Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ))).indicator
          (fun x => ENNReal.ofReal ((x ^ D)⁻¹)) q := by
  unfold extShell
  by_cases hs : q * σ ∈ Icc (ε ^ 2 / 2) (ε ^ 2)
  · have hσ : 0 < σ := lt_of_lt_of_le hσl hσ1
    have hε2 : 0 < ε ^ 2 := by positivity
    have hqσ : 0 < q * σ := lt_of_lt_of_le (by positivity) hs.1
    have hq0 : 0 < q := pos_of_mul_pos_left hqσ hσ.le
    have hm : q ∈ Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ)) := by
      constructor
      · rw [div_le_iff₀ (by linarith)]
        nlinarith [hs.1]
      · rw [le_div_iff₀ hσl]
        nlinarith [hs.2]
    rw [indicator_of_mem hs, indicator_of_mem hm, Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul' (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow, mul_inv, mul_comm ((q ^ D)⁻¹), ← mul_assoc]
    have h1 : (σ ^ D)⁻¹ ≤ ((σ₀ - τ) ^ D)⁻¹ :=
      inv_anti₀ (pow_pos hσl D) (pow_le_pow_left₀ hσl.le hσ1 D)
    have h2 : F * (σ ^ D)⁻¹ ≤ (F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹ :=
      mul_le_mul hF' h1 (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · rw [indicator_of_notMem hs, mul_zero, ENNReal.ofReal_zero]
    simp

theorem localShell_pointwise_lower (D : ℕ) {F σ q ε F₀ σ₀ τ : ℝ} (hF : 0 ≤ F) (hF' : F₀ - τ ≤ F)
    (hσl : 0 < σ₀ - τ) (hσ1 : σ₀ - τ ≤ σ) (hσ2 : σ ≤ σ₀ + τ) (hε : 0 < ε) :
    ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹) *
        (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator
          (fun x => ENNReal.ofReal ((x ^ D)⁻¹)) q ≤
      ENNReal.ofReal (F * ((q * σ) ^ D)⁻¹ * extShell ε (q * σ)) := by
  unfold extShell
  by_cases hm : q ∈ Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))
  · have hσ : 0 < σ := lt_of_lt_of_le hσl hσ1
    have hq0 : 0 < q := lt_of_lt_of_le (div_pos (by positivity) (by linarith)) hm.1
    have hs : q * σ ∈ Icc (ε ^ 2 / 2) (ε ^ 2) := by
      have h1 := hm.1
      have h2 := hm.2
      rw [div_le_iff₀ (by linarith)] at h1
      rw [le_div_iff₀ (by linarith)] at h2
      constructor <;> nlinarith
    rw [indicator_of_mem hs, indicator_of_mem hm, Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul' (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_pow, mul_inv, mul_comm ((q ^ D)⁻¹), ← mul_assoc]
    have h1 : ((σ₀ + τ) ^ D)⁻¹ ≤ (σ ^ D)⁻¹ :=
      inv_anti₀ (pow_pos hσ D) (pow_le_pow_left₀ hσ.le hσ2 D)
    have h2 : (F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ ≤ F * (σ ^ D)⁻¹ :=
      (mul_le_mul_of_nonneg_right hF' (inv_nonneg.2 (pow_nonneg (by linarith) D))).trans (mul_le_mul_of_nonneg_left h1 hF)
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · rw [indicator_of_notMem hm, mul_zero]
    simp

theorem localShell_round (hP : ShellPolar.Statement) {D : ℕ} (hD : 1 ≤ D) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ∫⁻ u : Fin D → ℂ, (Icc a b).indicator (fun x => ENNReal.ofReal ((x ^ D)⁻¹)) (localShellSq u) =
      ENNReal.ofReal (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (b / a)) := by
  have hc : Continuous (fun u : Fin D → ℂ => localShellSq u) :=
    continuous_finsetSum _ fun i _ => (continuous_norm.comp (continuous_apply i)).pow 2
  have hmeas : MeasurableSet ((fun u : Fin D → ℂ => localShellSq u) ⁻¹' Icc a b) :=
    measurableSet_Icc.preimage hc.measurable
  rw [← hP D hD a b ha hab, ← lintegral_indicator (show MeasurableSet
    {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b} from hmeas)]
  exact lintegral_congr fun u => by
    simp only [Set.indicator_apply, localShellSq, Set.mem_Icc, Set.mem_ofPred_eq]

theorem localShell_bounds_on_ball (hP : ShellPolar.Statement) {D : ℕ} (hD : 1 ≤ D)
    {V : Set (Fin D → ℂ)} {z₀ : Fin D → ℂ} {w : (Fin D → ℂ) → Fin D → ℂ}
    {F σ : (Fin D → ℂ) → ℝ} {r ρ η τ ε F₀ σ₀ J₀ : ℝ} (hV : MeasurableSet V)
    (hNV : Metric.ball z₀ r ⊆ V) (hinj : InjOn w (Metric.ball z₀ r))
    (hder : ∀ z ∈ Metric.ball z₀ r, HasFDerivAt w (fderiv ℂ w z) z)
    (hρ : 0 < ρ) (hρN : Metric.ball 0 ρ ⊆ w '' Metric.ball z₀ r)
    (hF0 : ∀ z ∈ V, 0 ≤ F z)
    (hFb : ∀ z ∈ Metric.ball z₀ r, F₀ - τ ≤ F z ∧ F z ≤ F₀ + τ)
    (hσb : ∀ z ∈ Metric.ball z₀ r, σ₀ - τ ≤ σ z ∧ σ z ≤ σ₀ + τ)
    (hJb : ∀ z ∈ Metric.ball z₀ r,
      J₀ - τ ≤ ‖LinearMap.det (fderiv ℂ w z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 ∧
      ‖LinearMap.det (fderiv ℂ w z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 ≤ J₀ + τ)
    (hη : ∀ z ∈ V, r ≤ dist z z₀ → η ≤ localShellSq (w z) * σ z)
    (hτ : 0 < τ) (hτσ : 3 * τ < σ₀) (hτJ : τ < J₀)
    (hε : 0 < ε) (hεη : ε ^ 2 < η) (hερ : ε ^ 2 < ρ ^ 2 * (σ₀ + τ)) :
    ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
        (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ)))) ≤
      ∫⁻ z in V, ENNReal.ofReal (F z * ((localShellSq (w z) * σ z) ^ D)⁻¹ *
        extShell ε (localShellSq (w z) * σ z)) ∧
    ∫⁻ z in V, ENNReal.ofReal (F z * ((localShellSq (w z) * σ z) ^ D)⁻¹ *
        extShell ε (localShellSq (w z) * σ z)) ≤
      ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹ * (J₀ - τ)⁻¹ *
        (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ + τ) / (σ₀ - τ)))) := by
  have hNm : MeasurableSet (Metric.ball z₀ r) := measurableSet_ball
  have hf' : ∀ z ∈ Metric.ball z₀ r, HasFDerivWithinAt w ((fderiv ℂ w z).restrictScalars ℝ)
      (Metric.ball z₀ r) z := fun z hz => ((hder z hz).restrictScalars ℝ).hasFDerivWithinAt
  have hJdet : ∀ z, |((fderiv ℂ w z).restrictScalars ℝ).det| =
      ‖LinearMap.det (fderiv ℂ w z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 :=
    fun z => localShell_det_restrictScalars _
  have hC0 : 0 ≤ Real.pi ^ D / ((D - 1).factorial : ℝ) := by positivity
  have hσm : 0 < σ₀ - τ := by linarith
  have hσp : 0 < σ₀ + τ := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  set G : (Fin D → ℂ) → ENNReal := fun z => ENNReal.ofReal (F z * ((localShellSq (w z) * σ z) ^ D)⁻¹ *
    extShell ε (localShellSq (w z) * σ z)) with hG
  set k : ℝ → ENNReal := fun x => ENNReal.ofReal ((x ^ D)⁻¹) with hk

  have hIN : ∫⁻ z in V, G z = ∫⁻ z in Metric.ball z₀ r, G z := by
    have hEq : EqOn G ((Metric.ball z₀ r).indicator G) V := fun z hz => by
      by_cases hzN : z ∈ Metric.ball z₀ r
      · rw [indicator_of_mem hzN]
      · rw [indicator_of_notMem hzN]
        have hd : r ≤ dist z z₀ := not_lt.1 hzN
        have ht := hη z hz hd
        simp only [hG, extShell]
        rw [indicator_of_notMem (fun h => by linarith [h.2]), mul_zero, ENNReal.ofReal_zero]
    rw [setLIntegral_congr_fun hV hEq, lintegral_indicator hNm, Measure.restrict_restrict hNm,
      inter_eq_left.2 hNV]

  have hup : ∫⁻ z in Metric.ball z₀ r, G z ≤
      ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹ * (J₀ - τ)⁻¹ *
        (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ + τ) / (σ₀ - τ)))) := by
    have hah : 0 < ε ^ 2 / (2 * (σ₀ + τ)) := div_pos hε2 (by linarith)
    have habh : ε ^ 2 / (2 * (σ₀ + τ)) ≤ ε ^ 2 / (σ₀ - τ) :=
      div_le_div_of_nonneg_left hε2.le hσm (by linarith)
    have hratio : ε ^ 2 / (σ₀ - τ) / (ε ^ 2 / (2 * (σ₀ + τ))) = 2 * (σ₀ + τ) / (σ₀ - τ) := by
      field_simp
    have hX : 0 ≤ Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ + τ) / (σ₀ - τ)) :=
      mul_nonneg hC0 (Real.log_nonneg ((one_le_div hσm).2 (by linarith)))
    have hB : 0 ≤ (J₀ - τ)⁻¹ := inv_nonneg.2 (by linarith)
    calc ∫⁻ z in Metric.ball z₀ r, G z
        ≤ ∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹) *
            (Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ))).indicator k (localShellSq (w z)) :=
          setLIntegral_mono' hNm fun z hz => localShell_pointwise_upper D (hF0 z (hNV hz))
            (hFb z hz).2 hσm (hσb z hz).1 (hσb z hz).2 (localShellSq_nonneg _) hε
      _ = ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹) * ∫⁻ z in Metric.ball z₀ r,
            (Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ))).indicator k (localShellSq (w z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹) * (ENNReal.ofReal (J₀ - τ)⁻¹ *
            ∫⁻ u in w '' Metric.ball z₀ r,
              (Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ))).indicator k (localShellSq u)) :=
          mul_le_mul_right (localShell_lintegral_comp_le volume hNm hf' hinj (by linarith)
            (fun z hz => by rw [hJdet]; exact (hJb z hz).1) _) _
      _ ≤ ENNReal.ofReal ((F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹) * (ENNReal.ofReal (J₀ - τ)⁻¹ *
            ∫⁻ u, (Icc (ε ^ 2 / (2 * (σ₀ + τ))) (ε ^ 2 / (σ₀ - τ))).indicator k (localShellSq u)) :=
          mul_le_mul_right (mul_le_mul_right (setLIntegral_le_lintegral _ _) _) _
      _ = _ := by
          rw [localShell_round hP hD hah habh, hratio,
            show (F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹ * (J₀ - τ)⁻¹ *
                (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ + τ) / (σ₀ - τ))) =
              (F₀ + τ) * ((σ₀ - τ) ^ D)⁻¹ * ((J₀ - τ)⁻¹ *
                (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ + τ) / (σ₀ - τ))))
              by ring, ENNReal.ofReal_mul' (mul_nonneg hB hX), ENNReal.ofReal_mul' hX]

  have hlo : ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
        (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ)))) ≤
      ∫⁻ z in Metric.ball z₀ r, G z := by
    have hal : 0 < ε ^ 2 / (2 * (σ₀ - τ)) := div_pos hε2 (by linarith)
    have habl : ε ^ 2 / (2 * (σ₀ - τ)) ≤ ε ^ 2 / (σ₀ + τ) :=
      div_le_div_of_nonneg_left hε2.le hσp (by linarith)
    have hratio : ε ^ 2 / (σ₀ + τ) / (ε ^ 2 / (2 * (σ₀ - τ))) = 2 * (σ₀ - τ) / (σ₀ + τ) := by
      field_simp
    have hY : 0 ≤ Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ)) :=
      mul_nonneg hC0 (Real.log_nonneg ((one_le_div hσp).2 (by linarith)))
    have hB : 0 ≤ (J₀ + τ)⁻¹ := inv_nonneg.2 (by linarith)
    have hsub : ∀ u : Fin D → ℂ,
        (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq u) ≠ 0 →
        u ∈ w '' Metric.ball z₀ r := fun u hu => by
      have hm : localShellSq u ∈ Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ)) := by
        by_contra h
        exact hu (indicator_of_notMem h _)
      have hb : ε ^ 2 / (σ₀ + τ) < ρ ^ 2 := (div_lt_iff₀ hσp).2 hερ
      apply hρN
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (localShell_norm_le_sqrt u)
        ((Real.sqrt_lt' hρ).2 (lt_of_le_of_lt hm.2 hb))
    have hW : ∫⁻ u in w '' Metric.ball z₀ r,
        (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq u) =
        ENNReal.ofReal (Real.pi ^ D / ((D - 1).factorial : ℝ) *
          Real.log (2 * (σ₀ - τ) / (σ₀ + τ))) := by
      rw [← hratio, ← localShell_round hP hD hal habl]
      exact setLIntegral_eq_of_support_subset fun u hu => hsub u hu
    have hJ : 0 < J₀ + τ := by linarith
    calc ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
          (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ))))
        = ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹) * (ENNReal.ofReal (J₀ + τ)⁻¹ *
            ∫⁻ u in w '' Metric.ball z₀ r,
              (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq u)) := by
          rw [hW, show (F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
                (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ))) =
              (F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹ * ((J₀ + τ)⁻¹ *
                (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (2 * (σ₀ - τ) / (σ₀ + τ))))
              by ring, ENNReal.ofReal_mul' (mul_nonneg hB hY), ENNReal.ofReal_mul' hY]
      _ ≤ ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹) * (ENNReal.ofReal (J₀ + τ)⁻¹ *
            (ENNReal.ofReal (J₀ + τ) * ∫⁻ z in Metric.ball z₀ r,
              (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq (w z)))) :=
          mul_le_mul_right (mul_le_mul_right (localShell_lintegral_image_le volume hNm hf' hinj
            (fun z hz => by rw [hJdet]; exact (hJb z hz).2) _) _) _
      _ = ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹) * ∫⁻ z in Metric.ball z₀ r,
              (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq (w z)) := by
          rw [← mul_assoc (ENNReal.ofReal (J₀ + τ)⁻¹), ← ENNReal.ofReal_mul hB,
            inv_mul_cancel₀ hJ.ne', ENNReal.ofReal_one, one_mul]
      _ = ∫⁻ z in Metric.ball z₀ r, ENNReal.ofReal ((F₀ - τ) * ((σ₀ + τ) ^ D)⁻¹) *
              (Icc (ε ^ 2 / (2 * (σ₀ - τ))) (ε ^ 2 / (σ₀ + τ))).indicator k (localShellSq (w z)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ z in Metric.ball z₀ r, G z :=
          setLIntegral_mono' hNm fun z hz => localShell_pointwise_lower D (hF0 z (hNV hz))
            (hFb z hz).1 hσm (hσb z hz).1 (hσb z hz).2 hε
  exact ⟨hlo.trans_eq hIN.symm, hIN.trans_le hup⟩

theorem LocalShell.proof (hP : ShellPolar.Statement) : LocalShell.Statement := by
  intro D hD V z₀ w F σ hV hz₀ hw hw0 hdet hF hF0 hσ hσ0 hlow
  have hVn : V ∈ 𝓝 z₀ := hV.mem_nhds hz₀
  have hs0 : 0 < σ z₀ := hσ0 z₀ hz₀
  have hJc : ContinuousAt
      (fun z => ‖LinearMap.det (fderiv ℂ w z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2) z₀ :=
    ((ContinuousLinearMap.continuous_det.continuousAt.comp
      (hw.fderiv z₀ hz₀).continuousAt).norm).pow 2
  have hJ0' : 0 < ‖LinearMap.det (fderiv ℂ w z₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 hdet) 2
  obtain ⟨J₀, hJ₀⟩ : ∃ J : ℝ,
      ‖LinearMap.det (fderiv ℂ w z₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 = J := ⟨_, rfl⟩
  rw [hJ₀]
  have hJ0 : 0 < J₀ := hJ₀ ▸ hJ0'
  set C := Real.pi ^ D / ((D - 1).factorial : ℝ) with hC

  have hstrict : HasStrictFDerivAt w
      ((fderiv ℂ w z₀).toContinuousLinearEquivOfDetNeZero hdet :
        (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) z₀ := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hw z₀ hz₀).hasStrictFDerivAt
  set Φ := hstrict.toOpenPartialHomeomorph w with hΦ
  have hSn : Φ.source ∈ 𝓝 z₀ := Φ.open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have hFc : ContinuousAt F z₀ := hF.continuousAt hVn
  have hσc : ContinuousAt σ z₀ := hσ.continuousAt hVn

  have hlim0 : F z₀ / σ z₀ ^ D / J₀ * C * Real.log 2 = (F z₀ - 0) * ((σ z₀ + 0) ^ D)⁻¹ *
      (J₀ + 0)⁻¹ * (C * Real.log (2 * (σ z₀ - 0) / (σ z₀ + 0))) := by
    rw [sub_zero, add_zero, add_zero, sub_zero, mul_div_assoc, div_self hs0.ne', mul_one]
    ring
  have hlim1 : F z₀ / σ z₀ ^ D / J₀ * C * Real.log 2 = (F z₀ + 0) * ((σ z₀ - 0) ^ D)⁻¹ *
      (J₀ - 0)⁻¹ * (C * Real.log (2 * (σ z₀ + 0) / (σ z₀ - 0))) := by
    rw [sub_zero, add_zero, sub_zero, add_zero, mul_div_assoc, div_self hs0.ne', mul_one]
    ring
  have e2 : 2 * σ z₀ / σ z₀ ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hs0.ne') hs0.ne'
  refine localShell_tendsto_of_param_sandwich
    (lo := fun τ => ENNReal.ofReal ((F z₀ - τ) * ((σ z₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
      (C * Real.log (2 * (σ z₀ - τ) / (σ z₀ + τ)))))
    (hi := fun τ => ENNReal.ofReal ((F z₀ + τ) * ((σ z₀ - τ) ^ D)⁻¹ * (J₀ - τ)⁻¹ *
      (C * Real.log (2 * (σ z₀ + τ) / (σ z₀ - τ))))) ?_ ?_ ?_
  · rw [hlim0]
    have e1 : σ z₀ + 0 ≠ 0 := by rw [add_zero]; exact hs0.ne'
    have e3 : J₀ + 0 ≠ 0 := by rw [add_zero]; exact hJ0.ne'
    have e4 : 2 * (σ z₀ - 0) / (σ z₀ + 0) ≠ 0 := by rw [sub_zero, add_zero]; exact e2
    have hc : ContinuousAt (fun τ : ℝ => (F z₀ - τ) * ((σ z₀ + τ) ^ D)⁻¹ * (J₀ + τ)⁻¹ *
        (C * Real.log (2 * (σ z₀ - τ) / (σ z₀ + τ)))) 0 := by
      apply ContinuousAt.mul
      · apply ContinuousAt.mul
        · apply ContinuousAt.mul
          · fun_prop
          · exact ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero _ e1)
        · exact ContinuousAt.inv₀ (by fun_prop) e3
      · apply ContinuousAt.mul continuousAt_const
        exact ContinuousAt.log (ContinuousAt.div (by fun_prop) (by fun_prop) e1) e4
    exact ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto)
  · rw [hlim1]
    have e1 : σ z₀ - 0 ≠ 0 := by rw [sub_zero]; exact hs0.ne'
    have e3 : J₀ - 0 ≠ 0 := by rw [sub_zero]; exact hJ0.ne'
    have e4 : 2 * (σ z₀ + 0) / (σ z₀ - 0) ≠ 0 := by rw [sub_zero, add_zero]; exact e2
    have hc : ContinuousAt (fun τ : ℝ => (F z₀ + τ) * ((σ z₀ - τ) ^ D)⁻¹ * (J₀ - τ)⁻¹ *
        (C * Real.log (2 * (σ z₀ + τ) / (σ z₀ - τ)))) 0 := by
      apply ContinuousAt.mul
      · apply ContinuousAt.mul
        · apply ContinuousAt.mul
          · fun_prop
          · exact ContinuousAt.inv₀ (by fun_prop) (pow_ne_zero _ e1)
        · exact ContinuousAt.inv₀ (by fun_prop) e3
      · apply ContinuousAt.mul continuousAt_const
        exact ContinuousAt.log (ContinuousAt.div (by fun_prop) (by fun_prop) e1) e4
    exact ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto)

  · have hm : (0 : ℝ) < min (σ z₀ / 3) J₀ := lt_min (by positivity) hJ0
    filter_upwards [Ioo_mem_nhdsGT hm] with τ hτ
    have hτ0 : 0 < τ := hτ.1
    have hτσ : 3 * τ < σ z₀ := by
      have := lt_of_lt_of_le hτ.2 (min_le_left _ _)
      linarith
    have hτJ : τ < J₀ := lt_of_lt_of_le hτ.2 (min_le_right _ _)
    have hev : ∀ᶠ z in 𝓝 z₀, z ∈ V ∧ z ∈ Φ.source ∧ F z ∈ Ioo (F z₀ - τ) (F z₀ + τ) ∧
        σ z ∈ Ioo (σ z₀ - τ) (σ z₀ + τ) ∧
        ‖LinearMap.det (fderiv ℂ w z : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 ∈
          Ioo (J₀ - τ) (J₀ + τ) :=
      Filter.Eventually.and (show ∀ᶠ z in 𝓝 z₀, z ∈ V from hVn)
        (Filter.Eventually.and (show ∀ᶠ z in 𝓝 z₀, z ∈ Φ.source from hSn)
          ((hFc.eventually (Ioo_mem_nhds (by linarith) (by linarith))).and
            ((hσc.eventually (Ioo_mem_nhds (by linarith) (by linarith))).and
              (hJc.eventually (Ioo_mem_nhds (by beta_reduce; rw [hJ₀]; linarith)
                (by beta_reduce; rw [hJ₀]; linarith))))))
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    have hNV : Metric.ball z₀ r ⊆ V := fun z hz => (hball z hz).1
    have hNS : Metric.ball z₀ r ⊆ Φ.source := fun z hz => (hball z hz).2.1
    have hinj : InjOn w (Metric.ball z₀ r) := Φ.injOn.mono hNS
    have hopen : IsOpen (w '' Metric.ball z₀ r) :=
      Φ.isOpen_image_of_subset_source Metric.isOpen_ball hNS
    have h0 : (0 : Fin D → ℂ) ∈ w '' Metric.ball z₀ r := ⟨z₀, Metric.mem_ball_self hr, hw0⟩
    obtain ⟨ρ, hρ, hρN⟩ := Metric.isOpen_iff.1 hopen 0 h0
    obtain ⟨η, hη, hηV⟩ := hlow r hr
    have hm2 : 0 < min η (ρ ^ 2 * (σ z₀ + τ)) := lt_min hη (mul_pos (by positivity) (by linarith))
    have hsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds ((continuous_pow 2).tendsto' (0 : ℝ) 0 (by norm_num))
    filter_upwards [self_mem_nhdsWithin, hsq.eventually (gt_mem_nhds hm2)] with ε hε hε2
    exact localShell_bounds_on_ball hP hD hV.measurableSet hNV hinj
      (fun z hz => (hw z (hNV hz)).differentiableAt.hasFDerivAt) hρ hρN hF0
      (fun z hz => ⟨(hball z hz).2.2.1.1.le, (hball z hz).2.2.1.2.le⟩)
      (fun z hz => ⟨(hball z hz).2.2.2.1.1.le, (hball z hz).2.2.2.1.2.le⟩)
      (fun z hz => ⟨(hball z hz).2.2.2.2.1.le, (hball z hz).2.2.2.2.2.le⟩)
      (fun z hz hd => hηV z hz hd) hτ0 hτσ hτJ hε (lt_of_lt_of_le hε2 (min_le_left _ _))
      (lt_of_lt_of_le hε2 (min_le_right _ _))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
