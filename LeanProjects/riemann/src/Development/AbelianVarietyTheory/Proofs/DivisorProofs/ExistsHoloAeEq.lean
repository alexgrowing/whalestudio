import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeak
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeak
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2LimitHolomorphic

open Set

variable {n : ℕ}

theorem exists_pos_le_on_compact {W K : Set (V n)} {ρ : V n → ℝ} (hρ : ContinuousOn ρ W)
    (hpos : ∀ v ∈ W, 0 < ρ v) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ ρ v := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hρ.mono hKW)
  exact ⟨ρ x, hpos x (hKW hx), fun v hv => hmin hv⟩

theorem lintegral_sq_le {W K : Set (V n)} {ρ : V n → ℝ} {c : ℝ} (hc : 0 < c)
    (hK : MeasurableSet K) (hKW : K ⊆ W) (hcK : ∀ v ∈ K, c ≤ ρ v) (g : V n → ℂ) :
    ∫⁻ v in K, ‖g v‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in W, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
  calc ∫⁻ v in K, ‖g v‖ₑ ^ 2
      ≤ ∫⁻ v in K, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
        apply setLIntegral_mono' hK
        intro v hv
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ c⁻¹ * ρ v := by
          rw [le_inv_mul_iff₀ hc]; simpa using hcK v hv
        have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖g v‖)
        nlinarith
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ v in K, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr

theorem integrableOn_of_limit {W K : Set (V n)} {ρ : V n → ℝ} {u : ℕ → V n → ℂ}
    {f : V n → ℂ} (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v)
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    (hK : IsCompact K) (hKW : K ⊆ W) : IntegrableOn f K := by
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_on_compact hρ hpos hK hKW
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hum : IntegrableOn (u m) K := ((hu m).continuousOn.mono hKW).integrableOn_compact hK
  have hfK : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.mono_measure (Measure.restrict_mono hKW le_rfl)).aestronglyMeasurable
  have hfin : ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_sq_le hc hK.measurableSet hKW hcK (fun v => f v - u m v))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm.trans ENNReal.one_lt_top))
  have hd : IntegrableOn (fun v => f v - u m v) K := by
    refine ⟨hfK.sub hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ v in K, ‖f v - u m v‖ₑ < ⊤
    have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
      intro x
      rcases le_total x 1 with h | h
      · exact h.trans le_self_add
      · calc x = x * 1 := (mul_one x).symm
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := (sq x).symm
          _ ≤ 1 + x ^ 2 := le_add_self
    calc ∫⁻ v in K, ‖f v - u m v‖ₑ ≤ ∫⁻ v in K, (1 + ‖f v - u m v‖ₑ ^ 2) :=
          lintegral_mono fun v => hpt _
      _ = volume K + ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hfin⟩
  exact (hd.add hum).congr_fun (fun v _ => by simp) hK.measurableSet

theorem enorm_integral_mul_le {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {d h : V n → ℂ}
    (hd : AEMeasurable d (volume.restrict W)) (hh : Continuous h) :
    ‖∫ v in W, d v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
  have hρm : AEMeasurable ρ (volume.restrict W) := hρ.aemeasurable hW.measurableSet
  have hsq : AEMeasurable (fun v => Real.sqrt (ρ v)) (volume.restrict W) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hρm
  have ham : AEMeasurable (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)))
      (volume.restrict W) := (hd.norm.mul hsq).ennreal_ofReal
  have hbm : AEMeasurable (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)))
      (volume.restrict W) := (hh.measurable.norm.aemeasurable.div hsq).ennreal_ofReal
  have hab : EqOn (fun v => ‖d v * h v‖ₑ)
      ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
        fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) W := by
    intro v hv
    have hs : 0 < Real.sqrt (ρ v) := Real.sqrt_pos.2 (hpos v hv)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_mul]
    congr 1
    field_simp
  have ha2 : EqOn (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      Real.sq_sqrt (hpos v hv).le]
  have hb2 : EqOn (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, div_pow,
      Real.sq_sqrt (hpos v hv).le]
  calc ‖∫ v in W, d v * h v‖ₑ ≤ ∫⁻ v in W, ‖d v * h v‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ v in W, ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
          fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) v :=
        setLIntegral_congr_fun hW.measurableSet hab
    _ ≤ (∫⁻ v in W, ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ v in W, ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two ham hbm
    _ = _ := by
        rw [setLIntegral_congr_fun hW.measurableSet ha2,
          setLIntegral_congr_fun hW.measurableSet hb2]

theorem integral_mul_eq_zero {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {u : ℕ → V n → ℂ} {f : V n → ℂ}
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    {h : V n → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h) (hsupp : tsupport h ⊆ W)
    (h0 : ∀ m, ∫ v in W, u m v * h v = 0) : ∫ v in W, f v * h v = 0 := by
  have hkc : Continuous fun v => ‖h v‖ ^ 2 / ρ v := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hhc.norm.pow 2).continuousAt.div (hρ.continuousAt (hW.mem_nhds hx))
        (hpos x hx).ne'
    · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
      have hev : (fun v => ‖h v‖ ^ 2 / ρ v) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with v hv
        simp [hv]
      exact continuousAt_const.congr hev.symm
  have hks : HasCompactSupport fun v => ‖h v‖ ^ 2 / ρ v := by
    refine hhs.mono fun x hx => ?_
    intro h1
    apply hx
    simp [h1]
  have hH : ∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (hkc.integrable_of_hasCompactSupport hks).lintegral_lt_top
  by_cases hfi : Integrable (fun v => f v * h v) (volume.restrict W)
  swap
  · exact integral_undef hfi
  have key : ∀ m, ‖∫ v in W, f v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
    intro m
    have hUi : Integrable (fun v => u m v * h v) (volume.restrict W) := by
      have h1 : IntegrableOn (fun v => u m v * h v) (tsupport h) :=
        (((hu m).continuousOn.mono hsupp).mul hhc.continuousOn).integrableOn_compact hhs
      exact h1.of_forall_sdiff_eq_zero hW.measurableSet fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2]
    have heq : ∫ v in W, f v * h v = ∫ v in W, (f v - u m v) * h v := by
      simp_rw [sub_mul]
      rw [integral_sub hfi hUi, h0 m, sub_zero]
    rw [heq]
    exact enorm_integral_mul_le hW hρ hpos
      (hf.sub ((hu m).continuousOn.aemeasurable hW.measurableSet)) hhc
  have hT : Tendsto (fun m =>
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m =>
        (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1
      (b := (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hH.ne))
    simpa using this
  have hle := ge_of_tendsto' hT key
  exact enorm_eq_zero.mp (le_antisymm hle bot_le)

theorem tsupport_dbarDir_subset (g : V n → ℂ) (w : V n) :
    tsupport (fun z => C.dbarDir g z w) ⊆ tsupport g := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  refine Function.mem_support.2 fun h0 => Function.mem_support.1 hz ?_
  simp [C.dbarDir, h0]

theorem exists_holo_ae_eq : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  intro n W ρ u f hW hρ hpos hu hf hlim
  have hwh : C.WeakHolo W f := by
    refine ⟨(locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK =>
      integrableOn_of_limit hρ hpos hu hf hlim hK hKW, ?_⟩
    intro g hg w
    obtain ⟨hhc, hhs⟩ := C.dbarDir_continuous_hasCompactSupport hg.1 hg.2.1 w
    exact integral_mul_eq_zero hW hρ hpos hu hf hlim hhc hhs
      ((tsupport_dbarDir_subset g w).trans hg.2.2)
      (fun m => (C.holoWeak n W (u m) hW (hu m)).2 g hg w)
  obtain ⟨U, hU, hfU⟩ := C.reg n W f hW hwh
  exact ⟨U, hU, hfU.symm⟩

end GlobalTheory.L2LimitHolomorphic
