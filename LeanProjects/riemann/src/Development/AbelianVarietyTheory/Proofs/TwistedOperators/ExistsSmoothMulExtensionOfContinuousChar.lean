import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff

namespace GlobalTheory

open MeasureTheory Filter Topology in

theorem contDiff_of_continuous_of_map_add_eq_mul {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (f : E → ℂ) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 ≠ 0) : ContDiff ℝ ∞ f := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht := ContDiffBump.convolution_tendsto_right_of_continuous (μ := μ) hb hf 0
  obtain ⟨n, hn⟩ := (ht.eventually_ne h0).exists
  have hs : ContDiff ℝ ∞
      (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ) :=
    HasCompactSupport.contDiff_convolution_left _ (b n).hasCompactSupport_normed
      (b n).contDiff_normed hf.locallyIntegrable
  have key : ∀ x, convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      = f x * convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0 := by
    intro x
    rw [convolution_def, convolution_def, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have : x - t = x + (0 - t) := by abel
    simp only [ContinuousLinearMap.lsmul_apply]
    rw [this, hadd, mul_smul_comm]
  have : f = fun x => convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ x
      * (convolution ((b n).normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ 0)⁻¹ := by
    funext x
    rw [key x, mul_inv_cancel_right₀ hn]
  rw [this]
  exact hs.mul contDiff_const

noncomputable def mixedExpUnit (K : Type) [Field K] (y : mixedSpace K) : (mixedSpace K)ˣ :=
  ⟨(fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w)),
    (fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w)),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add]),
    Prod.ext (funext fun w => by simp [← Real.exp_add])
      (funext fun w => by simp [← Complex.exp_add])⟩

theorem mixedExpUnit_add (K : Type) [Field K] (x y : mixedSpace K) :
    mixedExpUnit K (x + y) = mixedExpUnit K x * mixedExpUnit K y :=
  Units.ext (Prod.ext (funext fun w => Real.exp_add (x.1 w) (y.1 w))
    (funext fun w => Complex.exp_add (x.2 w) (y.2 w)))

theorem continuous_mixedExpUnit (K : Type) [Field K] : Continuous (mixedExpUnit K) := by
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (y.1 w), fun w => Complex.exp (y.2 w))) : mixedSpace K)
    fun_prop
  · show Continuous fun y : mixedSpace K =>
      (((fun w => Real.exp (-y.1 w), fun w => Complex.exp (-y.2 w))) : mixedSpace K)
    fun_prop

noncomputable def mixedLog (K : Type) [Field K] (x : mixedSpace K) : mixedSpace K :=
  (fun w => Real.log (x.1 w), fun w => Complex.log (x.2 w))

theorem contDiffAt_mixedLog_one (K : Type) [Field K] [NumberField K] :
    ContDiffAt ℝ ∞ (mixedLog K) 1 := by
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.1 w) :=
      (contDiff_apply ℝ ℝ w).comp contDiff_fst
    exact h1.contDiffAt.log (by simp)
  · have h1 : ContDiff ℝ ∞ (fun x : mixedSpace K => x.2 w) :=
      (contDiff_apply ℝ ℂ w).comp contDiff_snd
    have h2 : ContDiffAt ℝ ∞ Complex.log ((1 : mixedSpace K).2 w) :=
      (Complex.contDiffAt_log (by simp)).restrict_scalars ℝ
    exact h2.comp 1 h1.contDiffAt

open Filter Topology in
theorem eventually_mixedExpUnit_mixedLog (K : Type) [Field K] [NumberField K] :
    ∀ᶠ x in 𝓝 (1 : mixedSpace K), (mixedExpUnit K (mixedLog K x) : mixedSpace K) = x := by
  have h1 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, 0 < x.1 w := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.1 w) := by fun_prop
    exact hc.continuousAt.eventually (lt_mem_nhds (by simp))
  have h2 : ∀ᶠ x in 𝓝 (1 : mixedSpace K), ∀ w, x.2 w ≠ 0 := by
    refine eventually_all.mpr fun w => ?_
    have hc : Continuous (fun x : mixedSpace K => x.2 w) := by fun_prop
    exact hc.continuousAt.eventually_ne (by simp)
  filter_upwards [h1, h2] with x hx1 hx2
  exact Prod.ext (funext fun w => Real.exp_log (hx1 w)) (funext fun w => Complex.exp_log (hx2 w))

theorem mixedSpace_norm_ne_zero_iff_isUnit (K : Type) [Field K] [NumberField K]
    (x : mixedSpace K) : mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  rw [mixedEmbedding.norm_ne_zero_iff, Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  constructor
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · have := h w.1
      rw [normAtPlace_apply_of_isReal w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
    · have := h w.1
      rw [normAtPlace_apply_of_isComplex w.2] at this
      exact (norm_ne_zero_iff.mp this).isUnit
  · rintro ⟨h1, h2⟩ w
    rcases w.isReal_or_isComplex with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]
      exact norm_ne_zero_iff.mpr (h1 _).ne_zero
    · rw [normAtPlace_apply_of_isComplex hw]
      exact norm_ne_zero_iff.mpr (h2 _).ne_zero

theorem exists_smooth_mul_extension_of_continuous_char :
    ∀ (K : Type) [Field K] [NumberField K] (ψ : (mixedSpace K)ˣ →* ℂˣ), Continuous ψ → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ)) ∧ ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 ↔ IsUnit x := by
  intro K _ _ ψ hψ
  let φ : mixedSpace K → ℂ := fun x => if h : IsUnit x then (ψ h.unit : ℂ) else 0
  have hu : ∀ u : (mixedSpace K)ˣ, φ u = (ψ u : ℂ) := by
    intro u
    simp only [φ, dif_pos u.isUnit, IsUnit.unit_of_val_units]
  have hn : ∀ x, ¬ IsUnit x → φ x = 0 := fun x hx => dif_neg hx
  have hmul : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    by_cases hx : IsUnit x
    · by_cases hy : IsUnit y
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [← Units.val_mul, hu, hu, hu, map_mul, Units.val_mul]
      · rw [hn y hy, hn _ (fun h => hy (isUnit_of_mul_isUnit_right h)), mul_zero]
    · rw [hn x hx, hn _ (fun h => hx (isUnit_of_mul_isUnit_left h)), zero_mul]
  have hf : ContDiff ℝ ∞ (fun y => (ψ (mixedExpUnit K y) : ℂ)) :=
    contDiff_of_continuous_of_map_add_eq_mul _
      (Units.continuous_val.comp (hψ.comp (continuous_mixedExpUnit K)))
      (fun x y => by rw [mixedExpUnit_add, map_mul, Units.val_mul]) (Units.ne_zero _)
  have h1 : ContDiffAt ℝ ∞ φ 1 := by
    refine (hf.contDiffAt.comp 1 (contDiffAt_mixedLog_one K)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_mixedExpUnit_mixedLog K] with x hx
    rw [Function.comp_apply, ← hu, hx]
  refine ⟨φ, hmul, fun x hx => ?_, hu, mixedSpace_norm_ne_zero_iff_isUnit K⟩
  obtain ⟨u, rfl⟩ := (mixedSpace_norm_ne_zero_iff_isUnit K x).mp hx
  have h2 : φ = fun z => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z) := by
    funext z
    rw [← hmul, Units.mul_inv_cancel_left]
  have h3 : ContDiffAt ℝ ∞ φ (((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * u) := by
    rw [Units.inv_mul]
    exact h1
  have h4 : ContDiffAt ℝ ∞
      (fun z : mixedSpace K => φ u * φ ((u⁻¹ : (mixedSpace K)ˣ) * z)) (u : mixedSpace K) :=
    contDiffAt_const.mul (h3.comp (u : mixedSpace K)
      (f := fun z : mixedSpace K => ((u⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) * z)
      (contDiffAt_const.mul contDiffAt_id))
  rw [← h2] at h4
  exact h4.contDiffWithinAt

end GlobalTheory
