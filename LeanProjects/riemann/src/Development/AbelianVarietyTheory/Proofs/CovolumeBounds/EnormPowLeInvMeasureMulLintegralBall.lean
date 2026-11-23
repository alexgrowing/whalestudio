import Mathlib

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace GlobalTheory

section Circle

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem enorm_pow_mul_le_lintegral_circle {f : ℂ → H} (hf : DiffContOnCl ℂ f (ball 0 1)) (n : ℕ) :
    ‖f 0‖ₑ ^ n * ENNReal.ofReal (2 * π) ≤
      ∫⁻ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ₑ ^ n := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hc : Continuous fun t => f (circleMap 0 1 t) := by
    refine hf.continuousOn.comp_continuous (continuous_circleMap 0 1) fun t => ?_
    rw [closure_ball _ one_ne_zero]
    exact sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one t)
  have hav : ⨍ t in Ioc 0 (2 * π), f (circleMap 0 1 t) = f 0 := by
    have h := DiffContOnCl.circleAverage (f := f) (c := 0) (R := 1) (by simpa using hf)
    rw [← h, Real.circleAverage, intervalIntegral.integral_of_le h2.le, setAverage_eq]
    simp [h2.le]
  have hg : ConvexOn ℝ univ fun x : H => ‖x‖ ^ n :=
    (convexOn_univ_norm (E := H)).pow (fun x _ => norm_nonneg x) n
  have hi : IntegrableOn (fun t => ‖f (circleMap 0 1 t)‖ ^ n) (Ioc 0 (2 * π)) :=
    (hc.norm.pow n).integrableOn_Ioc
  have hJ := hg.map_set_average_le (μ := volume) (t := Ioc 0 (2 * π))
    (f := fun t => f (circleMap 0 1 t)) (by fun_prop) isClosed_univ (by simp [Real.pi_pos])
    measure_Ioc_lt_top.ne (by simp) hc.integrableOn_Ioc hi
  rw [hav, setAverage_eq] at hJ
  simp only [Real.volume_real_Ioc, sub_zero, max_eq_left h2.le, smul_eq_mul] at hJ
  rw [le_inv_mul_iff₀ h2] at hJ
  have hl : ∫⁻ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ₑ ^ n =
      ENNReal.ofReal (∫ t in Ioc 0 (2 * π), ‖f (circleMap 0 1 t)‖ ^ n) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun t => by positivity)]
    simp [ENNReal.ofReal_pow]
  rw [hl, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), mul_comm]
  exact ENNReal.ofReal_le_ofReal hJ

end Circle

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E]

theorem measurePreserving_smul_of_norm_eq_one (μ : Measure E) [μ.IsAddHaarMeasure] {c : ℂ}
    (hc : ‖c‖ = 1) : MeasurePreserving (fun z : E => c • z) μ μ := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hm : Measurable fun z : E => c • z := (continuous_const_smul c).measurable
  let e : E ≃L[ℂ] E := (LinearEquiv.smulOfNeZero ℂ E c hc0).toContinuousLinearEquiv
  have hH : (μ.map fun z : E => c • z).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have h := Measure.isAddLeftInvariant_eq_smul (μ.map fun z : E => c • z) μ
  have hb : (μ.map fun z : E => c • z) (ball 0 1) = μ (ball 0 1) := by
    rw [Measure.map_apply hm measurableSet_ball]
    congr 1
    ext z
    simp [norm_smul, hc]
  have h0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have ht : μ (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨hm, ?_⟩
  have h1 : Measure.addHaarScalarFactor (μ.map fun z : E => c • z) μ = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
    exact_mod_cast (ENNReal.mul_eq_right h0 ht).1 hb
  rw [h, h1, one_smul]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem enorm_pow_mul_lintegral_le_of_circular (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : MeasurableSet S) (hSc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, c • z ∈ S) {φ : E → H}
    (hφc : ContinuousOn φ S) (hφ : ∀ z ∈ S, DiffContOnCl ℂ (fun c : ℂ => φ (c • z)) (ball 0 1))
    {w : E → ℝ≥0∞} (hw : Measurable w) (hwc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, w (c • z) = w z)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in S, w z ∂μ ≤ ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := by
  classical
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hn : ∀ t, ‖circleMap 0 1 t‖ = 1 := fun t => by simp
  set g : E → ℝ≥0∞ := S.indicator fun z => ‖φ z‖ₑ ^ n * w z with hg
  have hgm : Measurable g := by
    have h1 : ContinuousOn (fun z => ‖φ z‖ₑ ^ n) S :=
      (ENNReal.continuous_pow n).comp_continuousOn hφc.enorm
    have h3 := (h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS).mul hw
    convert h3 using 1
    ext z
    by_cases hz : z ∈ S <;> simp [hg, hz]
  have hj : Measurable fun p : ℝ × E => g (circleMap 0 1 p.1 • p.2) := by
    refine hgm.comp (Continuous.measurable ?_)
    exact ((continuous_circleMap 0 1).comp continuous_fst).smul continuous_snd
  have hA : ∫⁻ t in Ioc 0 (2 * π), ∫⁻ z, g (circleMap 0 1 t • z) ∂μ =
      (∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ) * ENNReal.ofReal (2 * π) := by
    have h4 : ∀ t, ∫⁻ z, g (circleMap 0 1 t • z) ∂μ = ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := fun t => by
      rw [(measurePreserving_smul_of_norm_eq_one μ (hn t)).lintegral_comp hgm, hg,
        lintegral_indicator hS]
    simp [h4]
  rw [← ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 h2).ne' ENNReal.ofReal_ne_top, ← hA,
    lintegral_lintegral_swap hj.aemeasurable, mul_right_comm, ← lintegral_const_mul _ hw,
    ← lintegral_indicator hS]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ S
  · have h5 : ∀ t, g (circleMap 0 1 t • z) = ‖φ (circleMap 0 1 t • z)‖ₑ ^ n * w z := fun t => by
      rw [hg, indicator_of_mem (hSc _ (hn t) z hz), hwc _ (hn t) z hz]
    have h6 : Measurable fun t => ‖φ (circleMap 0 1 t • z)‖ₑ ^ n := by
      refine Continuous.measurable ((ENNReal.continuous_pow n).comp (Continuous.enorm ?_))
      exact hφc.comp_continuous ((continuous_circleMap 0 1).smul continuous_const)
        fun t => hSc _ (hn t) z hz
    simp only [indicator_of_mem hz, h5]
    rw [lintegral_mul_const _ h6]
    gcongr
    simpa using enorm_pow_mul_le_lintegral_circle (hφ z hz) n
  · simp [hz]

theorem enorm_pow_mul_lintegral_le_of_balanced (μ : Measure E) [μ.IsAddHaarMeasure] {S : Set E}
    (hS : MeasurableSet S) (hSc : Balanced ℂ S) {φ : E → H}
    (hφ : ∀ z ∈ S, DifferentiableAt ℂ φ z)
    {w : E → ℝ≥0∞} (hw : Measurable w) (hwc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z ∈ S, w (c • z) = w z)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in S, w z ∂μ ≤ ∫⁻ z in S, ‖φ z‖ₑ ^ n * w z ∂μ := by
  refine enorm_pow_mul_lintegral_le_of_circular μ hS (fun c hc z hz => hSc.smul_mem hc.le hz)
    (fun z hz => (hφ z hz).continuousAt.continuousWithinAt) (fun z hz => ?_) hw hwc n
  refine DifferentiableOn.diffContOnCl fun c hc => ?_
  rw [closure_ball _ one_ne_zero, mem_closedBall_zero_iff] at hc
  exact ((hφ _ (hSc.smul_mem hc hz)).comp c
    (differentiableAt_id.smul_const z)).differentiableWithinAt

theorem enorm_pow_mul_lintegral_ball_le (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ} {φ : E → H}
    (hφ : DifferentiableOn ℂ φ (ball 0 r)) {w : ℝ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in ball 0 r, w ‖z‖ ∂μ ≤ ∫⁻ z in ball 0 r, ‖φ z‖ₑ ^ n * w ‖z‖ ∂μ :=
  enorm_pow_mul_lintegral_le_of_balanced μ measurableSet_ball balanced_ball_zero
    (fun _ hz => hφ.differentiableAt (isOpen_ball.mem_nhds hz)) (w := fun z => w ‖z‖)
    (hw.comp measurable_norm) (fun c hc z _ => by simp [norm_smul, hc]) n

theorem enorm_pow_mul_lintegral_closedBall_le (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball 0 r)) {w : ℝ → ℝ≥0∞} (hw : Measurable w) (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in closedBall 0 r, w ‖z‖ ∂μ ≤
      ∫⁻ z in closedBall 0 r, ‖φ z‖ₑ ^ n * w ‖z‖ ∂μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact enorm_pow_mul_lintegral_le_of_balanced μ measurableSet_closedBall
      balanced_closedBall_zero (fun z _ => differentiable_of_subsingleton z) (w := fun z => w ‖z‖)
      (hw.comp measurable_norm) (fun c hc z _ => by simp [norm_smul, hc]) n
  · have h : (closedBall (0 : E) r : Set E) =ᵐ[μ] (ball 0 r : Set E) := by
      rw [← ball_union_sphere]
      exact union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.2 (μ.addHaar_sphere 0 r))
    rw [Measure.restrict_congr_set h]
    exact enorm_pow_mul_lintegral_ball_le μ hφ hw n

theorem enorm_pow_mul_lintegral_ball_le_of_centre (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ≥0∞}
    (hw : Measurable w) (n : ℕ) :
    ‖φ a‖ₑ ^ n * ∫⁻ z in ball a r, w ‖z - a‖ ∂μ ≤
      ∫⁻ z in ball a r, ‖φ z‖ₑ ^ n * w ‖z - a‖ ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have hp : (fun z : E => z + a) ⁻¹' ball a r = ball 0 r := by
    ext z; simp
  have hd : DifferentiableOn ℂ (fun z => φ (z + a)) (ball 0 r) :=
    hφ.comp (differentiableOn_id.add_const a) fun z hz => by simpa using hz
  have h := enorm_pow_mul_lintegral_ball_le μ hd hw n
  have hm := measurePreserving_add_right μ a
  have he := (MeasurableEquiv.addRight a).measurableEmbedding
  rw [← hm.setLIntegral_comp_preimage_emb he _ (ball a r),
    ← hm.setLIntegral_comp_preimage_emb he _ (ball a r), hp]
  simpa using h

theorem enorm_pow_le_inv_measure_mul_lintegral_ball (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} (hr : 0 < r) {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ) :
    ‖φ a‖ₑ ^ n ≤ (μ (ball a r))⁻¹ * ∫⁻ z in ball a r, ‖φ z‖ₑ ^ n ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h := enorm_pow_mul_lintegral_ball_le_of_centre μ hφ (w := fun _ => 1) measurable_const n
  simp only [lintegral_const, one_mul, mul_one, MeasurableSet.univ, Measure.restrict_apply,
    univ_inter] at h
  rw [← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos μ a hr).ne')
      (Or.inl measure_ball_lt_top.ne)]
  exact h

theorem norm_pow_mul_integral_ball_le (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) {w : ℝ → ℝ}
    (hw : Measurable w) (hw0 : ∀ t, 0 ≤ t → 0 ≤ w t) (n : ℕ)
    (hi : IntegrableOn (fun z => w ‖z - a‖) (ball a r) μ)
    (hi' : IntegrableOn (fun z => ‖φ z‖ ^ n * w ‖z - a‖) (ball a r) μ) :
    ‖φ a‖ ^ n * ∫ z in ball a r, w ‖z - a‖ ∂μ ≤ ∫ z in ball a r, ‖φ z‖ ^ n * w ‖z - a‖ ∂μ := by
  have h := enorm_pow_mul_lintegral_ball_le_of_centre μ hφ (w := fun t => ENNReal.ofReal (w t))
    hw.ennreal_ofReal n
  have h0 : ∀ z : E, 0 ≤ ‖φ z‖ ^ n * w ‖z - a‖ := fun z =>
    mul_nonneg (by positivity) (hw0 _ (norm_nonneg _))
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg h0), ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun z => hw0 _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall h0)]
  simpa [ENNReal.ofReal_mul, ENNReal.ofReal_pow] using h

theorem norm_pow_le_inv_measure_mul_integral_ball (μ : Measure E) [μ.IsAddHaarMeasure] {a : E}
    {r : ℝ} (hr : 0 < r) {φ : E → H} (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ)
    (hi : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r) μ) :
    ‖φ a‖ ^ n ≤ (μ.real (ball a r))⁻¹ * ∫ z in ball a r, ‖φ z‖ ^ n ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h := norm_pow_mul_integral_ball_le μ hφ (w := fun _ => 1) measurable_const
    (fun _ _ => zero_le_one) n (integrableOn_const measure_ball_lt_top.ne) (by simpa using hi)
  have h0 : 0 < μ.real (ball a r) :=
    ENNReal.toReal_pos (measure_ball_pos μ a hr).ne' measure_ball_lt_top.ne
  rw [le_inv_mul_iff₀ h0, mul_comm]
  simpa using h

theorem integrableOn_norm_pow_ball {H : Type*} [NormedAddCommGroup H] (μ : Measure E)
    [μ.IsAddHaarMeasure] {a : E} {r : ℝ} {φ : E → H} (hφ : ContinuousOn φ (closedBall a r))
    (n : ℕ) : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r) μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  exact ((hφ.norm.pow n).integrableOn_compact (isCompact_closedBall a r)).mono_set
    ball_subset_closedBall

end Haar

section Volume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem volume_ball_of_finrank_eq_two_mul {D : ℕ} (hD : Module.finrank ℝ E = 2 * D) (a : E)
    {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hD0 : D = 0 := by
      rw [Module.finrank_zero_of_subsingleton] at hD
      omega
    have h : ball a r = parallelepiped (stdOrthonormalBasis ℝ E) := by
      ext z
      rw [Subsingleton.elim z a]
      simp only [mem_ball_self hr, true_iff, mem_parallelepiped_iff]
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
    rw [h, OrthonormalBasis.volume_parallelepiped, hD0]
    simp
  · rw [InnerProductSpace.volume_ball_of_dim_even hD, hD, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

theorem volume_closedBall_of_finrank_eq_two_mul {D : ℕ} (hD : Module.finrank ℝ E = 2 * D) (a : E)
    {r : ℝ} (hr : 0 < r) :
    volume (closedBall a r) = ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  rw [← volume_ball_of_finrank_eq_two_mul hD a hr]
  rcases subsingleton_or_nontrivial E with hE | hE
  · congr 1
    ext z
    rw [Subsingleton.elim z a]
    simp [hr, hr.le]
  · exact Measure.addHaar_closedBall_eq_addHaar_ball _ _ _

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem volume_ball_complex (a : E) {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ Module.finrank ℂ E * r ^ (2 * Module.finrank ℂ E) /
      (Module.finrank ℂ E).factorial) :=
  volume_ball_of_finrank_eq_two_mul
    (by rw [← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]) a hr

theorem norm_pow_le_factorial_div_mul_integral_ball {a : E} {r : ℝ} (hr : 0 < r) {φ : E → H}
    (hφ : DifferentiableOn ℂ φ (ball a r)) (n : ℕ)
    (hi : IntegrableOn (fun z => ‖φ z‖ ^ n) (ball a r)) :
    ‖φ a‖ ^ n ≤ (Module.finrank ℂ E).factorial /
      (π ^ Module.finrank ℂ E * r ^ (2 * Module.finrank ℂ E)) * ∫ z in ball a r, ‖φ z‖ ^ n := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  have h := norm_pow_le_inv_measure_mul_integral_ball volume hr hφ n hi
  rwa [Measure.real, volume_ball_complex a hr, ENNReal.toReal_ofReal (by positivity), inv_div] at h

end Volume

section Euclidean

variable {ι : Type*} [Fintype ι]

theorem volume_ball_euclideanSpace_complex (a : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    volume (ball a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) :=
  volume_ball_of_finrank_eq_two_mul (by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]) a hr

theorem volume_closedBall_euclideanSpace_complex (a : EuclideanSpace ℂ ι) {r : ℝ} (hr : 0 < r) :
    volume (closedBall a r) = ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
      (Fintype.card ι).factorial) :=
  volume_closedBall_of_finrank_eq_two_mul (by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι), Complex.finrank_real_complex,
      finrank_euclideanSpace]) a hr

theorem measurePreserving_toLp_complex :
    MeasurePreserving (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) := by
  let e : (ι → ℂ) ≃L[ℂ] EuclideanSpace ℂ ι := (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => ℂ).symm
  have hm : Measurable (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) := e.continuous.measurable
  have hH : ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) volume
  have hb : ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) (ball 0 1) =
      volume (ball (0 : EuclideanSpace ℂ ι) 1) := by
    rw [Measure.map_apply hm measurableSet_ball, volume_ball_euclideanSpace_complex 0 one_pos]
    have h1 := Complex.volume_sum_rpow_lt_one ι (p := 2) one_le_two
    have h2 : (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) ⁻¹' ball 0 1 =
        {x : ι → ℂ | ∑ i, ‖x i‖ ^ (2 : ℝ) < 1} := by
      ext x
      simp [EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos]
    rw [h2, h1, mul_div_cancel_left₀ _ (two_ne_zero' ℝ), Real.Gamma_nat_eq_factorial]
    norm_num
  have h0 : volume (ball (0 : EuclideanSpace ℂ ι) 1) ≠ 0 := (measure_ball_pos _ 0 one_pos).ne'
  have ht : volume (ball (0 : EuclideanSpace ℂ ι) 1) ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨hm, ?_⟩
  have h1 : Measure.addHaarScalarFactor ((volume : Measure (ι → ℂ)).map
      (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι)) volume = 1 := by
    rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hb
    exact_mod_cast (ENNReal.mul_eq_right h0 ht).1 hb
  rw [h, h1, one_smul]

theorem preimage_toLp_ball_complex {r : ℝ} (hr : 0 < r) :
    (WithLp.toLp 2 : (ι → ℂ) → EuclideanSpace ℂ ι) ⁻¹' ball 0 r =
      {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < r ^ 2} := by
  ext x
  simp [EuclideanSpace.norm_eq, Real.sqrt_lt' hr]

theorem volume_sum_norm_sq_lt {r : ℝ} (hr : 0 < r) :
    volume {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < r ^ 2} =
      ENNReal.ofReal (π ^ Fintype.card ι * r ^ (2 * Fintype.card ι) /
        (Fintype.card ι).factorial) := by
  rw [← preimage_toLp_ball_complex hr,
    measurePreserving_toLp_complex.measure_preimage measurableSet_ball.nullMeasurableSet,
    volume_ball_euclideanSpace_complex 0 hr]

theorem enorm_pow_mul_lintegral_sum_norm_sq_lt_le {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] {R : ℝ} {φ : (ι → ℂ) → H}
    (hφ : DifferentiableOn ℂ φ {x | ∑ i, ‖x i‖ ^ 2 < R}) {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (n : ℕ) :
    ‖φ 0‖ₑ ^ n * ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, w (∑ i, ‖z i‖ ^ 2) ≤
      ∫⁻ z in {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R}, ‖φ z‖ₑ ^ n * w (∑ i, ‖z i‖ ^ 2) := by
  have hq : Continuous fun x : ι → ℂ => ∑ i, ‖x i‖ ^ 2 := by fun_prop
  have ho : IsOpen {x : ι → ℂ | ∑ i, ‖x i‖ ^ 2 < R} := isOpen_lt hq continuous_const
  refine enorm_pow_mul_lintegral_le_of_balanced volume ho.measurableSet ?_
    (fun _ hz => hφ.differentiableAt (ho.mem_nhds hz)) (w := fun z => w (∑ i, ‖z i‖ ^ 2))
    (hw.comp hq.measurable) (fun c hc z _ => by simp [hc]) n
  rintro c hc _ ⟨z, hz, rfl⟩
  simp only [mem_ofPred_eq, Pi.smul_apply, norm_smul] at hz ⊢
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i _ => ?_) hz
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) hc

theorem submean_sq_closedBall {D : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {r : ℝ} (hr : 0 < r) {φ : EuclideanSpace ℂ (Fin D) → H}
    (hφ : DifferentiableOn ℂ φ (ball 0 r)) :
    (∀ w : ℝ → ℝ≥0∞, Measurable w →
      ‖φ 0‖ₑ ^ 2 * ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, w ‖z‖ ≤
        ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 * w ‖z‖) ∧
    ‖φ 0‖ₑ ^ 2 ≤ (volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r))⁻¹ *
      ∫⁻ z in closedBall (0 : EuclideanSpace ℂ (Fin D)) r, ‖φ z‖ₑ ^ 2 ∧
    volume (closedBall (0 : EuclideanSpace ℂ (Fin D)) r) =
      ENNReal.ofReal (π ^ D * r ^ (2 * D) / D.factorial) := by
  refine ⟨fun w hw => enorm_pow_mul_lintegral_closedBall_le volume hφ hw 2, ?_, ?_⟩
  · have h := enorm_pow_mul_lintegral_closedBall_le volume hφ (w := fun _ => 1) measurable_const 2
    simp only [lintegral_const, one_mul, mul_one, MeasurableSet.univ, Measure.restrict_apply,
      univ_inter] at h
    rw [← ENNReal.div_eq_inv_mul,
      ENNReal.le_div_iff_mul_le (Or.inl (measure_closedBall_pos _ _ hr).ne')
        (Or.inl measure_closedBall_lt_top.ne)]
    exact h
  · simpa using volume_closedBall_euclideanSpace_complex (0 : EuclideanSpace ℂ (Fin D)) hr

end Euclidean

end GlobalTheory
