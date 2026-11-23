import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Circle

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def rotAbout {n : ℕ} (c : V n) (a : ℂ) (z : V n) : V n := c + a • (z - c)

theorem rotAbout_sub {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (z : V n) :
    ‖rotAbout c a z - c‖ = ‖z - c‖ := by
  simp [rotAbout, norm_smul, ha]

theorem rotAbout_mem_ball_iff {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) (z : V n) :
    rotAbout c a z ∈ ball c R ↔ z ∈ ball c R := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, rotAbout_sub c ha]

theorem measurePreserving_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (rotAbout c a) volume volume :=
  (measurePreserving_add_left volume c).comp
    ((measurePreserving_smul_unit a ha).comp (measurePreserving_sub_right volume c))

theorem measurableEmbedding_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurableEmbedding (rotAbout c a) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let h : V n ≃ₜ V n :=
    { toFun := rotAbout c a
      invFun := fun z => c + a⁻¹ • (z - c)
      left_inv := fun z => by simp [rotAbout, smul_smul, inv_mul_cancel₀ ha0]
      right_inv := fun z => by simp [rotAbout, smul_smul, mul_inv_cancel₀ ha0]
      continuous_toFun := by unfold rotAbout; fun_prop
      continuous_invFun := by fun_prop }
  exact h.measurableEmbedding

theorem indicator_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) {β : Type*}
    [Zero β] (g : V n → β) (z : V n) :
    (ball c R).indicator (fun z => g (rotAbout c a z)) z =
      (ball c R).indicator g (rotAbout c a z) := by
  by_cases hz : z ∈ ball c R
  · rw [indicator_of_mem hz, indicator_of_mem ((rotAbout_mem_ball_iff c ha R z).2 hz)]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (fun h => hz ((rotAbout_mem_ball_iff c ha R z).1 h))]

theorem setLIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    (g : V n → ℝ≥0∞) :
    ∫⁻ z in ball c R, g (rotAbout c a z) = ∫⁻ z in ball c R, g z := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    lintegral_congr fun z => indicator_rotAbout c ha R g z]
  exact (measurePreserving_rotAbout c ha).lintegral_comp_emb (measurableEmbedding_rotAbout c ha) _

theorem setIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : V n → E) :
    ∫ z in ball c R, g (rotAbout c a z) = ∫ z in ball c R, g z := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    integral_congr_ae (Eventually.of_forall fun z => indicator_rotAbout c ha R g z)]
  exact (measurePreserving_rotAbout c ha).integral_comp (measurableEmbedding_rotAbout c ha) _

theorem integrableOn_rotAbout_iff {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    {E : Type*} [NormedAddCommGroup E] (g : V n → E) :
    IntegrableOn (fun z => g (rotAbout c a z)) (ball c R) ↔ IntegrableOn g (ball c R) := by
  rw [← integrable_indicator_iff measurableSet_ball, ← integrable_indicator_iff measurableSet_ball]
  have : (ball c R).indicator (fun z => g (rotAbout c a z)) =
      (ball c R).indicator g ∘ rotAbout c a :=
    funext fun z => indicator_rotAbout c ha R g z
  rw [this]
  exact (measurePreserving_rotAbout c ha).integrable_comp_emb (measurableEmbedding_rotAbout c ha)

theorem norm_exp_mul_I_eq_one (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem continuous_rotAbout_exp {n : ℕ} (c : V n) :
    Continuous (fun p : ℝ × V n => rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) := by
  unfold rotAbout; fun_prop

theorem continuousOn_comp_rotAbout {n : ℕ} {c : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
      (s ×ˢ ball c R) := by
  refine hu.continuousOn.comp (continuous_rotAbout_exp c).continuousOn ?_
  rintro ⟨θ, z⟩ ⟨_, hz⟩
  exact (rotAbout_mem_ball_iff c (norm_exp_mul_I_eq_one θ) R z).2 hz

theorem mv : MVStatement := by
  intro n c R u r hu hr
  have hT1 := norm_exp_mul_I_eq_one
  have hrot : ∀ θ : ℝ, ∫⁻ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ =
        ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖ := by
    intro θ
    have h := setLIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z‖ₑ ^ 2 * r ‖z - c‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hmeas : AEMeasurable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    rw [Measure.prod_restrict]
    have h1 := ((continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aemeasurable
      (μ := volume.prod volume) (measurableSet_Ioc.prod measurableSet_ball)).enorm.pow_const 2
    have h2 : Measurable fun p : ℝ × V n => r ‖p.2 - c‖ :=
      hr.comp ((measurable_snd.sub_const c).norm)
    exact h1.mul h2.aemeasurable
  have hvol : volume (Ioc (0 : ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioc, sub_zero]
  have key : (∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi) =
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← hvol, ← setLIntegral_const, ← lintegral_lintegral_swap hmeas]
    exact lintegral_congr fun θ => (hrot θ).symm
  have hmr : Measurable fun z : V n => r ‖z - c‖ := hr.comp (measurable_id.sub_const c).norm
  have low : ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ ≤
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← lintegral_const_mul _ hmr]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcz : Continuous fun θ : ℝ => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) :=
      hu.continuousOn.comp_continuous (by unfold rotAbout; fun_prop)
        (fun θ => (rotAbout_mem_ball_iff c (hT1 θ) R z).2 hz)
    have hm : Measurable fun θ : ℝ =>
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 :=
      hcz.measurable.enorm.pow_const 2
    rw [lintegral_mul_const _ hm]
    gcongr
    exact circle_mean_sq hu hw
  have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  refine (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 ?_
  calc ‖u c‖ₑ ^ 2 * (∫⁻ z in ball c R, r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi)
      = ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ := by ring
    _ ≤ _ := low
    _ = _ := key.symm

theorem mvEq : MVEqStatement := by
  intro n c R u k hu hk hF
  have hT1 := norm_exp_mul_I_eq_one
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have hrot : ∀ θ : ℝ, ∫ z in ball c R,
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) := by
    intro θ
    have h := setIntegral_rotAbout c (hT1 θ) R (fun z => u z * (k ‖z - c‖ : ℂ))
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hrotN : ∀ θ : ℝ, ∫ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ)‖ =
        ∫ z in ball c R, ‖u z * (k ‖z - c‖ : ℂ)‖ := by
    intro θ
    have h := setIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z * (k ‖z - c‖ : ℂ)‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hrotI : ∀ θ : ℝ, IntegrableOn
      (fun z => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ)) (ball c R) := by
    intro θ
    have h := integrableOn_rotAbout_iff c (hT1 θ) R (fun z => u z * (k ‖z - c‖ : ℂ))
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h.2 hF
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) * (k ‖p.2 - c‖ : ℂ))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
        ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
      rw [Measure.prod_restrict]
      exact (continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aestronglyMeasurable
        (measurableSet_Ioc.prod measurableSet_ball)
    exact h1.mul hk.aestronglyMeasurable.comp_snd
  have hint : Integrable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall hrotI, ?_⟩
    have hc0 : Integrable (fun _ : ℝ => ∫ z in ball c R, ‖u z * (k ‖z - c‖ : ℂ)‖)
        (volume.restrict (Ioc 0 (2 * Real.pi))) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact hc0.congr (Eventually.of_forall fun θ => (hrotN θ).symm)
  have hswap := integral_integral_swap hint
  have hL : ∫ θ in Ioc 0 (2 * Real.pi), ∫ z in ball c R,
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) := by
    simp only [hrot]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hpi, sub_zero, Complex.real_smul]
  have hR : ∫ z in ball c R, ∫ θ in Ioc 0 (2 * Real.pi),
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcm := circle_mean hu hw
    simp only [rotAbout]
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hpi, hcm]
  have h2 : ((2 * Real.pi : ℝ) : ℂ) * ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ)) := by
    rw [← hL, hswap, hR, mul_assoc]
  have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  exact mul_left_cancel₀ hne h2

end ReciprocityTheory.L2DbarEstimates.C
