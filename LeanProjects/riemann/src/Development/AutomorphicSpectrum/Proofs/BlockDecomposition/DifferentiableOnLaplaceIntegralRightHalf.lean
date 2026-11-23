import Mathlib
open MeasureTheory

namespace GlobalTheory.CompanionTheory.HoloFamily

theorem abs_le_exp_add_exp_neg (δ y : ℝ) (hδ : 0 < δ) :
    |y| ≤ (Real.exp (δ * y) + Real.exp (-(δ * y))) / δ := by
  rw [le_div_iff₀ hδ]
  have h1 := Real.add_one_le_exp (δ * y)
  have h2 := Real.add_one_le_exp (-(δ * y))
  have e1 := Real.exp_pos (δ * y)
  have e2 := Real.exp_pos (-(δ * y))
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith

theorem exp_mul_le_add (a b t y : ℝ) (ha : a ≤ t) (hb : t ≤ b) :
    Real.exp (t * y) ≤ Real.exp (a * y) + Real.exp (b * y) := by
  rcases le_total 0 y with hy | hy
  · have : Real.exp (t * y) ≤ Real.exp (b * y) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hy)
    have := Real.exp_pos (a * y)
    linarith
  · have : Real.exp (t * y) ≤ Real.exp (a * y) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha hy)
    have := Real.exp_pos (b * y)
    linarith

theorem abs_mul_exp_le (σ t y : ℝ) (hσ : 0 < σ) (h1 : 3 * σ / 4 ≤ t) (h2 : t ≤ 5 * σ / 4) :
    |y| * Real.exp (t * y) ≤ (4 / σ) * (Real.exp (σ / 2 * y) + 2 * Real.exp (σ * y)
      + Real.exp (3 * σ / 2 * y)) := by
  have hδ : 0 < σ / 4 := by positivity
  have hA := abs_le_exp_add_exp_neg (σ / 4) y hδ
  have hB := exp_mul_le_add (3 * σ / 4) (5 * σ / 4) t y h1 h2
  have hm := mul_le_mul hA hB (Real.exp_pos _).le
    (div_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hδ.le)
  refine hm.trans (le_of_eq ?_)
  have e1 : Real.exp (σ / 4 * y) * Real.exp (3 * σ / 4 * y) = Real.exp (σ * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (σ / 4 * y) * Real.exp (5 * σ / 4 * y) = Real.exp (3 * σ / 2 * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-(σ / 4 * y)) * Real.exp (3 * σ / 4 * y) = Real.exp (σ / 2 * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have e4 : Real.exp (-(σ / 4 * y)) * Real.exp (5 * σ / 4 * y) = Real.exp (σ * y) := by
    rw [← Real.exp_add]; congr 1; ring
  have : (Real.exp (σ / 4 * y) + Real.exp (-(σ / 4 * y))) / (σ / 4) *
      (Real.exp (3 * σ / 4 * y) + Real.exp (5 * σ / 4 * y))
      = (4 / σ) * (Real.exp (σ / 4 * y) * Real.exp (3 * σ / 4 * y)
        + Real.exp (σ / 4 * y) * Real.exp (5 * σ / 4 * y)
        + Real.exp (-(σ / 4 * y)) * Real.exp (3 * σ / 4 * y)
        + Real.exp (-(σ / 4 * y)) * Real.exp (5 * σ / 4 * y)) := by
    field_simp
    ring
  rw [this, e1, e2, e3, e4]
  ring

theorem differentiableOn_integral_mul_cexp
    {X : Type} [MeasurableSpace X] (μ : Measure X) (G : X → ℂ) (L : X → ℝ)
    (hG : AEStronglyMeasurable G μ) (hL : Measurable L)
    (hI : ∀ σ : ℝ, 0 < σ → Integrable (fun x => ‖G x‖ * Real.exp (σ * L x)) μ) :
    DifferentiableOn ℂ (fun u : ℂ => ∫ x, G x * Complex.exp (u * (L x : ℂ)) ∂μ)
      {u : ℂ | 0 < u.re} := by
  intro u₀ hu₀
  have hσ : 0 < u₀.re := hu₀
  set σ := u₀.re with hσdef
  have hLc : Measurable fun x => (L x : ℂ) := Complex.measurable_ofReal.comp hL
  have hmeas : ∀ u : ℂ, AEStronglyMeasurable (fun x => G x * Complex.exp (u * (L x : ℂ))) μ :=
    fun u => hG.mul ((Complex.measurable_exp.comp (hLc.const_mul u)).aestronglyMeasurable)
  have hmeas' : ∀ u : ℂ, AEStronglyMeasurable
      (fun x => G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ))) μ :=
    fun u => (hG.mul hLc.aestronglyMeasurable).mul
      ((Complex.measurable_exp.comp (hLc.const_mul u)).aestronglyMeasurable)
  have hnorm : ∀ (u : ℂ) (x : X), ‖Complex.exp (u * (L x : ℂ))‖ = Real.exp (u.re * L x) := by
    intro u x
    rw [Complex.norm_exp]
    simp
  have hF_int : Integrable (fun x => G x * Complex.exp (u₀ * (L x : ℂ))) μ := by
    refine (hI σ hσ).mono' (hmeas u₀) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hnorm]
  let bound : X → ℝ := fun x => (4 / σ) * (‖G x‖ * Real.exp (σ / 2 * L x)
    + 2 * (‖G x‖ * Real.exp (σ * L x)) + ‖G x‖ * Real.exp (3 * σ / 2 * L x))
  have hbound : Integrable bound μ :=
    (((hI (σ / 2) (by positivity)).add ((hI σ hσ).const_mul 2)).add
      (hI (3 * σ / 2) (by positivity))).const_mul (4 / σ)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (u : ℂ) x => G x * Complex.exp (u * (L x : ℂ)))
    (F' := fun (u : ℂ) x => G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ)))
    (x₀ := u₀) (s := Metric.ball u₀ (σ / 4)) (bound := bound)
    (Metric.ball_mem_nhds u₀ (by positivity))
    (Filter.Eventually.of_forall hmeas) hF_int (hmeas' u₀)
    (Filter.Eventually.of_forall fun x u hu => ?_) hbound
    (Filter.Eventually.of_forall fun x u _ => ?_)
  · exact hmain.2.differentiableAt.differentiableWithinAt
  · have hre : |u.re - σ| < σ / 4 := by
      have h1 : ‖u - u₀‖ < σ / 4 := by simpa [dist_eq_norm] using hu
      have h2 : |(u - u₀).re| ≤ ‖u - u₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      exact lt_of_le_of_lt h2 h1
    have hab := abs_lt.mp hre
    have hb := abs_mul_exp_le σ u.re (L x) hσ (by linarith [hab.1]) (by linarith [hab.2])
    have hnG := norm_nonneg (G x)
    calc ‖G x * (L x : ℂ) * Complex.exp (u * (L x : ℂ))‖
        = ‖G x‖ * (|L x| * Real.exp (u.re * L x)) := by
          rw [norm_mul, norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
      _ ≤ ‖G x‖ * ((4 / σ) * (Real.exp (σ / 2 * L x) + 2 * Real.exp (σ * L x)
            + Real.exp (3 * σ / 2 * L x))) := mul_le_mul_of_nonneg_left hb hnG
      _ = bound x := by simp only [bound]; ring
  · have h1 : HasDerivAt (fun w : ℂ => w * (L x : ℂ)) (L x : ℂ) u := by
      simpa using (hasDerivAt_id u).mul_const (L x : ℂ)
    exact ((h1.cexp).const_mul (G x)).congr_deriv (by ring)

end GlobalTheory.CompanionTheory.HoloFamily
