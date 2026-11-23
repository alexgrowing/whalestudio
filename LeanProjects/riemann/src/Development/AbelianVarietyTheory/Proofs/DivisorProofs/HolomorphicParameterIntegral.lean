import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem abs_log_mul_rpow_le_of_near {x t σ δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (ht : |t - σ| < δ) :
    |Real.log x| * x ^ t ≤ (x ^ (σ - 2 * δ) + x ^ (σ + 2 * δ)) / δ := by
  have ht' := abs_lt.1 ht
  have h1 : 0 ≤ x ^ (σ - 2 * δ) := Real.rpow_nonneg hx.le _
  have h2 : 0 ≤ x ^ (σ + 2 * δ) := Real.rpow_nonneg hx.le _
  have hxt : 0 ≤ x ^ t := Real.rpow_nonneg hx.le _
  rcases le_total 1 x with h | h
  · have hl : |Real.log x| ≤ x ^ δ / δ := by
      rw [abs_of_nonneg (Real.log_nonneg h)]; exact Real.log_le_rpow_div hx.le hδ
    have he : x ^ δ * x ^ t ≤ x ^ (σ + 2 * δ) := by
      rw [← Real.rpow_add hx]; exact Real.rpow_le_rpow_of_exponent_le h (by linarith)
    calc |Real.log x| * x ^ t ≤ x ^ δ / δ * x ^ t := mul_le_mul_of_nonneg_right hl hxt
      _ = (x ^ δ * x ^ t) / δ := by ring
      _ ≤ (x ^ (σ - 2 * δ) + x ^ (σ + 2 * δ)) / δ := by gcongr; linarith
  · have hl : |Real.log x| ≤ x ^ (-δ) / δ := by
      rw [abs_of_nonpos (Real.log_nonpos hx.le h), ← Real.log_inv]
      have := Real.log_le_rpow_div (inv_nonneg.2 hx.le) hδ
      rwa [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at this
    have he : x ^ (-δ) * x ^ t ≤ x ^ (σ - 2 * δ) := by
      rw [← Real.rpow_add hx]; exact Real.rpow_le_rpow_of_exponent_ge hx h (by linarith)
    calc |Real.log x| * x ^ t ≤ x ^ (-δ) / δ * x ^ t := mul_le_mul_of_nonneg_right hl hxt
      _ = (x ^ (-δ) * x ^ t) / δ := by ring
      _ ≤ (x ^ (σ - 2 * δ) + x ^ (σ + 2 * δ)) / δ := by gcongr; linarith

theorem differentiableOn_integral_integral_mul_cpow {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μK : Measure α) [IsFiniteMeasure μK] (μ : Measure β) [SFinite μ]
    (A : α → β → ℂ) (a : β → ℝ) (ha : Measurable a) (hpos : ∀ l, 0 < a l)
    (hA : AEStronglyMeasurable (Function.uncurry A) (μK.prod μ))
    (g : β → ℝ) (hg : ∀ s : ℝ, 1 < s → Integrable (fun l => g l * a l ^ s) μ)
    (hAg : ∀ k l, ‖A k l‖ ≤ g l) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ k, ∫ l, A k l * ((a l : ℝ) : ℂ) ^ z ∂μ ∂μK)
      {z : ℂ | 1 < z.re} := by
  let F : ℂ → α × β → ℂ := fun z p => A p.1 p.2 * ((a p.2 : ℝ) : ℂ) ^ z
  have hmeas : ∀ z, AEStronglyMeasurable (F z) (μK.prod μ) := fun z =>
    hA.mul ((Complex.measurable_ofReal.comp (ha.comp measurable_snd)).pow_const z).aestronglyMeasurable
  have hgp : ∀ s : ℝ, 1 < s → Integrable (fun p : α × β => g p.2 * a p.2 ^ s) (μK.prod μ) :=
    fun s hs => (hg s hs).comp_snd μK
  have hnorm : ∀ z p, ‖F z p‖ ≤ g p.2 * a p.2 ^ z.re := by
    intro z p
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos p.2)]
    exact mul_le_mul_of_nonneg_right (hAg _ _) (Real.rpow_nonneg (hpos _).le _)
  have hint : ∀ z : ℂ, 1 < z.re → Integrable (F z) (μK.prod μ) := fun z hz =>
    (hgp _ hz).mono' (hmeas z) (Filter.Eventually.of_forall (hnorm z))
  have heq : ∀ z ∈ {z : ℂ | 1 < z.re},
      (∫ k, ∫ l, A k l * ((a l : ℝ) : ℂ) ^ z ∂μ ∂μK) = ∫ p, F z p ∂(μK.prod μ) := by
    intro z hz
    exact (integral_prod (F z) (hint z hz)).symm
  refine DifferentiableOn.congr ?_ heq
  intro z₀ hz₀
  apply DifferentiableAt.differentiableWithinAt
  have hσ : 1 < z₀.re := hz₀
  set σ := z₀.re with hσdef
  set δ := (σ - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  let F' : ℂ → α × β → ℂ := fun z p =>
    A p.1 p.2 * (((a p.2 : ℝ) : ℂ) ^ z * ((Real.log (a p.2) : ℝ) : ℂ))
  have hball : ∀ z ∈ Metric.ball z₀ δ, |z.re - σ| < δ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc |z.re - σ| = |(z - z₀).re| := by simp [σ]
      _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
      _ < δ := hz
  have h1 : 1 < σ - 2 * δ := by rw [hδdef]; linarith
  have h2 : 1 < σ + 2 * δ := by rw [hδdef]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μK.prod μ) (F := F) (x₀ := z₀)
    (bound := fun p => (g p.2 * a p.2 ^ (σ - 2 * δ) + g p.2 * a p.2 ^ (σ + 2 * δ)) / δ)
    (Metric.ball_mem_nhds z₀ hδ) (Filter.Eventually.of_forall hmeas) (hint z₀ hz₀)
    (F' := F') ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · exact hA.mul ((((Complex.measurable_ofReal.comp (ha.comp measurable_snd)).pow_const z₀).mul
      (Complex.measurable_ofReal.comp (ha.comp measurable_snd).log))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p z hz => ?_)
    have hp := hpos p.2
    have hgnn : 0 ≤ g p.2 := (norm_nonneg _).trans (hAg p.1 p.2)
    have hb := abs_log_mul_rpow_le_of_near hp hδ (hball z hz)
    simp only [F', norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.norm_real,
      Real.norm_eq_abs]
    calc ‖A p.1 p.2‖ * (a p.2 ^ z.re * |Real.log (a p.2)|)
        ≤ g p.2 * (|Real.log (a p.2)| * a p.2 ^ z.re) := by
          rw [mul_comm (a p.2 ^ z.re)]
          exact mul_le_mul_of_nonneg_right (hAg _ _)
            (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _))
      _ ≤ g p.2 * ((a p.2 ^ (σ - 2 * δ) + a p.2 ^ (σ + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left hb hgnn
      _ = (g p.2 * a p.2 ^ (σ - 2 * δ) + g p.2 * a p.2 ^ (σ + 2 * δ)) / δ := by ring
  · exact ((hgp _ h1).add (hgp _ h2)).div_const δ
  · refine Filter.Eventually.of_forall (fun p z _ => ?_)
    have hp := hpos p.2
    have hd := (hasDerivAt_id' z).const_cpow (c := ((a p.2 : ℝ) : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.2 hp.ne'))
    have hd2 := hd.const_mul (A p.1 p.2)
    have e : F' z p = A p.1 p.2 * (((a p.2 : ℝ) : ℂ) ^ z * Complex.log ((a p.2 : ℝ) : ℂ) * 1) := by
      simp only [F', mul_one, Complex.ofReal_log hp.le]
    rw [e]
    exact hd2

end GlobalTheory
