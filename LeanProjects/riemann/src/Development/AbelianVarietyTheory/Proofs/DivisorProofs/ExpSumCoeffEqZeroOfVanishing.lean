import Mathlib

open MeasureTheory Filter Topology

namespace GlobalTheory.ExpSumUniq

noncomputable def chr {N : ℕ} (μ : Fin N → ℝ) (t : Fin N → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ j, (μ j : ℂ) * (t j : ℂ))

lemma norm_chr {N : ℕ} (μ t : Fin N → ℝ) : ‖chr μ t‖ = 1 := by
  unfold chr
  have : 2 * Real.pi * Complex.I * ∑ j, (μ j : ℂ) * (t j : ℂ)
      = ((2 * Real.pi * ∑ j, μ j * t j : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma chr_sub {N : ℕ} (a b t : Fin N → ℝ) : chr (a - b) t = chr a t / chr b t := by
  unfold chr
  rw [← Complex.exp_sub]
  congr 1
  simp only [Pi.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib]
  ring

lemma continuous_chr {N : ℕ} (μ : Fin N → ℝ) : Continuous (chr μ) := by
  unfold chr; fun_prop

lemma chr_eq_prod {N : ℕ} (μ t : Fin N → ℝ) :
    chr μ t = ∏ j, Complex.exp (2 * Real.pi * Complex.I * ((μ j : ℂ) * (t j : ℂ))) := by
  unfold chr
  rw [Finset.mul_sum, Complex.exp_sum]

noncomputable def avg (R m : ℝ) : ℂ :=
  (R⁻¹ : ℂ) * ∫ s in (0:ℝ)..R, Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (s : ℂ)))

lemma avg_zero {R : ℝ} (hR : R ≠ 0) : avg R 0 = 1 := by
  simp [avg, hR]

lemma norm_avg_le {R m : ℝ} (hR : 0 < R) (hm : m ≠ 0) :
    ‖avg R m‖ ≤ 1 / (Real.pi * |m|) * R⁻¹ := by
  set c : ℂ := 2 * Real.pi * Complex.I * (m : ℂ) with hcdef
  have hc : c ≠ 0 := by
    simp [hcdef, Real.pi_ne_zero, hm, Complex.I_ne_zero]
  have hI : ∫ s in (0:ℝ)..R, Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) * (s : ℂ)))
      = (Complex.exp (c * R) - Complex.exp (c * (0:ℝ))) / c := by
    rw [← integral_exp_mul_complex hc]
    congr 1; ext s; rw [hcdef]; ring_nf
  have hnum : ‖Complex.exp (c * R) - Complex.exp (c * (0:ℝ))‖ ≤ 2 := by
    have h1 : ‖Complex.exp (c * R)‖ = 1 := by
      have : c * (R : ℂ) = ((2 * Real.pi * m * R : ℝ) : ℂ) * Complex.I := by
        rw [hcdef]; push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    calc _ ≤ ‖Complex.exp (c * R)‖ + ‖Complex.exp (c * (0:ℝ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1]; simp; norm_num
  have hden : ‖c‖ = 2 * Real.pi * |m| := by
    simp [hcdef, Complex.norm_real, abs_of_pos Real.pi_pos]
  have hRn : ‖(R⁻¹ : ℂ)‖ = R⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hpm : 0 < Real.pi * |m| := mul_pos Real.pi_pos (abs_pos.mpr hm)
  rw [avg, hI, norm_mul, norm_div, hden, hRn]
  calc R⁻¹ * (‖Complex.exp (c * R) - Complex.exp (c * (0:ℝ))‖ / (2 * Real.pi * |m|))
      ≤ R⁻¹ * (2 / (2 * Real.pi * |m|)) := by gcongr
    _ = 1 / (Real.pi * |m|) * R⁻¹ := by field_simp

noncomputable def lim0 (m : ℝ) : ℂ := if m = 0 then 1 else 0

lemma tendsto_avg (m : ℝ) : Tendsto (fun R => avg R m) atTop (𝓝 (lim0 m)) := by
  by_cases hm : m = 0
  · subst hm
    simp only [lim0, if_true]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [avg_zero hR.ne']
  · simp only [lim0, hm, if_false]
    have h0 : Tendsto (fun R : ℝ => 1 / (Real.pi * |m|) * R⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (1 / (Real.pi * |m|))
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact norm_avg_le hR hm

noncomputable def rho (R : ℝ) : Measure ℝ :=
  (ENNReal.ofReal R)⁻¹ • volume.restrict (Set.Ioc (0:ℝ) R)

lemma rho_prob {R : ℝ} (hR : 0 < R) : IsProbabilityMeasure (rho R) := by
  constructor
  rw [rho, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hR) ENNReal.ofReal_ne_top

lemma integral_rho {R : ℝ} (hR : 0 < R) (f : ℝ → ℂ) :
    ∫ s, f s ∂(rho R) = (R⁻¹ : ℂ) * ∫ s in (0:ℝ)..R, f s := by
  rw [rho, integral_smul_measure, intervalIntegral.integral_of_le hR.le, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hR.le, Complex.real_smul]
  push_cast; rfl

lemma integral_chr {N : ℕ} {R : ℝ} (hR : 0 < R) (μ : Fin N → ℝ) :
    ∫ t, chr μ t ∂(Measure.pi (fun _ : Fin N => rho R)) = ∏ j, avg R (μ j) := by
  haveI := rho_prob hR
  simp_rw [chr_eq_prod]
  rw [integral_fintype_prod_eq_prod
    (fun j (s : ℝ) => Complex.exp (2 * Real.pi * Complex.I * ((μ j : ℂ) * (s : ℂ))))]
  congr 1; ext j; rw [integral_rho hR]; rfl

lemma prod_indicator_zero_eq_ite {N : ℕ} (μ : Fin N → ℝ) : ∏ j, lim0 (μ j) = if μ = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [lim0]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [lim0] using hj)

theorem coeff_eq_zero : ∀ (N : ℕ) (Ξ : Type) (lam : Ξ → Fin N → ℝ) (c : Ξ → ℂ),
    Function.Injective lam → Summable c →
    (∀ t : Fin N → ℝ, ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I *
      ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) = 0) →
    ∀ ξ, c ξ = 0 := by
  intro N Ξ lam c hinj hc hsum ξ₀
  let g : Ξ → (Fin N → ℝ) → ℂ := fun ξ t => c ξ * chr (lam ξ - lam ξ₀) t
  have hg0 : ∀ t, ∑' ξ, g ξ t = 0 := by
    intro t
    have h : ∑' ξ, c ξ * chr (lam ξ) t = 0 := hsum t
    simp only [g, chr_sub, ← mul_div_assoc]
    rw [tsum_div_const, h, zero_div]
  have hcn : Summable (fun ξ => ‖c ξ‖) := summable_norm_iff.mpr hc
  have hgn : ∀ ξ t, ‖g ξ t‖ = ‖c ξ‖ := by
    intro ξ t; simp [g, norm_mul, norm_chr]
  have hgs : ∀ t, Summable (fun ξ => g ξ t) := fun t =>
    Summable.of_norm (by simpa [hgn] using hcn)
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  obtain ⟨F, hF, hF0⟩ : ∃ F : Finset Ξ, ∑' ξ : {x // x ∉ F}, ‖c ξ‖ < ε ∧ {ξ₀} ≤ F :=
    (((tendsto_tsum_compl_atTop_zero (fun ξ => ‖c ξ‖)).eventually (gt_mem_nhds hε)).and
      (eventually_ge_atTop {ξ₀})).exists
  have hξ₀F : ξ₀ ∈ F := Finset.singleton_subset_iff.mp hF0
  have hbound : ∀ t, ‖∑ ξ ∈ F, g ξ t‖ ≤ ε := by
    intro t
    have h := (hgs t).sum_add_tsum_subtype_compl F
    rw [hg0 t] at h
    rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    have hs : Summable (fun ξ : {x // x ∉ F} => ‖g ξ t‖) := by
      have h' : Summable (fun ξ : {x // x ∉ F} => ‖c ξ‖) :=
        hcn.comp_injective Subtype.val_injective
      simp only [hgn]; exact h'
    calc _ ≤ ∑' ξ : {x // x ∉ F}, ‖g ξ t‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' ξ : {x // x ∉ F}, ‖c ξ‖ := by simp [hgn]
      _ ≤ ε := hF.le
  have hA : ∀ R : ℝ, 0 < R → ‖∑ ξ ∈ F, c ξ * ∏ j, avg R ((lam ξ - lam ξ₀) j)‖ ≤ ε := by
    intro R hR
    haveI := rho_prob hR
    have hint : ∫ t, ∑ ξ ∈ F, g ξ t ∂(Measure.pi fun _ : Fin N => rho R)
        = ∑ ξ ∈ F, c ξ * ∏ j, avg R ((lam ξ - lam ξ₀) j) := by
      rw [integral_finset_sum]
      · refine Finset.sum_congr rfl fun ξ _ => ?_
        simp only [g]
        rw [integral_const_mul, integral_chr hR]
      · intro ξ _
        exact Integrable.of_bound
          ((continuous_const.mul (continuous_chr _)).aestronglyMeasurable) ‖c ξ‖
          (Eventually.of_forall fun t => (hgn ξ t).le)
    rw [← hint]
    calc _ ≤ ε * (Measure.pi fun _ : Fin N => rho R).real Set.univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall hbound)
      _ = ε := by simp
  have hlim : Tendsto (fun R : ℝ => ∑ ξ ∈ F, c ξ * ∏ j, avg R ((lam ξ - lam ξ₀) j)) atTop
      (𝓝 (c ξ₀)) := by
    have := tendsto_finset_sum F fun ξ _ =>
      (tendsto_finset_prod Finset.univ fun j _ => tendsto_avg ((lam ξ - lam ξ₀) j)).const_mul (c ξ)
    convert this using 2
    simp_rw [prod_indicator_zero_eq_ite]
    rw [Finset.sum_eq_single ξ₀]
    · simp
    · intro ξ _ hξ
      rw [if_neg (sub_ne_zero.mpr (hinj.ne hξ)), mul_zero]
    · intro h; exact absurd hξ₀F h
  exact le_of_tendsto hlim.norm (by
    filter_upwards [eventually_gt_atTop 0] with R hR using hA R hR)

end GlobalTheory.ExpSumUniq
