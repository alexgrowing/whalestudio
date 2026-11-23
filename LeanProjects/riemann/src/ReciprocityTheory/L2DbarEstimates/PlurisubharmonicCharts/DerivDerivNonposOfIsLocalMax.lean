import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

open Complex ComplexConjugate Filter Topology

namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative

open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} (hmax : IsLocalMax g 0)
    (hd : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ g t) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  have hd2 : DifferentiableAt ℝ (deriv g) 0 := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpos
    exact lt_irrefl _ hpos
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd2.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < slope (deriv g) 0 t := hslope.eventually (lt_mem_nhds hpos)
  rw [eventually_nhdsWithin_iff] at hev
  have hmax' : ∀ᶠ y in 𝓝 (0:ℝ), g y ≤ g 0 := hmax
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp ((hev.and hd).and hmax')
  have ht : 0 < ε / 2 := half_pos hε
  have hdist : ∀ y ∈ Set.Icc (0:ℝ) (ε / 2), dist y 0 < ε := by
    intro y hy
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  have hcont : ContinuousOn g (Set.Icc 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y hy)).1.2).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (Set.Ioo 0 (ε / 2)) := fun y hy =>
    ((hball (hdist y (Set.Ioo_subset_Icc_self hy))).1.2).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope g ht hcont hdiffOn
  have hcpos : 0 < deriv g c := by
    have h := (hball (hdist c (Set.Ioo_subset_Icc_self hc))).1.1
      (Set.mem_compl_singleton_iff.mpr hc.1.ne')
    simp only [slope_def_field, h0, sub_zero] at h
    exact (div_pos_iff_of_pos_right hc.1).mp h
  rw [hcd, sub_zero] at hcpos
  have hgt := (div_pos_iff_of_pos_right ht).mp hcpos
  have hle := (hball (hdist (ε / 2) ⟨ht.le, le_rfl⟩)).2
  linarith

private theorem differentiableAt_fderiv_of_contDiffAt_two' {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt (by norm_num)

set_option maxHeartbeats 400000 in

theorem snd_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (u : V n) : fderiv ℝ (fderiv ℝ f) x u u ≤ 0 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hγd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • u) u t := fun t => by
    simpa using ((hasDerivAt_id' t).smul_const u).const_add x
  have hγ : Tendsto (fun t : ℝ => x + t • u) (𝓝 0) (𝓝 x) := by
    have h := (hγd 0).continuousAt.tendsto
    simpa using h
  have hev := hγ.eventually (ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf)
  have hgd : ∀ t : ℝ, DifferentiableAt ℝ f (x + t • u) →
      HasDerivAt (fun t : ℝ => f (x + t • u)) (fderiv ℝ f (x + t • u) u) t :=
    fun t ht => ht.hasFDerivAt.comp_hasDerivAt t (hγd t)
  have hg : IsLocalMax (fun t : ℝ => f (x + t • u)) 0 := by
    show ∀ᶠ t in 𝓝 (0:ℝ), f (x + t • u) ≤ f (x + (0:ℝ) • u)
    filter_upwards [hγ.eventually (show ∀ᶠ y in 𝓝 x, f y ≤ f x from hmax)] with t ht
    simpa using ht
  have hdg : ∀ᶠ t in 𝓝 (0:ℝ), DifferentiableAt ℝ (fun t : ℝ => f (x + t • u)) t := by
    filter_upwards [hev] with t ht using (hgd t ht).differentiableAt
  have hEq : deriv (fun t : ℝ => f (x + t • u)) =ᶠ[𝓝 0] fun t => fderiv ℝ f (x + t • u) u := by
    filter_upwards [hev] with t ht using (hgd t ht).deriv
  have hφ : HasFDerivAt (fun y => fderiv ℝ f y u) ((fderiv ℝ (fderiv ℝ f) x).flip u) (x + (0:ℝ) • u) := by
    rw [zero_smul, add_zero]
    exact (hD.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).congr_fderiv (by ext b; simp)
  have h3 := hφ.comp_hasDerivAt (0:ℝ) (hγd 0)
  have h4 : ((fderiv ℝ (fderiv ℝ f) x).flip u) u = fderiv ℝ (fderiv ℝ f) x u u :=
    ContinuousLinearMap.flip_apply _ _ _
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • u) u) (fderiv ℝ (fderiv ℝ f) x u u) 0 := by
    rw [← h4]
    exact h3
  have h := deriv_deriv_nonpos_of_isLocalMax hg hdg
  rwa [hEq.deriv_eq, h2.deriv] at h

private theorem wirtinger_wirtingerBar_ofReal_lemma_2 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wd n j (ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ))) x =
      (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hψ : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, HasFDerivAt (fun y => ((fderiv ℝ f y a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip a)) x := by
    intro a
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y a) ((fderiv ℝ (fderiv ℝ f) x).flip a) x :=
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).congr_fderiv (by ext b; simp)
    exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hG : HasFDerivAt (fun y => (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)))
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (ReciprocityTheory.L2DbarEstimates.bas n k)) +
        I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (I • ReciprocityTheory.L2DbarEstimates.bas n k)))) x :=
    ((hψ (ReciprocityTheory.L2DbarEstimates.bas n k)).add ((hψ (I • ReciprocityTheory.L2DbarEstimates.bas n k)).const_mul I)).const_mul (2⁻¹ : ℂ)
  have hE : ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ)) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) := by
    filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
    rw [ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, div_eq_inv_mul]
  rw [ReciprocityTheory.L2DbarEstimates.wd_congr hE, ReciprocityTheory.L2DbarEstimates.wd, hG.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  push_cast
  linear_combination
    (-((fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) / 4) * I_sq

private theorem euclideanLeviForm_ofReal_eq_lemma_3 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun y => (f y : ℂ)) x ξ =
      ∑ j, ∑ k, (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 *
          ξ j * conj (ξ k) := by
  simp only [ReciprocityTheory.L2DbarEstimates.leviV, wirtinger_wirtingerBar_ofReal_lemma_2 hf]

private theorem re_div_four_mul_mul_conj_mul_four (P Q : ℝ) (z w : ℂ) :
    (((P : ℂ) + I * (Q : ℂ)) / 4 * z * conj w).re * 4 =
      P * (z.re * w.re + z.im * w.im) - Q * (z.im * w.re - z.re * w.im) := by
  have h4 : ((P : ℂ) + I * (Q : ℂ)) / 4 = ((P / 4 : ℝ) : ℂ) + I * ((Q / 4 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h4]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem bilinear_apply_sum_sum (T : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℝ) (v w : Fin n → ReciprocityTheory.L2DbarEstimates.V n) :
    T (∑ j, v j) (∑ k, w k) = ∑ j, ∑ k, T (v j) (w k) := by
  have h : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, T (∑ j, v j) a = ∑ j, T (v j) a := fun a => by
    rw [map_sum, ContinuousLinearMap.sum_apply]
  rw [h]
  exact Finset.sum_congr rfl fun j _ => map_sum (T (v j)) w Finset.univ

theorem leviV_re_eq {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (f y : ℂ)) x ξ).re * 4 =
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k)))
          (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k))) +
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k))
          (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k)) := by
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hf, bilinear_apply_sum_sum, bilinear_apply_sum_sum]
  simp only [Complex.re_sum, Finset.sum_mul, re_div_four_mul_mul_conj_mul_four]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem leviV_re_nonpos_of_isLocalMax {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hmax : IsLocalMax f x) (ξ : Fin n → ℂ) : (leviV n (fun y => (f y : ℂ)) x ξ).re ≤ 0 := by
  have h := leviV_re_eq hf ξ
  have h1 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • ReciprocityTheory.L2DbarEstimates.bas n k + (ξ k).im • (I • ReciprocityTheory.L2DbarEstimates.bas n k)))
  have h2 := snd_nonpos_of_isLocalMax hf hmax
    (∑ k, ((ξ k).re • (I • ReciprocityTheory.L2DbarEstimates.bas n k) - (ξ k).im • ReciprocityTheory.L2DbarEstimates.bas n k))
  linarith

theorem leviV_ofReal_add {f g : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((f y + g y : ℝ) : ℂ)) x ξ =
      leviV n (fun y => (f y : ℂ)) x ξ + leviV n (fun y => (g y : ℂ)) x ξ := by
  have hfg : ContDiffAt ℝ 2 (fun y => f y + g y) x := hf.add hg
  have hT : fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
    have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf,
        ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hg] with y hfy hgy
      exact fderiv_add hfy hgy
    rw [hev.fderiv_eq]
    exact fderiv_add (differentiableAt_fderiv_of_contDiffAt_two' hf)
      (differentiableAt_fderiv_of_contDiffAt_two' hg)
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hfg, euclideanLeviForm_ofReal_eq_lemma_3 hf, euclideanLeviForm_ofReal_eq_lemma_3 hg, hT]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.add_apply]
  push_cast
  ring

theorem leviV_ofReal_const_mul {f : V n → ℝ} {x : V n} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y : ℝ) : ℂ)) x ξ = (c : ℂ) * leviV n (fun y => (f y : ℂ)) x ξ := by
  have hcf : ContDiffAt ℝ 2 (fun y => c * f y) x := contDiffAt_const.mul hf
  have hT : fderiv ℝ (fderiv ℝ (fun y => c * f y)) x = c • fderiv ℝ (fderiv ℝ f) x := by
    have hev : fderiv ℝ (fun y => c * f y) =ᶠ[𝓝 x] fun y => c • fderiv ℝ f y := by
      filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
      exact fderiv_const_mul hy c
    rw [hev.fderiv_eq]
    exact fderiv_const_smul (differentiableAt_fderiv_of_contDiffAt_two' hf) c
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hcf, euclideanLeviForm_ofReal_eq_lemma_3 hf, hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
