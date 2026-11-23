import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcE

noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalc2H

open DCalcH DCalcBH DCalcDH DCalcEH

variable {m n : ℕ}

theorem hasDeriv (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (t : ℝ) :
    HasDerivAt (fun t => fF c X P u t) (fF c X (dil c X P) u t) t :=
  fF_hasDeriv c X P u t

theorem quot_le (c : ℝ) (X : Fin n → ℝ) (P : PX m n) (u : Fin m → Fin n → ℂ) (s B : ℝ)
    (hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ B) (h : ℝ) (hh : |h| ≤ 1) :
    ‖fF c X P u (s + h) - fF c X P u s‖ ≤ B * |h| := by
  have hcv : Convex ℝ (Set.Icc (s - 1) (s + 1)) := convex_Icc _ _
  have hs : s ∈ Set.Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hsh : s + h ∈ Set.Icc (s - 1) (s + 1) := by
    rw [abs_le] at hh; exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have := hcv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t => fF c X P u t)
    (fun t _ => (hasDeriv c X P u t).hasDerivWithinAt) hB hs hsh
  simpa [Real.norm_eq_abs] using this

theorem l2conv (c : ℝ) (hc : 0 < c) (X : Fin n → ℝ) (P : PX m n) (s : ℝ) :
    Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨K, a, hK, ha, hb⟩ := fF_bound c hc X (dil c X P) s
  suffices key : Tendsto (fun h : ℝ => ∫ u, ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2)
      (𝓝[≠] 0) (𝓝 (∫ _u : Fin m → Fin n → ℂ, (0 : ℝ))) by simpa using key
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun h => ?_
    refine Continuous.aestronglyMeasurable ?_
    have h1 := fF_cont c X P (s + h)
    have h2 := fF_cont c X P s
    have h3 := fF_cont c X (dil c X P) s
    fun_prop
  · have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| ≤ 1 ∧ h ≠ 0 := by
      refine (eventually_nhdsWithin_of_eventually_nhds ?_).and self_mem_nhdsWithin
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      exact hh.le
    filter_upwards [hev] with h ⟨hh, h0⟩
    refine Eventually.of_forall fun u => ?_
    have hB : ∀ t ∈ Set.Icc (s - 1) (s + 1), ‖fF c X (dil c X P) u t‖ ≤ K * Real.exp (-(a * sqN u)) := fun t ht => hb u t ht
    have hq := quot_le c X P u s _ hB h hh
    have hhpos : 0 < |h| := abs_pos.2 h0
    have e1 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ ≤ K * Real.exp (-(a * sqN u)) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hhpos]
      exact hq
    have e2 : ‖fF c X (dil c X P) u s‖ ≤ K * Real.exp (-(a * sqN u)) := hb u s ⟨by linarith, by linarith⟩
    have e3 : ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ≤ 2 * K * Real.exp (-(a * sqN u)) := by
      calc _ ≤ ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ)‖ + ‖fF c X (dil c X P) u s‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖(fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s‖ ^ 2
        ≤ (2 * K * Real.exp (-(a * sqN u))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
      _ = (2 * K) ^ 2 * Real.exp (-(2 * a * sqN u)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  · exact (integrable_gauss (2 * a) (by positivity)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have : Tendsto (fun h : ℝ => (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s) (𝓝[≠] 0) (𝓝 0) := by
      have h2 := (hasDeriv c X P u s).tendsto_slope_zero
      have h3 := h2.sub_const (fF c X (dil c X P) u s)
      rw [sub_self] at h3
      refine h3.congr' (Eventually.of_forall fun h => ?_)
      show h⁻¹ • (fF c X P u (s + h) - fF c X P u s) - fF c X (dil c X P) u s =
        (fF c X P u (s + h) - fF c X P u s) / (h : ℂ) - fF c X (dil c X P) u s
      rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
    have := (this.norm).pow 2
    simpa using this

end DCalc2H

end PositivityTheory.Rg.Sw.Glob

end
