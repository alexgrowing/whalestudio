import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfG
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem wdb_contDiffOn (hU : IsOpen U) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g U) (k : Fin n) :
    ContDiffOn ℝ ∞ (wdb n k g) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (bas n k)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y (Complex.I • bas n k)) U :=
    hd.clm_apply contDiffOn_const
  show ContDiffOn ℝ ∞
    (fun y => (fderiv ℝ g y (bas n k) + Complex.I * fderiv ℝ g y (Complex.I • bas n k)) / 2) U
  exact (h1.add (contDiffOn_const.mul h2)).div_const 2

theorem wd_continuousOn (hU : IsOpen U) {h : V n → ℂ} (hh : ContDiffOn ℝ ∞ h U) (j : Fin n) :
    ContinuousOn (wd n j h) U := by
  have hd : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hh).2
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (bas n j)) U := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ h y (Complex.I • bas n j)) U :=
    hd.clm_apply contDiffOn_const
  show ContinuousOn
    (fun y => (fderiv ℝ h y (bas n j) - Complex.I * fderiv ℝ h y (Complex.I • bas n j)) / 2) U
  exact ((h1.sub (contDiffOn_const.mul h2)).div_const 2).continuousOn

theorem leviV_scale (g : V n → ℂ) (z : V n) (t : ℝ) (ξ : Fin n → ℂ) :
    (leviV n g z (fun j => (t : ℂ) * ξ j)).re = t ^ 2 * (leviV n g z ξ).re := by
  have h : leviV n g z (fun j => (t : ℂ) * ξ j) = ((t ^ 2 : ℝ) : ℂ) * leviV n g z ξ := by
    simp only [leviV, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]

theorem levi_unif (hU : IsOpen U) {g : V n → ℝ} (hg : ContDiffOn ℝ ∞ g U) {K : Set (V n)}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hpos : ∀ z ∈ K, ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => (g w : ℂ)) z ξ).re) :
    ∃ c > 0, ∀ z ∈ K, ∀ ξ : Fin n → ℂ,
      c * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (g w : ℂ)) z ξ).re := by
  have hG : ContDiffOn ℝ ∞ (fun w => (g w : ℂ)) U :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hg).congr (fun x _ => by simp)
  have hcont : ContinuousOn
      (fun p : V n × (Fin n → ℂ) => (leviV n (fun w => (g w : ℂ)) p.1 p.2).re)
      (K ×ˢ sphere (0 : Fin n → ℂ) 1) := by
    refine Complex.continuous_re.comp_continuousOn
      (f := fun p : V n × (Fin n → ℂ) => leviV n (fun w => (g w : ℂ)) p.1 p.2) ?_
    show ContinuousOn (fun p : V n × (Fin n → ℂ) => ∑ j, ∑ k,
      wd n j (wdb n k (fun w => (g w : ℂ))) p.1 * p.2 j * (starRingEnd ℂ) (p.2 k)) _
    refine continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun k _ => ?_
    have hw : ContinuousOn
        (fun p : V n × (Fin n → ℂ) => wd n j (wdb n k (fun w => (g w : ℂ))) p.1)
        (K ×ˢ sphere (0 : Fin n → ℂ) 1) :=
      (wd_continuousOn hU (wdb_contDiffOn hU hG k) j).comp continuousOn_fst
        (fun p hp => hKU hp.1)
    refine (hw.mul ?_).mul ?_
    · exact ((continuous_apply j).comp continuous_snd).continuousOn
    · exact (Complex.continuous_conj.comp ((continuous_apply k).comp continuous_snd)).continuousOn
  by_cases hne : (K ×ˢ sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ :=
      (hK.prod (isCompact_sphere (0 : Fin n → ℂ) 1)).exists_isMinOn hne hcont
    have hp0ne : p0.2 ≠ 0 := by
      intro h
      have h1 := hp0.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
    have hc0 : 0 < (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re := hpos p0.1 hp0.1 p0.2 hp0ne
    refine ⟨(leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1),
      div_pos hc0 (by positivity), ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      have hη : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      have hm : (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re
          ≤ (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        isMinOn_iff.1 hmin (z, ‖ξ‖⁻¹ • ξ) (Set.mk_mem_prod hz hη)
      have hξη : (fun j => ((‖ξ‖ : ℝ) : ℂ) * (‖ξ‖⁻¹ • ξ) j) = ξ := by
        funext j
        rw [Pi.smul_apply, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hr.ne', Complex.ofReal_one, one_mul]
      have key : (leviV n (fun w => (g w : ℂ)) z ξ).re
          = ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re :=
        (congrArg (fun v => (leviV n (fun w => (g w : ℂ)) z v).re) hξη.symm).trans
          (leviV_scale (fun w => (g w : ℂ)) z ‖ξ‖ (‖ξ‖⁻¹ • ξ))
      have hsum : ∑ j, ‖ξ j‖ ^ 2 ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by
        calc ∑ j, ‖ξ j‖ ^ 2 ≤ ∑ _j : Fin n, ‖ξ‖ ^ 2 :=
              Finset.sum_le_sum fun j _ => by gcongr; exact norm_le_pi_norm ξ j
          _ = (n : ℝ) * ‖ξ‖ ^ 2 := by simp
          _ ≤ ((n : ℝ) + 1) * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
      rw [key]
      calc (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1) * ∑ j, ‖ξ j‖ ^ 2
          ≤ (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re / ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * ‖ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum (div_pos hc0 (by positivity)).le
        _ = (leviV n (fun w => (g w : ℂ)) p0.1 p0.2).re * ‖ξ‖ ^ 2 := by
            rw [← mul_assoc, div_mul_cancel₀ _ (by positivity : ((n : ℝ) + 1) ≠ 0)]
        _ ≤ ‖ξ‖ ^ 2 * (leviV n (fun w => (g w : ℂ)) z (‖ξ‖⁻¹ • ξ)).re := by
            nlinarith [hm, sq_nonneg ‖ξ‖]
  · refine ⟨1, one_pos, ?_⟩
    intro z hz ξ
    by_cases hξ : ξ = 0
    · subst hξ
      simp [leviV]
    · exfalso
      apply hne
      refine ⟨(z, ‖ξ‖⁻¹ • ξ), hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_iff.2 hξ).ne']

private theorem eq_zero_on_ball_of_eventuallyEq_zero {F : V n → ℂ} {w : V n} {ρ : ℝ}
    (hF : DifferentiableOn ℂ F (ball w ρ)) (h0 : F =ᶠ[𝓝 w] 0) :
    ∀ y ∈ ball w ρ, F y = 0 := by
  intro y hy
  by_cases hyw : y = w
  · subst hyw
    exact h0.self_of_nhds
  have hρ : 0 < ρ := pos_of_mem_ball hy
  have hd : 0 < ‖y - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
  have hyd : ‖y - w‖ < ρ := by rw [← dist_eq_norm]; exact hy
  have hmaps : Set.MapsTo (fun t : ℂ => w + t • (y - w)) (ball (0 : ℂ) (ρ / ‖y - w‖)) (ball w ρ) := by
    intro t ht
    rw [mem_ball, dist_zero_right, lt_div_iff₀ hd] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hLd : Differentiable ℂ (fun t : ℂ => w + t • (y - w)) := by fun_prop
  have hg : DifferentiableOn ℂ (fun t : ℂ => F (w + t • (y - w))) (ball (0 : ℂ) (ρ / ‖y - w‖)) :=
    hF.comp hLd.differentiableOn hmaps
  have hT : Filter.Tendsto (fun t : ℂ => w + t • (y - w)) (𝓝 0) (𝓝 w) := by
    have h := hLd.continuous.tendsto 0
    rwa [zero_smul, add_zero] at h
  have hg0 : (fun t : ℂ => F (w + t • (y - w))) =ᶠ[𝓝 0] 0 := h0.comp_tendsto hT
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (ρ / ‖y - w‖) := by
    rw [mem_ball, dist_zero_right, norm_one, lt_div_iff₀ hd, one_mul]
    exact hyd
  have h2 := (hg.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) _).isPreconnected (mem_ball_self (div_pos hρ hd)) hg0 h1
  simpa using h2

theorem ident_preconn (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ}
    (hF : DifferentiableOn ℂ F U) {a : V n} (ha : a ∈ U) (h0 : F =ᶠ[𝓝 a] 0) : Set.EqOn F 0 U := by
  have hS : IsOpen {z : V n | F =ᶠ[𝓝 z] 0} := isOpen_setOf_eventually_nhds
  have hcl : closure {z : V n | F =ᶠ[𝓝 z] 0} ∩ U ⊆ {z : V n | F =ᶠ[𝓝 z] 0} := by
    rintro z ⟨hzc, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hzU
    obtain ⟨w, hwS, hzw⟩ := Metric.mem_closure_iff.1 hzc (r / 2) (half_pos hr)
    have hsub : ball w (r / 2) ⊆ U := by
      intro y hy
      apply hrU
      rw [mem_ball] at hy ⊢
      calc dist y z ≤ dist y w + dist w z := dist_triangle _ _ _
        _ < r / 2 + r / 2 := by rw [dist_comm w z]; exact add_lt_add hy hzw
        _ = r := add_halves r
    have hzb : z ∈ ball w (r / 2) := by rw [mem_ball]; exact hzw
    have hw0 : F =ᶠ[𝓝 w] 0 := hwS
    show F =ᶠ[𝓝 z] 0
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb)
      (fun y hy => eq_zero_on_ball_of_eventuallyEq_zero (hF.mono hsub) hw0 y hy)
  have hUS := hc.subset_of_closure_inter_subset hS ⟨a, ha, h0⟩ hcl
  intro z hz
  have h' : F =ᶠ[𝓝 z] 0 := hUS hz
  exact h'.self_of_nhds

theorem hgn_of (hU : IsOpen U) (hc : IsPreconnected U) {F : V n → ℂ} (hF : DifferentiableOn ℂ F U)
    {a : V n} (ha : a ∈ U) (hne : ¬ F =ᶠ[𝓝 a] 0) :
    ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, F y ≠ 0 := by
  intro W hW hWU hWne
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy⟩ := hWne
  have hy0 : F =ᶠ[𝓝 y] 0 := Filter.eventually_of_mem (hW.mem_nhds hy) (fun x hx => hcon x hx)
  have hall := ident_preconn hU hc hF (hWU hy) hy0
  exact hne (Filter.eventually_of_mem (hU.mem_nhds ha) (fun x hx => hall hx))

theorem ker_bot_of_det {f' : V n →L[ℂ] V n} (hdet : f'.det ≠ 0) :
    LinearMap.ker (f' : V n →ₗ[ℂ] V n) = ⊥ := by
  exact (LinearMap.isUnit_iff_ker_eq_bot _).1
    ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))

theorem iso_zero {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0) (hdet : f'.det ≠ 0)
    (h0 : f 0 = 0) : ∃ δ > 0, ∀ y ∈ closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  obtain ⟨K, -, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (ker_bot_of_det hdet)
  have hev : ∀ᶠ z in 𝓝[≠] (0 : V n), f z ≠ 0 := hf.eventually_ne (c := 0) ⟨K, hK⟩
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, half_pos hε, fun y hy hy0 => ?_⟩
  by_contra hne
  have hyd : dist y 0 < ε := lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hε)
  exact hball hyd hne hy0

theorem coord_ne_of_det {f : V n → V n} (hn : 1 ≤ n) (hdet : (fderiv ℂ f 0).det ≠ 0) :
    ∃ k : Fin n, ¬ (fun z => f z k) =ᶠ[𝓝 0] 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ᶠ z in 𝓝 (0 : V n), ∀ k : Fin n, f z k = 0 := by
    rw [Filter.eventually_all]
    intro k
    exact hcon k
  have hf0 : f =ᶠ[𝓝 0] 0 := by
    filter_upwards [hall] with z hz
    ext k
    simpa using hz k
  have hd : fderiv ℂ f 0 = 0 := by
    rw [hf0.fderiv_eq]
    simp
  apply hdet
  rw [hd]
  have hfr : Module.finrank ℂ (V n) = n := finrank_euclideanSpace_fin
  show LinearMap.det ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) = 0
  rw [ContinuousLinearMap.coe_zero, LinearMap.det_zero, hfr]
  exact zero_pow (by omega)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
