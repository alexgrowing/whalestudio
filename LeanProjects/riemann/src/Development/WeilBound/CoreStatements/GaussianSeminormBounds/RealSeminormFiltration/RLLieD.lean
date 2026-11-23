import Mathlib

noncomputable section

open Filter Topology MeasureTheory

namespace PositivityTheory.RL.Delta

open Complex
open scoped Real ContDiff

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x := by
  intro n f hf h0
  have hD : ∀ v : Fin n → ℝ, ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) := fun v =>
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hmean : ∀ h : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ h →
      ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∫ s in (0 : ℝ)..1, h (s • x)) := by
    intro h hh
    let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    have hk : IsCompact (Metric.closedBall (0 : ℝ) 2) := isCompact_closedBall _ _
    have hloc : MeasureTheory.LocallyIntegrable
        ((Set.Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) MeasureTheory.volume :=
      (MeasureTheory.locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ioc
    have hsm : ContDiffOn ℝ ∞ (Function.uncurry fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p))
        (Set.univ ×ˢ Set.univ) := by
      refine ContDiff.contDiffOn ?_
      exact (b.contDiff.comp contDiff_snd).smul (hh.comp (contDiff_snd.neg.smul contDiff_fst))
    have key := MeasureTheory.contDiffOn_convolution_right_with_param_comp (n := (⊤ : ℕ∞))
      (μ := MeasureTheory.volume) (ContinuousLinearMap.lsmul ℝ ℝ) (s := Set.univ)
      (v := fun _ : Fin n → ℝ => (0 : ℝ)) contDiffOn_const
      (g := fun (p : Fin n → ℝ) (t : ℝ) => b t • h ((-t) • p)) isOpen_univ hk
      (fun p t _ ht => by
        have : b t = 0 := image_eq_zero_of_notMem_tsupport (by rw [b.tsupport_eq]; exact ht)
        simp [this]) hloc hsm
    rw [contDiffOn_univ] at key
    convert key using 2 with x
    rw [MeasureTheory.convolution_def, intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
    · have : b (-t) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, norm_neg, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2)
      simp [ht, this]
    · simp [ht]
  refine ⟨fun i x => ∫ s in (0 : ℝ)..1, fderiv ℝ f (s • x) (Pi.single i 1),
    fun i => hmean _ (hD _), fun x => ?_⟩
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (s • x) x) s := by
    intro s _
    have := (hd (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
    rw [one_smul] at this
    exact this
  have hcv : ∀ v : Fin n → ℝ, Continuous (fun s : ℝ => fderiv ℝ f (s • x) v) := fun v =>
    (hD v).continuous.comp (continuous_id.smul continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcv x).intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, h0, sub_zero] at hftc
  rw [← hftc]
  have hx : ∀ s : ℝ, fderiv ℝ f (s • x) x =
      ∑ i, (x i : ℂ) * fderiv ℝ f (s • x) (Pi.single i 1) := by
    intro s
    calc fderiv ℝ f (s • x) x = fderiv ℝ f (s • x) (∑ i, x i • (Pi.single i 1 : Fin n → ℝ)) :=
          congrArg (fderiv ℝ f (s • x)) (pi_eq_sum_univ' x)
      _ = _ := by simp only [map_sum, map_smul, Complex.real_smul]
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · exact fun i _ => (continuous_const.mul (hcv _)).intervalIntegrable 0 1

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} := by
  intro n f
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  set u : (Fin n → ℝ) → ℝ := (b : (Fin n → ℝ) → ℝ) - fun _ => 1 with hu
  have hus : ContDiff ℝ ∞ u := b.contDiff.sub contDiff_const
  have hub : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i u x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      ((b.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top))
    refine ⟨C + 1, by linarith [(norm_nonneg _).trans (hC 0)], fun x => ?_⟩
    rw [hu, iteratedFDeriv_sub b.contDiff contDiff_const]
    refine (norm_sub_le _ _).trans (add_le_add (hC x) ?_)
    by_cases hi : i = 0
    · subst hi; simp
    · rw [iteratedFDeriv_const_of_ne hi]; simp
  choose C hC0 hC using hub
  let L : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := fun R =>
    ((R : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ _
  have hL : ∀ R x, ‖L R x‖ = ‖x‖ / ((R : ℝ) + 1) := by
    intro R x
    show ‖((R : ℝ) + 1)⁻¹ • x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (by positivity), div_eq_inv_mul]
  have hL1 : ∀ R, ‖L R‖ ≤ 1 := fun R =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [hL, one_mul]
      exact div_le_self (norm_nonneg _) (by linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
  have hsm : ∀ R, ContDiff ℝ ∞ (fun x => b (L R x) • f x) := fun R =>
    (b.contDiff.comp (L R).contDiff).smul (f.smooth ⊤)
  have hcs : ∀ R, HasCompactSupport (fun x => b (L R x) • f x) := by
    intro R
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * ((R : ℝ) + 1))) ?_
    intro x hx
    rw [mem_closedBall_zero_iff, not_le] at hx
    rw [b.zero_of_le_dist, zero_smul]
    rw [dist_zero_right, hL, le_div_iff₀ (by positivity)]
    exact hx.le
  refine mem_closure_of_tendsto (b := Filter.atTop) (f := fun R : ℕ => (hcs R).toSchwartzMap (hsm R))
    ?_ (Filter.Eventually.of_forall hcs)
  rw [(schwartz_withSeminorms ℂ (Fin n → ℝ) ℂ).tendsto_nhds]
  rintro ⟨k, j⟩ ε hε
  set M : ℝ := ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * C i * SchwartzMap.seminorm ℂ (k + 1) (j - i) f with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i)) (apply_nonneg _ _)
  have hlim : Filter.Tendsto (fun R : ℕ => M * (1 / ((R : ℝ) + 1))) Filter.atTop (nhds (M * 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with R hR
  refine lt_of_le_of_lt ?_ hR
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine SchwartzMap.seminorm_le_bound ℂ k j _ (by positivity) fun x => ?_
  have e : (⇑((hcs R).toSchwartzMap (hsm R) - f) : (Fin n → ℝ) → ℂ) =
      fun x => (u ∘ L R) x • f x := by
    funext y
    show b (L R y) • f y - f y = (b (L R y) - 1) • f y
    rw [sub_smul, one_smul]
  rw [e]
  have hR0 : (0 : ℝ) < R + 1 := by positivity
  by_cases hx : ‖x‖ < R + 1
  · have hz : (fun x => (u ∘ L R) x • f x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have : b (L R y) = 1 := b.one_of_mem_closedBall (by
        rw [mem_closedBall_zero_iff, hL]
        exact (div_le_one hR0).2 (le_of_lt hy))
      show (b (L R y) - 1) • f y = 0
      rw [this, sub_self, zero_smul]
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero, mul_zero]
    positivity
  · rw [not_lt] at hx
    have h1 := norm_iteratedFDeriv_smul_le (hus.comp (L R).contDiff) (f.smooth ⊤) x (n := j)
      (by exact_mod_cast le_top)
    rw [mul_one_div, le_div_iff₀ hR0]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun x => (u ∘ L R) x • f x) x‖ * ((R : ℝ) + 1)
        ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖) * ‖x‖ := by
          gcongr
      _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ *
          (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (j - i) f x‖) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ M := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h2 : ‖iteratedFDeriv ℝ i (u ∘ L R) x‖ ≤ C i := by
            rw [(L R).iteratedFDeriv_comp_right hus x (by exact_mod_cast le_top)]
            refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
            refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hC i _)
            exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL1 R)
          have h3 := SchwartzMap.le_seminorm ℂ (k + 1) (j - i) f x
          have h4 := hC0 i
          gcongr

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t := by
  set E : ℂ → ℂ := fun z => cexp (2 * π * I * z) with hE
  have hEd : Differentiable ℂ E := by rw [hE]; fun_prop
  have hd : Differentiable ℂ (dslope E 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).2 hEd.differentiableOn
  have hc : ContDiff ℝ ∞ (fun t : ℝ => dslope E 0 (t : ℂ)) :=
    (hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  have hmul : ∀ t : ℝ, (t : ℂ) * dslope E 0 t = cexp (2 * π * I * t) - 1 := by
    intro t
    have := sub_smul_dslope E 0 (t : ℂ)
    simpa [hE] using this
  have hne : ∀ t ∈ Metric.ball (0 : ℝ) 1, dslope E 0 (t : ℂ) ≠ 0 := by
    intro t ht h0
    by_cases h : t = 0
    · subst h
      have hD : HasDerivAt E (cexp (2 * π * I * 0) * (2 * π * I * 1)) 0 :=
        ((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).cexp
      rw [Complex.ofReal_zero, dslope_same, hD.deriv] at h0
      simp [Real.pi_ne_zero] at h0
    · have h1 := hmul t
      rw [h0, mul_zero, eq_comm, sub_eq_zero, Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2 : (t : ℂ) = k := by
        have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ h3
        rw [hk]; ring
      have h4 : t = k := by exact_mod_cast h2
      rw [mem_ball_zero_iff, Real.norm_eq_abs, h4] at ht
      have h5 : |k| < 1 := by exact_mod_cast ht
      have h6 : k = 0 := Int.abs_lt_one_iff.1 h5
      exact h (by rw [h4, h6]; simp)
  refine ⟨fun t => (dslope E 0 (t : ℂ))⁻¹, hc.contDiffOn.inv hne, fun t ht => ?_⟩
  rw [← hmul t, mul_assoc, mul_inv_cancel₀ (hne t ht), mul_one]

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x := by
  obtain ⟨q, hq, hq'⟩ := exists_quot
  obtain ⟨h, hh, hh'⟩ := hadamard_lemma n f (f.smooth ⊤) h0
  have hK : IsCompact (tsupport (f : (Fin n → ℝ) → ℂ)) :=
    (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset (isClosed_tsupport _)
      (hf.trans Metric.ball_subset_closedBall)
  obtain ⟨r, hr, hr'⟩ := exists_lt_subset_ball (isClosed_tsupport _) hf
  set r' : ℝ := max r (1 / 2) with hr'def
  have hr1 : r' < 1 := max_lt hr (by norm_num)
  have hr0 : 0 < r' := lt_max_of_lt_right (by norm_num)
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨r', (r' + 1) / 2, hr0, by linarith⟩
  have hbs : tsupport (b : (Fin n → ℝ) → ℝ) ⊆ Metric.ball 0 1 := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by show (r' + 1) / 2 < 1; linarith)
  have hcoord : ∀ (i : Fin n), ∀ x ∈ Metric.ball (0 : Fin n → ℝ) 1, x i ∈ Metric.ball (0 : ℝ) 1 := by
    intro i x hx
    rw [mem_ball_zero_iff] at hx ⊢
    exact (norm_le_pi_norm x i).trans_lt hx
  have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) := by
    intro i
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_of_tsupport fun x hx => ?_
    rw [contMDiffAt_iff_contDiffAt]
    have hx' : x ∈ Metric.ball (0 : Fin n → ℝ) 1 := hbs (tsupport_smul_subset_left _ _ hx)
    refine b.contDiff.contDiffAt.smul (ContDiffAt.mul ?_ (hh i).contDiffAt)
    exact ContDiffAt.comp x (g := q) (f := fun x : Fin n → ℝ => x i)
      (hq.contDiffAt (Metric.isOpen_ball.mem_nhds (hcoord i x hx'))) (contDiffAt_apply ℝ ℝ i x)
  have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => b x • (q (x i) * h i x)) :=
    fun i => b.hasCompactSupport.smul_right
  refine ⟨fun i => (hcs i).toSchwartzMap (hsm i), hcs, fun x => ?_⟩
  show f x = ∑ i, (cexp (2 * π * I * x i) - 1) * (b x • (q (x i) * h i x))
  have hb : f x = b x • f x := by
    by_cases hx : x ∈ tsupport (f : (Fin n → ℝ) → ℂ)
    · rw [b.one_of_mem_closedBall, one_smul]
      exact Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_max_left _ _) (hr' hx))
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
  by_cases hx : x ∈ Metric.ball (0 : Fin n → ℝ) 1
  · rw [hb, hh' x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← mul_assoc, ← hq' _ (hcoord i x hx)]
  · have : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hbs h)
    rw [hb, this]; simp

theorem zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]

theorem eq_delta (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this

theorem eq_delta' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]

end PositivityTheory.RL.Delta

end
