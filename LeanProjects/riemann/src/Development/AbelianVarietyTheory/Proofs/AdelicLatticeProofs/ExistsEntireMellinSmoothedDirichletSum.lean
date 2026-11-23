import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology

namespace GlobalTheory.SmoothedSumMellin

lemma weight_bound {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ}
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y → ‖wt y‖ ≤ M * y ^ (-2 : ℝ) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0 * (max b 1) ^ 2, by positivity, fun y hy => ?_⟩
  by_cases h0 : wt y = 0
  · rw [h0, norm_zero]
    positivity
  obtain ⟨hay, hyb⟩ := hs y h0
  have hB : ‖wt y‖ ≤ max C 0 := (hC y ⟨hay, hyb⟩).trans (le_max_left _ _)
  rw [Real.rpow_neg hy.le, Real.rpow_two]
  have hyb' : y ^ 2 ≤ (max b 1) ^ 2 := pow_le_pow_left₀ hy.le (hyb.trans (le_max_left _ _)) 2
  have h1 : 1 ≤ (max b 1) ^ 2 * (y ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    linarith
  calc ‖wt y‖ ≤ max C 0 * 1 := by rw [mul_one]; exact hB
    _ ≤ max C 0 * ((max b 1) ^ 2 * (y ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    _ = _ := by ring

lemma weight_mellinConvergent {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ} (ha : 0 < a)
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) (s : ℂ) : MellinConvergent wt s := by
  have hev0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), wt t = 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    by_contra h
    exact absurd (hs t h).1 (not_le.2 ht.2)
  have hevT : ∀ᶠ t in atTop, wt t = 0 := by
    filter_upwards [eventually_gt_atTop b] with t ht
    by_contra h
    exact absurd (hs t h).2 (not_le.2 ht)
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _)
    ((Asymptotics.isBigO_zero _ _).congr' (hevT.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)
    ((Asymptotics.isBigO_zero _ _).congr' (hev0.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)

lemma continuousOn_sum {ι : Type} {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} (hc : Continuous wt)
    {α β : ℝ} (hs : ∀ y, wt y ≠ 0 → α ≤ y ∧ y ≤ β) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-2 : ℝ)) :
    ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := weight_bound hc hs
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  have hcont : ContinuousOn (fun t : ℝ => ∑' i, a i * wt (t * N i)) (Ioi (t0 / 2)) := by
    refine continuousOn_tsum (u := fun i => ‖a i‖ * N i ^ (-2 : ℝ) * (M * (t0 / 2) ^ (-2 : ℝ)))
      (fun i => (continuous_const.mul (hc.comp (continuous_id.mul continuous_const))).continuousOn)
      (hsum.mul_right _) ?_
    intro i t ht
    have ht' : t0 / 2 < t := ht
    by_cases hai : a i = 0
    · simp [hai]
    have hNi : (1 : ℝ) ≤ N i := hN i hai
    have htN : 0 < t * N i := mul_pos (by linarith) (by linarith)
    rw [norm_mul]
    have h1 := hM (t * N i) htN
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : t ^ (-2 : ℝ) ≤ (t0 / 2) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) ht'.le (by norm_num)
    have hNn : 0 ≤ N i ^ (-2 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc ‖a i‖ * ‖wt (t * N i)‖ ≤ ‖a i‖ * (M * (t ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ ‖a i‖ * (M * ((t0 / 2) ^ (-2 : ℝ) * N i ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h2 hNn) hM0) (norm_nonneg _)
      _ = _ := by ring
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

lemma integral_norm_comp (wt : ℝ → ℂ) (s : ℂ) {n : ℝ} (hn : 0 < n) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖
      = n ^ (-s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
  have h1 : ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖ =
      ∫ t in Ioi (0 : ℝ), (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) (t * n) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, mul_div_cancel_right₀ t hn.ne']
    simp
  have h2 : ∫ t in Ioi (0 : ℝ), (t / n) ^ (s.re - 1) * ‖wt t‖ =
      n ^ (1 - s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Real.div_rpow ht'.le hn.le]
    have h3 : n ^ (1 - s.re) = (n ^ (s.re - 1))⁻¹ := by rw [← Real.rpow_neg hn.le, neg_sub]
    rw [h3]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  rw [h1, integral_comp_mul_right_Ioi (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) 0 hn, zero_mul]
  rw [h2, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn]
  congr 1
  ring

lemma mellin_sum {ι : Type} [Countable ι] {a : ι → ℂ} {N : ι → ℝ} {wt : ℝ → ℂ} {s : ℂ}
    (hw : MellinConvergent wt s) (hN : ∀ i, a i ≠ 0 → 1 ≤ N i)
    (hsum : Summable fun i => ‖a i‖ * N i ^ (-s.re)) :
    mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s
      = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) := by
  have hI : ∀ i, a i ≠ 0 → 0 < N i := fun i hi => by linarith [hN i hi]
  set I := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ with hIdef
  set G : ι → ℝ → ℂ := fun i t => (t : ℂ) ^ (s - 1) • (a i * wt (t * N i)) with hG
  have hGint : ∀ i, Integrable (G i) (volume.restrict (Ioi 0)) := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have hc : MellinConvergent (fun t => wt (t * N i)) s := by
        have := (MellinConvergent.comp_mul_left (f := wt) (s := s) (hI i hai)).2 hw
        simpa only [mul_comm] using this
      exact hc.const_smul (a i)
  have hGnorm : ∀ i, ∫ t in Ioi (0 : ℝ), ‖G i t‖ = ‖a i‖ * N i ^ (-s.re) * I := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∀ t, ‖G i t‖ = ‖a i‖ * ‖(t : ℂ) ^ (s - 1) • wt (t * N i)‖ := fun t => by
        simp only [hG, _root_.norm_smul, norm_mul]
        ring
      simp_rw [h1]
      rw [integral_const_mul, integral_norm_comp wt s (hI i hai)]
      ring
  have hsumG : Summable fun i => ∫ t in Ioi (0 : ℝ), ‖G i t‖ := by
    simp_rw [hGnorm]
    exact hsum.mul_right I
  have key := integral_tsum_of_summable_integral_norm hGint hsumG
  have hM : mellin (fun t : ℝ => ∑' i, a i * wt (t * N i)) s = ∫ t in Ioi (0 : ℝ), ∑' i, G i t := by
    rw [mellin]
    congr 1
    funext t
    simp only [hG, smul_eq_mul]
    rw [tsum_mul_left]
  have hGi : ∀ i, ∫ t in Ioi (0 : ℝ), G i t = a i * (N i : ℂ) ^ (-s) * mellin wt s := by
    intro i
    by_cases hai : a i = 0
    · simp [hG, hai]
    · have h1 : ∫ t in Ioi (0 : ℝ), G i t = a i * mellin (fun t => wt (t * N i)) s := by
        rw [mellin, ← integral_const_mul]
        congr 1
        funext t
        simp only [hG, smul_eq_mul]
        ring
      rw [h1, mellin_comp_mul_right wt s (hI i hai), smul_eq_mul, mul_assoc]
  rw [hM, ← key]
  simp_rw [hGi]
  rw [tsum_mul_right, mul_comm]

theorem exists_entire_mellin : ∀ (ι : Type) [Countable ι] (a : ι → ℂ) (N : ι → ℝ) (R : ℂ) (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → (∀ i, a i ≠ 0 → 1 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => ‖a i‖ * N i ^ (-σ)) → (∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' i, a i * wt (t * N i) - R / (t : ℂ)‖ ≤ C * t ^ A) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = R ∧ ∀ s : ℂ, 1 < s.re → Z s = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s)) := by
  intro ι _ a N R wt hwt hsupp0 hN hsum hasym
  obtain ⟨α, β, hα, hsupp⟩ := hsupp0
  have hc : Continuous wt := hwt.continuous
  set F : ℝ → ℂ := fun t => ∑' i, a i * wt (t * N i) with hF
  set G : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) with hG
  set H : ℝ → ℂ := fun t => F t - R * G t with hH
  have hFtop : ∀ t, max β 1 < t → F t = 0 := by
    intro t ht
    have h1 : ∀ i, a i * wt (t * N i) = 0 := by
      intro i
      by_cases hai : a i = 0
      · rw [hai, zero_mul]
      · have hNi := hN i hai
        have hw0 : wt (t * N i) = 0 := by
          by_contra h
          have h2 := (hsupp _ h).2
          have h3 : t ≤ t * N i := le_mul_of_one_le_right (by linarith [le_max_right β 1]) hNi
          linarith [le_max_left β 1]
        rw [hw0, mul_zero]
    simp only [hF, h1, tsum_zero]
  have hFc : ContinuousOn F (Ioi 0) := continuousOn_sum hc hsupp hN (hsum 2 (by norm_num))
  have hGc : ContinuousOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) := fun t ht =>
    (continuousAt_const.mul (ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt (x := t))
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 ht))).continuousWithinAt
  have hRGloc : LocallyIntegrableOn (fun t => R * G t) (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k hk hkc
    have h1 : IntegrableOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) k :=
      (hGc.mono hk).integrableOn_compact hkc
    have h2 := h1.indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
    refine h2.congr_fun (fun t _ => ?_) hkc.measurableSet
    simp only [hG, indicator]
    split_ifs <;> simp
  have hHloc : LocallyIntegrableOn H (Ioi 0) :=
    (hFc.locallyIntegrableOn measurableSet_Ioi).sub hRGloc
  have htop : ∀ c : ℝ, H =O[atTop] (· ^ c) := by
    intro c
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (max β 1)] with t ht
    have ht1 : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2, le_max_right β 1]
    simp only [hH, hFtop t ht, hG, Set.indicator_of_notMem ht1, mul_zero, sub_zero]
  have hbot : ∀ A : ℕ, H =O[𝓝[>] 0] (· ^ (A : ℝ)) := by
    intro A
    obtain ⟨C, hC⟩ := hasym A
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht0 : 0 < t := ht.1
    have hHt : H t = F t - R / t := by
      simp only [hH, hG, Set.indicator_of_mem ht, Complex.cpow_neg_one, div_eq_mul_inv]
    rw [hHt, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg ht0.le A)]
    exact hC t ht0 ht.2
  have hbot' : ∀ s : ℂ, ∃ b : ℝ, b < s.re ∧ H =O[𝓝[>] 0] (· ^ (-b)) := by
    intro s
    refine ⟨-((⌈-s.re⌉₊ + 1 : ℕ) : ℝ), ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil (-s.re)]
    · simpa only [neg_neg] using hbot (⌈-s.re⌉₊ + 1)
  have hHconv : ∀ s : ℂ, MellinConvergent H s := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _) (by linarith) hbO hb
  have hdiff : Differentiable ℂ (mellin H) := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _)
      (by linarith) hbO hb
  refine ⟨fun s => (s - 1) * mellin H s + R, ?_, by simp, ?_⟩
  · exact ((differentiable_id.sub_const 1).mul hdiff).add_const R
  · intro s hs
    have hs1 : s + -1 ≠ 0 := by
      intro h
      have : (s + -1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    have hGm := hasMellin_cpow_Ioc (-1) (s := s) (by rw [Complex.neg_re, Complex.one_re]; linarith)
    have hGconv : MellinConvergent G s := hGm.1
    have hGval : mellin G s = 1 / (s + -1) := hGm.2
    have e1 : F = fun t => H t + R • G t := by
      funext t
      simp only [hH, smul_eq_mul]
      ring
    have hmF : mellin F s = mellin H s + R * (1 / (s + -1)) := by
      rw [e1, (hasMellin_add (hHconv s) (hGconv.const_smul R)).2, mellin_const_smul, hGval,
        smul_eq_mul]
    have hmel : mellin F s = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) :=
      mellin_sum (weight_mellinConvergent hc hα hsupp s) hN (hsum s.re hs)
    have hHs : mellin H s = mellin F s - R * (1 / (s + -1)) := by rw [hmF]; ring
    show (s - 1) * mellin H s + R = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s))
    rw [hHs, hmel, ← sub_eq_add_neg]
    rw [← sub_eq_add_neg] at hs1
    field_simp
    ring

end GlobalTheory.SmoothedSumMellin
