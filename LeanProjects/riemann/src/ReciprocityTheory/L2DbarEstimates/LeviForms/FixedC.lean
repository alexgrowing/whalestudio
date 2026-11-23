import ReciprocityTheory.L2DbarEstimates.LeviForms.FixedA

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

theorem fx_lp_norm_sq_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : Lp ℂ 2 μ)
    (G : α → ℂ) (h : (v : α → ℂ) =ᵐ[μ] G) :
    eLpNorm G 2 μ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [eLpNorm_congr_ae h.symm, Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v), ENNReal.rpow_two]

theorem fx_exists_holo_limit {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hC : HoloClosedNeed n M) (hE : EvalNeed n M) (hCVX : CVXNeed.{u})
    (S : Set M) (hS : S.Finite) (a : M → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
    (F : ℕ → M → ℂ) (hF : ∀ k, Holo n X.z (F k))
    (hB : ∀ k, wint n X.z (F k) ps ≤ ENNReal.ofReal B)
    (hlim : ∀ p ∈ S, Tendsto (fun k => F k p) atTop (𝓝 (a p))) :
    ∃ G : M → ℂ, Holo n X.z G ∧ (∀ p ∈ S, G p = a p) ∧ wint n X.z G ps ≤ ENNReal.ofReal B := by
  have hz := X.isLocalHomeomorph
  have hpsc : Continuous ps := by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hps)
    exact this.congr fun x => by simp
  set μ : Measure M := (vol n X.z).withDensity (fun x => ENNReal.ofReal (Real.exp (-ps x)))
    with hμ
  have hkey : ∀ f : M → ℂ, wint n X.z f ps = eLpNorm f 2 μ ^ (2 : ℝ) := fun f => by
    rw [fx_wint_eq_withDensity n X.z ps hpsc.measurable f, fx_lintegral_enorm_sq_eq]
  have hN : ∀ (v : Lp ℂ 2 μ) (G : M → ℂ), (v : M → ℂ) =ᵐ[μ] G →
      wint n X.z G ps = ENNReal.ofReal (‖v‖ ^ 2) := fun v G h => by
    rw [hkey, fx_lp_norm_sq_eq μ v G h]
  have hcont : ∀ G : M → ℂ, Holo n X.z G → Continuous G := fun G hG =>
    Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hG)

  have hEv : ∀ p ∈ S, ∃ C : ℝ, 0 ≤ C ∧ ∀ (G₁ G₂ : M → ℂ), Holo n X.z G₁ → Holo n X.z G₂ →
      ∀ w : Lp ℂ 2 μ, (w : M → ℂ) =ᵐ[μ] (fun x => G₁ x - G₂ x) → ‖G₁ p - G₂ p‖ ≤ C * ‖w‖ := by
    intro p _
    obtain ⟨C, hC⟩ := hE X ps p hps
    refine ⟨Real.sqrt (max C 0), Real.sqrt_nonneg _, fun G₁ G₂ h₁ h₂ w hw => ?_⟩
    have h := hC _ (Holo.sub n X.z _ _ h₁ h₂)
    rw [hN w _ hw] at h
    have h' : ENNReal.ofReal (‖G₁ p - G₂ p‖ ^ 2) ≤ ENNReal.ofReal (max C 0 * ‖w‖ ^ 2) := by
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      exact h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h'
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (le_max_right _ _)]
    exact h'
  choose! Cev hCev0 hCev using hEv
  have hmem : ∀ k, MemLp (F k) 2 μ := fun k => by
    refine ⟨(hcont _ (hF k)).aestronglyMeasurable, ?_⟩
    have h := ((hkey (F k)).symm.trans_le (hB k)).trans_lt ENNReal.ofReal_lt_top
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h
  let K : ℕ → Set (Lp ℂ 2 μ) := fun m => {v | ∃ G : M → ℂ, Holo n X.z G ∧
    (v : M → ℂ) =ᵐ[μ] G ∧ ‖v‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) ∧
    ∀ p ∈ S, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1)}
  have hanti : Antitone K := by
    intro m₁ m₂ h v hv
    obtain ⟨G, hG, hvG, hn, hp⟩ := hv
    have : 1 / ((m₂ : ℝ) + 1) ≤ 1 / ((m₁ : ℝ) + 1) := by
      gcongr
    exact ⟨G, hG, hvG, hn.trans (by linarith), fun p hp' => (hp p hp').trans this⟩
  have hne : ∀ m, (K m).Nonempty := by
    intro m
    have hev : ∀ᶠ k in atTop, ∀ p ∈ S, ‖F k p - a p‖ ≤ 1 / ((m : ℝ) + 1) := by
      refine (Filter.eventually_all_finite hS).2 fun p hp => ?_
      have := (Metric.tendsto_nhds.mp (hlim p hp)) (1 / ((m : ℝ) + 1)) (by positivity)
      filter_upwards [this] with k hk
      rw [← dist_eq_norm]; exact hk.le
    obtain ⟨k, hk⟩ := hev.exists
    refine ⟨(hmem k).toLp (F k), F k, hF k, MemLp.coeFn_toLp _, ?_, hk⟩
    have h := (hN ((hmem k).toLp (F k)) (F k) (MemLp.coeFn_toLp (hmem k))).symm.trans_le (hB k)
    rw [ENNReal.ofReal_le_ofReal_iff hB0] at h
    have : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hclosed : ∀ m, IsClosed (K m) := by
    intro m
    refine IsSeqClosed.isClosed fun vs v hvs hlimv => ?_
    have hvs' : ∀ i, ∃ G : M → ℂ, Holo n X.z G ∧
        (vs i : M → ℂ) =ᵐ[μ] G ∧ ‖vs i‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) ∧
        ∀ p ∈ S, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1) := hvs
    choose G hG hvG hnG hpG using hvs'
    have hvm : Measurable (v : M → ℂ) := (Lp.stronglyMeasurable v).measurable
    have hd : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - (v : M → ℂ) x := fun i => by
      filter_upwards [Lp.coeFn_sub (vs i) v, hvG i] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
    have hlim0 : Tendsto (fun i => ‖vs i - v‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hlimv
    have hw : Tendsto (fun i => wint n X.z (fun x => G i x - (v : M → ℂ) x) ps) atTop (𝓝 0) := by
      have he : (fun i => wint n X.z (fun x => G i x - (v : M → ℂ) x) ps) =
          fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2) := funext fun i => hN _ _ (hd i)
      rw [he]
      have : Tendsto (fun i => ENNReal.ofReal (‖vs i - v‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hlim0.pow 2)
      simpa using this
    obtain ⟨Gl, hGl, hfG⟩ := hC X ps G (v : M → ℂ) hps hG hvm hw
    have hvGl : (v : M → ℂ) =ᵐ[μ] Gl := (withDensity_absolutelyContinuous _ _).ae_le hfG
    refine ⟨Gl, hGl, hvGl, ?_, fun p hp => ?_⟩
    · exact le_of_tendsto (((continuous_norm.tendsto v).comp hlimv).pow 2)
        (Eventually.of_forall hnG)
    · have hd2 : ∀ i, (⇑(vs i - v) : M → ℂ) =ᵐ[μ] fun x => G i x - Gl x := fun i => by
        filter_upwards [hd i, hvGl] with x h1 h2
        rw [h1, h2]
      have hb : ∀ i, ‖Gl p - a p‖ ≤ Cev p * ‖vs i - v‖ + 1 / ((m : ℝ) + 1) := fun i => by
        have h1 := hCev p hp (G i) Gl (hG i) hGl _ (hd2 i)
        calc ‖Gl p - a p‖ ≤ ‖Gl p - G i p‖ + ‖G i p - a p‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ = ‖G i p - Gl p‖ + ‖G i p - a p‖ := by rw [norm_sub_rev (Gl p)]
          _ ≤ _ := add_le_add h1 (hpG i p hp)
      have ht : Tendsto (fun i => Cev p * ‖vs i - v‖ + 1 / ((m : ℝ) + 1)) atTop
          (𝓝 (Cev p * 0 + 1 / ((m : ℝ) + 1))) := (hlim0.const_mul _).add_const _
      simpa using ge_of_tendsto' ht hb
  have hmid : ∀ m, ∀ v ∈ K m, ∀ w ∈ K m, (2 : ℂ)⁻¹ • (v + w) ∈ K m := by
    rintro m v ⟨G, hG, hvG, hnv, hpv⟩ w ⟨G', hG', hwG, hnw, hpw⟩
    refine ⟨fun x => (2 : ℂ)⁻¹ * (G x + G' x),
      Holo.mul n X.z _ _ (Holo.const n X.z _) (Holo.add n X.z _ _ hG hG'), ?_, ?_, fun p hp => ?_⟩
    · filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (v + w), Lp.coeFn_add v w, hvG, hwG]
        with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, smul_eq_mul]
    · have h1 : ‖(2 : ℂ)⁻¹ • (v + w)‖ ≤ (‖v‖ + ‖w‖) / 2 := by
        rw [norm_smul, norm_inv, Complex.norm_two]
        have := norm_add_le v w
        linarith
      have h0 : 0 ≤ ‖(2 : ℂ)⁻¹ • (v + w)‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖v‖ - ‖w‖), mul_le_mul h1 h1 h0 (by positivity),
        norm_nonneg v, norm_nonneg w]
    · calc ‖(2 : ℂ)⁻¹ * (G p + G' p) - a p‖ = ‖(2 : ℂ)⁻¹ * ((G p - a p) + (G' p - a p))‖ := by
            congr 1; ring
        _ ≤ 2⁻¹ * (‖G p - a p‖ + ‖G' p - a p‖) := by
            rw [norm_mul, norm_inv, Complex.norm_two]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ 1 / ((m : ℝ) + 1) := by linarith [hpv p hp, hpw p hp]
  have hbdd : Bornology.IsBounded (K 0) := by
    refine (Metric.isBounded_closedBall (x := (0 : Lp ℂ 2 μ)) (r := B + 2)).subset ?_
    rintro v ⟨G, -, -, hn, -⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    norm_num at hn
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  obtain ⟨v, hv⟩ := hCVX (Lp ℂ 2 μ) K hanti hne hclosed hmid hbdd
  obtain ⟨G, hG, hvG, -, -⟩ := hv 0
  refine ⟨G, hG, fun p hp => ?_, ?_⟩
  · have hb : ∀ m : ℕ, ‖G p - a p‖ ≤ 1 / ((m : ℝ) + 1) := fun m => by
      obtain ⟨G', hG', hvG', -, hp'⟩ := hv m
      have h0 : (⇑(0 : Lp ℂ 2 μ) : M → ℂ) =ᵐ[μ] fun x => G x - G' x := by
        filter_upwards [Lp.coeFn_zero ℂ 2 μ, hvG, hvG'] with x h1 h2 h3
        rw [h1, Pi.zero_apply, ← h2, ← h3, sub_self]
      have h1 := hCev p hp G G' hG hG' 0 h0
      rw [norm_zero, mul_zero] at h1
      calc ‖G p - a p‖ ≤ ‖G p - G' p‖ + ‖G' p - a p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 0 + 1 / ((m : ℝ) + 1) := add_le_add h1 (hp' p hp)
        _ = _ := zero_add _
    have h := ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  · rw [hN v G hvG]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ∀ m : ℕ, ‖v‖ ^ 2 ≤ B + 1 / ((m : ℝ) + 1) := fun m => (hv m).choose_spec.2.2.1
    have ht : Tendsto (fun m : ℕ => B + 1 / ((m : ℝ) + 1)) atTop (𝓝 (B + 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
    simpa using ge_of_tendsto' ht hb

end

end ReciprocityTheory.L2DbarEstimates.I
