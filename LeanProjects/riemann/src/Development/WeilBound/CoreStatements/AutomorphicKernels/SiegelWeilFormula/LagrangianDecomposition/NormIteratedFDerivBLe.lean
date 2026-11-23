import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.NormAinApplyLe

noncomputable section

open scoped ContDiff
open MeasureTheory Set Filter Topology

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {κ' κ'' : Type} [Fintype κ']
  [Fintype κ'']

theorem contDiff_Θ (h : SchwartzMap (κ' ⊕ κ'' → W) ℂ) :
    ContDiff ℝ ∞ (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) :=
  (h.smooth ⊤).comp contDiff_Ain

theorem norm_pder_le (h : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (m : ℕ) (x : κ' ⊕ κ'' → W) {s : ℝ} (hs : |s| ≤ 1) :
    ‖pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)‖ ≤ ‖iteratedFDeriv ℝ m h (Ain s x)‖ := by
  have e : pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)
      = iteratedFDeriv ℝ m (⇑h ∘ ⇑(Ain s : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W))) x := rfl
  rw [e, (Ain s).iteratedFDeriv_comp_right (h.smooth ⊤) x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin m, ‖(Ain s : (κ' ⊕ κ'' → W) →L[ℝ] (κ' ⊕ κ'' → W))‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => norm_Ain_le hs)
  calc _ ≤ ‖iteratedFDeriv ℝ m h (Ain s x)‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := mul_one _

theorem near_bound (h : SchwartzMap (κ' ⊕ κ'' → W) ℂ) {R : ℝ} (hR : 0 ≤ R) (k m : ℕ) (x : κ' ⊕ κ'' → W)
    (hx : ‖x ∘ Sum.inr‖ ≤ R) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x‖ ≤
      SchwartzMap.seminorm ℝ k m h + R ^ k * SchwartzMap.seminorm ℝ 0 m h := by
  have hc : ContDiff ℝ ∞ (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) := contDiff_Θ h
  rw [show iteratedFDeriv ℝ m (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x
      = ∫ s in Ioc (0 : ℝ) 1, pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)
      from iteratedFDeriv_integral hc m x]
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖(‖x‖ ^ k) • pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)‖ ≤
        SchwartzMap.seminorm ℝ k m h + R ^ k * SchwartzMap.seminorm ℝ 0 m h := by
    intro s hs
    have hs' : |s| ≤ 1 := by
      rw [abs_of_pos hs.1]
      exact hs.2
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_pder_le h m x hs'
    have h2 := norm_le_max_Ain s x
    have hA := SchwartzMap.le_seminorm ℝ k m h (Ain s x)
    have hB := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ h m (Ain s x)
    have hxk : ‖x‖ ^ k ≤ ‖Ain s x‖ ^ k + R ^ k := by
      rcases le_total ‖Ain s x‖ ‖x ∘ Sum.inr‖ with hle | hle
      · rw [max_eq_right hle] at h2
        have : ‖x‖ ^ k ≤ R ^ k := pow_le_pow_left₀ (norm_nonneg _) (h2.trans hx) k
        linarith [pow_nonneg (norm_nonneg (Ain s x)) k]
      · rw [max_eq_left hle] at h2
        have : ‖x‖ ^ k ≤ ‖Ain s x‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) h2 k
        linarith [pow_nonneg hR k]
    calc ‖x‖ ^ k * ‖pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)‖
        ≤ (‖Ain s x‖ ^ k + R ^ k) * ‖iteratedFDeriv ℝ m h (Ain s x)‖ :=
          mul_le_mul hxk h1 (norm_nonneg _) (by positivity)
      _ = ‖Ain s x‖ ^ k * ‖iteratedFDeriv ℝ m h (Ain s x)‖ +
            R ^ k * ‖iteratedFDeriv ℝ m h (Ain s x)‖ := by ring
      _ ≤ _ := add_le_add hA (mul_le_mul_of_nonneg_left hB (by positivity))
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hpt
  rw [integral_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at hI
  simpa using hI

theorem norm_iteratedFDeriv_B_le (β : (κ'' → W) → ℝ) (hβ : ContDiff ℝ ∞ β) (i : ℕ) (x : κ' ⊕ κ'' → W) :
    ‖iteratedFDeriv ℝ i (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) x‖ ≤ ‖iteratedFDeriv ℝ i β (x ∘ Sum.inr)‖ := by
  let L : (κ' ⊕ κ'' → W) →L[ℝ] (κ'' → W) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Sum.inr j)
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun j => ?_
    exact norm_le_pi_norm y (Sum.inr j)
  have e : (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) = ⇑Complex.ofRealLI ∘ (β ∘ ⇑L) := rfl
  have hβL : ContDiff ℝ ∞ (β ∘ ⇑L) := hβ.comp L.contDiff
  rw [e, Complex.ofRealLI.norm_iteratedFDeriv_comp_left hβL.contDiffAt (by exact_mod_cast le_top),
    L.iteratedFDeriv_comp_right hβ x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _j : Fin i, ‖L‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
  calc _ ≤ ‖iteratedFDeriv ℝ i β (L x)‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := mul_one _

private theorem differentiable_integral_Ioc_of_contDiff {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (G : V × ℝ → E) (hG : ContDiff ℝ 1 G) :
    Differentiable ℝ (fun x => ∫ s in Ioc (0 : ℝ) 1, G (x, s)) := by
  intro x₀
  have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall x₀ 1).prod isCompact_Icc
  have hGd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGd.continuousOn
  have hGc : Continuous G := hG.continuous
  have hd : ∀ p, HasFDerivAt G (fderiv ℝ G p) p := fun p =>
    (hG.differentiable (by simp) p).hasFDerivAt
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun x s => G (x, s))
    (F' := fun x s => (fderiv ℝ G (x, s)).comp (ContinuousLinearMap.inl ℝ V ℝ))
    (bound := fun _ => C * ‖ContinuousLinearMap.inl ℝ V ℝ‖)
    (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt
  · exact Filter.Eventually.of_forall fun x =>
      (hGc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · exact ((hGc.comp (Continuous.prodMk continuous_const continuous_id)).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · exact ((hGd.comp (Continuous.prodMk continuous_const continuous_id)).clm_comp
      continuous_const).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs x hx => ?_
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hC _ ⟨hx, Ioc_subset_Icc_self hs⟩) (norm_nonneg _)
  · exact (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact Filter.Eventually.of_forall fun s x _ =>
      (hd (x, s)).comp x (hasFDerivAt_prodMk_left x s)

theorem near_schwartz (h : SchwartzMap (κ' ⊕ κ'' → W) ℂ) (β : (κ'' → W) → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) :
    ∃ g : SchwartzMap (κ' ⊕ κ'' → W) ℂ, ∀ x, g x = (β (x ∘ Sum.inr) : ℂ) * ∫ s in Ioc (0 : ℝ) 1, h (Ain s x) := by
  have hc : ContDiff ℝ ∞ (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) := contDiff_Θ h
  have hIF : ∀ m x, iteratedFDeriv ℝ m (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x
      = ∫ s in Ioc (0 : ℝ) 1, pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s) :=
    fun m x => iteratedFDeriv_integral hc m x
  have hF : ContDiff ℝ ∞ (fun y : κ' ⊕ κ'' → W => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) := by
    refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
    rw [show iteratedFDeriv ℝ m (fun y : κ' ⊕ κ'' → W => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) =
        fun x => ∫ s in Ioc (0 : ℝ) 1,
          pder m (fun p : (κ' ⊕ κ'' → W) × ℝ => h (Ain p.2 p.1)) (x, s)
      from funext (hIF m)]
    exact differentiable_integral_Ioc_of_contDiff _ ((contDiff_pder m hc).of_le (by exact_mod_cast le_top))
  have hB : ContDiff ℝ ∞ (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) := by
    have hL : ContDiff ℝ ∞ (fun y : κ' ⊕ κ'' → W => y ∘ Sum.inr) :=
      contDiff_pi.2 fun j => contDiff_apply ℝ W (Sum.inr j)
    exact Complex.ofRealCLM.contDiff.comp (hβ.comp hL)
  obtain ⟨R0, hR0⟩ := hβc.isCompact.isBounded.subset_closedBall 0
  have hR : 0 ≤ max R0 0 := le_max_right _ _
  have hsupp : ∀ y ∈ tsupport β, ‖y‖ ≤ max R0 0 := fun y hy => by
    have := hR0 hy
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hM : ∀ i, ∃ C, ∀ y, ‖iteratedFDeriv ℝ i β y‖ ≤ C := fun i =>
    (hβ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hβc.iteratedFDeriv i)
  choose M hM using hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  refine ⟨⟨fun x => (β (x ∘ Sum.inr) : ℂ) * ∫ s in Ioc (0 : ℝ) 1, h (Ain s x), hB.mul hF, ?_⟩,
    fun x => rfl⟩
  intro k n
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (M i * (SchwartzMap.seminorm ℝ k (n - i) h +
      (max R0 0) ^ k * SchwartzMap.seminorm ℝ 0 (n - i) h)), fun x => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le hB hF x (n := n) (by exact_mod_cast le_top)
  refine (mul_le_mul_of_nonneg_left hmul (by positivity)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have key : ‖iteratedFDeriv ℝ i (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) x‖ *
      (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x‖) ≤
      M i * (SchwartzMap.seminorm ℝ k (n - i) h +
        (max R0 0) ^ k * SchwartzMap.seminorm ℝ 0 (n - i) h) := by
    have h3 := norm_iteratedFDeriv_B_le β hβ i x
    by_cases hx : x ∘ Sum.inr ∈ tsupport β
    · exact mul_le_mul (h3.trans (hM i _)) (near_bound h hR k (n - i) x (hsupp _ hx))
        (by positivity) (hM0 i)
    · have h0 : iteratedFDeriv ℝ i β (x ∘ Sum.inr) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hm => hx (tsupport_iteratedFDeriv_subset i hm)
      rw [h0, norm_zero] at h3
      have hz : ‖iteratedFDeriv ℝ i (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) x‖ = 0 :=
        le_antisymm h3 (norm_nonneg _)
      rw [hz, zero_mul]
      exact mul_nonneg (hM0 i) (add_nonneg (apply_nonneg _ _)
        (mul_nonneg (pow_nonneg hR k) (apply_nonneg _ _)))
  calc ‖x‖ ^ k * ((n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x‖)
      = (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun y : κ' ⊕ κ'' → W => (β (y ∘ Sum.inr) : ℂ)) x‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) (fun y => ∫ s in Ioc (0 : ℝ) 1, h (Ain s y)) x‖)) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
