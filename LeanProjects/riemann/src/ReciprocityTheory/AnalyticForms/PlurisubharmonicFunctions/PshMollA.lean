import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution

noncomputable section

variable {D : ℕ}

lemma finrank_fin_complex : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]

section Scaled

variable (ρ : Mollifier D)

lemma scaled_nonneg {ε : ℝ} (hε : 0 < ε) (w : Fin D → ℂ) : 0 ≤ ρ.scaled ε w :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le _)) (ρ.nonneg _)

lemma scaled_eq_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ε ≤ ‖w‖) :
    ρ.scaled ε w = 0 := by
  have : ρ.toFun (ε⁻¹ • w) = 0 := by
    by_contra h
    have h1 := ρ.support_subset h
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h1
    have h2 : ε⁻¹ * ε ≤ ε⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (inv_pos.2 hε).le
    rw [inv_mul_cancel₀ hε.ne'] at h2
    linarith
  simp [Mollifier.scaled, this]

lemma norm_lt_of_scaled_ne_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ρ.scaled ε w ≠ 0) :
    ‖w‖ < ε :=
  lt_of_not_ge fun h => hw (scaled_eq_zero ρ hε h)

lemma scaled_contDiff (ε : ℝ) : ContDiff ℝ ∞ (ρ.scaled ε) :=
  contDiff_const.mul (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹))

lemma scaled_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ.scaled ε) :=
  HasCompactSupport.intro (isCompact_closedBall 0 ε) fun _ hw =>
    scaled_eq_zero ρ hε (le_of_lt (not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)))

lemma integral_scaled {ε : ℝ} (hε : 0 < ε) : ∫ w, ρ.scaled ε w = 1 := by
  simp only [Mollifier.scaled]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume ρ.toFun hε.le,
    finrank_fin_complex, ρ.integral_eq_one, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_pos hε _).ne']

lemma integrable_scaled {ε : ℝ} (hε : 0 < ε) : Integrable (ρ.scaled ε) :=
  (scaled_contDiff ρ ε).continuous.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε)

lemma molli_congr {ε : ℝ} (hε : 0 < ε) {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ}
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) (h : EqOn φ ψ U) :
    molli ρ ε φ z = molli ρ ε ψ z := by
  unfold molli
  congr 1
  funext w
  by_cases hw : ρ.scaled ε w = 0
  · simp [hw]
  · rw [h (hz ?_)]
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact (norm_lt_of_scaled_ne_zero ρ hε hw).le

lemma conv_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} {L : NNReal} (hg : LipschitzWith L g)
    (z : Fin D → ℂ) : ‖(∫ w, ρ.scaled ε w • g (z - w)) - g z‖ ≤ L * ε := by
  have hc : Continuous fun w => ρ.scaled ε w • g (z - w) :=
    (scaled_contDiff ρ ε).continuous.smul (hg.continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable fun w => ρ.scaled ε w • g (z - w) :=
    hc.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε).smul_right
  have hi2 : Integrable fun w => ρ.scaled ε w • g z := (integrable_scaled ρ hε).smul_const _
  have e1 : g z = ∫ w, ρ.scaled ε w • g z := by
    rw [integral_smul_const, integral_scaled ρ hε, one_smul]
  rw [e1, ← integral_sub hi hi2]
  have hb : Integrable fun w => ρ.scaled ε w * (L * ε) := (integrable_scaled ρ hε).mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun w => ?_)).trans ?_
  · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (scaled_nonneg ρ hε w)]
    by_cases hw : ρ.scaled ε w = 0
    · simp [hw]
    · refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε w)
      have h1 := hg.dist_le_mul (z - w) z
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h1
      calc ‖g (z - w) - g z‖ ≤ L * ‖w‖ := h1
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (norm_lt_of_scaled_ne_zero ρ hε hw).le L.coe_nonneg
  · rw [integral_mul_const, integral_scaled ρ hε, one_mul]

lemma hasFDerivAt_conv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Fin D → ℂ) :
    HasFDerivAt (fun x => ∫ t, ρ.scaled ε t • g (x - t))
      (∫ t, ρ.scaled ε t • fderiv ℝ g (x - t)) x := by
  have h := hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (integrable_scaled ρ hε).locallyIntegrable hg x
  have e1 : (ρ.scaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      fun x => ∫ t, ρ.scaled ε t • g (x - t) := by
    funext y
    rw [convolution_def]
    rfl
  have e2 : (ρ.scaled ε ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin D → ℂ), volume]
      fderiv ℝ g) x = ∫ t, ρ.scaled ε t • fderiv ℝ g (x - t) := by
    rw [convolution_def]
    congr 1
  rw [e1, e2] at h
  exact h

end Scaled

lemma exists_cutoff {K U : Set (Fin D → ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ χ : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      cthickening δ K ⊆ U ∧ EqOn χ 1 (cthickening (δ / 2) K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hfs, hf, hfr⟩ :=
    (isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hg, hgr⟩ :=
    (isClosed_cthickening (δ := δ / 2) (E := K)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hts : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  have hpos : ∀ x, 0 < f x + g x := by
    intro x
    have hf0 : 0 ≤ f x := (hfr (mem_range_self x)).1
    have hg0 : 0 ≤ g x := (hgr (mem_range_self x)).1
    by_cases hx : x ∈ cthickening (δ / 2) K
    · have : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm this)) hg0
    · have : g x ≠ 0 := by rw [← Function.mem_support, hgs]; exact hx
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm this))
  have hsupp : tsupport (fun x => f x / (f x + g x)) ⊆ cthickening δ K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    rw [← hfs]
    intro h
    apply hx
    simp [h]
  refine ⟨δ, hδ, fun x => f x / (f x + g x), hf.div (hf.add hg) (fun x => (hpos x).ne'),
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hδU, hδU, ?_⟩
  intro x hx
  have hg0 : g x = 0 := Function.notMem_support.1 (by rw [hgs]; exact fun h => h hx)
  have hf0 : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
  simp [hg0, hf0]

lemma cutoff_mul {χ φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hts : tsupport χ ⊆ U) (hφ : ContDiffOn ℝ 3 φ U) :
    ContDiff ℝ 3 (fun x => χ x * φ x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (contDiff_infty.1 hχ 3).contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hts h)
    have h0 : (fun x => χ x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma mollificationSecondOrder_holds : MollificationSecondOrder := by
  intro D ρ U K φ hU hφ hK hKU
  obtain ⟨δ, hδ, χ, hχ, hχc, hχU, hδU, hχ1⟩ := exists_cutoff hK hU hKU
  set ψ : (Fin D → ℂ) → ℝ := fun x => χ x * φ x with hψ
  have hψd : ContDiff ℝ 3 ψ := cutoff_mul hU hχ hχU hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hd1 : ContDiff ℝ 2 (fderiv ℝ ψ) := hψd.fderiv_right (by norm_num)
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ψ)) := hd1.fderiv_right (by norm_num)
  obtain ⟨L0, hL0⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψd (by norm_num)
  obtain ⟨L1, hL1⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hψc.fderiv ℝ) hd1 (by norm_num)
  obtain ⟨L2, hL2⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport ((hψc.fderiv ℝ).fderiv ℝ) hd2 (by norm_num)
  have hD1 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε hψc (hψd.of_le (by norm_num)) x).fderiv
  have hD2 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ (fderiv ℝ ψ) (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε (hψc.fderiv ℝ) (hd1.of_le (by norm_num)) x).fderiv
  set C : ℝ := max (max (L0 : ℝ) L1) L2 with hC
  refine ⟨C, δ / 4, by positivity, fun ε hε hεδ z hz => ?_⟩
  have hzU : z ∈ shrink U ε :=
    ((closedBall_subset_closedBall (by linarith : ε ≤ δ)).trans
      (closedBall_subset_cthickening hz δ)).trans hδU
  have hEq : EqOn φ ψ (cthickening (δ / 2) K) := fun y hy => by
    have : χ y = 1 := hχ1 hy
    simp [hψ, this]
  have hball : ∀ y ∈ ball z (δ / 4), closedBall y ε ⊆ cthickening (δ / 2) K := by
    intro y hy x hx
    apply closedBall_subset_cthickening hz (δ / 2)
    rw [mem_closedBall] at hx ⊢
    rw [mem_ball] at hy
    linarith [dist_triangle x y z]
  have hmol : molli ρ ε φ =ᶠ[𝓝 z] fun x => ∫ t, ρ.scaled ε t • ψ (x - t) := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 4)] with y hy
    rw [molli_congr ρ hε (hball y hy) hEq]
    simp only [molli, smul_eq_mul]
  have hφψ : φ =ᶠ[𝓝 z] ψ := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 2)] with y hy
    exact hEq (closedBall_subset_cthickening hz _ (ball_subset_closedBall hy))
  have hle : ∀ L : NNReal, (L : ℝ) ≤ C → (L : ℝ) * ε ≤ C * ε := fun L hL =>
    mul_le_mul_of_nonneg_right hL hε.le
  refine ⟨hzU, ?_, ?_, ?_⟩
  · rw [hmol.eq_of_nhds, hφψ.eq_of_nhds]
    have := conv_lip ρ hε hL0 z
    rw [Real.norm_eq_abs] at this
    exact this.trans (hle L0 (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rw [hmol.fderiv_eq, hφψ.fderiv_eq, hD1 ε hε]
    exact (conv_lip ρ hε hL1 z).trans (hle L1 (le_trans (le_max_right _ _) (le_max_left _ _)))
  · rw [hmol.fderiv.fderiv_eq, hφψ.fderiv.fderiv_eq, hD1 ε hε, hD2 ε hε]
    exact (conv_lip ρ hε hL2 z).trans (hle L2 (le_max_right _ _))

end

end ReciprocityTheory.AnForm.A
