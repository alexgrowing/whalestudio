import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Mathlib

section

noncomputable section

open MeasureTheory Filter Topology

namespace GlobalTheory.PsCo.PcdSFB

theorem scale_int {ι : Type} [Fintype ι] (g : (ι → ℂ) → ℂ) (t : ℝ) (ht : 0 < t) :
    (t : ℂ) ^ Fintype.card ι * ∫ B, g B = ∫ w, g ((Real.sqrt t)⁻¹ • w) := by
  have hf : Module.finrank ℝ (ι → ℂ) = Fintype.card ι * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  rw [MeasureTheory.Measure.integral_comp_smul, hf]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h1 : |(((Real.sqrt t)⁻¹) ^ (Fintype.card ι * 2))⁻¹| = t ^ Fintype.card ι := by
    rw [abs_of_pos (by positivity), inv_pow, inv_inv, mul_comm, pow_mul, Real.sq_sqrt ht.le]
  rw [h1, Complex.real_smul]
  push_cast
  ring

def diag_int_map {ι : Type} [Fintype ι] (d : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  LinearMap.pi fun x => (d x • LinearMap.id : ℂ →ₗ[ℂ] ℂ).comp (LinearMap.proj x)

theorem diag_int_det {ι : Type} [Fintype ι] (d : ι → ℂ) :
    LinearMap.det ((diag_int_map d).restrictScalars ℝ) = ∏ x, ‖d x‖ ^ 2 := by
  rw [LinearMap.det_restrictScalars, diag_int_map, LinearMap.det_pi]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

theorem diag_int {ι : Type} [Fintype ι] (d : ι → ℂ) (hd : ∀ x, d x ≠ 0) (f : (ι → ℂ) → ℂ) :
    ∫ w : ι → ℂ, f (fun x => d x * w x) = (∫ w, f w) / ((∏ x, ‖d x‖ ^ 2 : ℝ) : ℂ) := by
  set g := (diag_int_map d).restrictScalars ℝ with hg
  have hdet : LinearMap.det g ≠ 0 := by
    rw [diag_int_det]; exact Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd x))
  let e := (g.equivOfDetNeZero hdet).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have he : ∀ w, (e w) = fun x => d x * w x := by
    intro w; funext x; simp [e, g, diag_int_map]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) hdet
  have h1 : ∫ w, f (e w) = ∫ y, f y ∂(Measure.map e volume) := (integral_map_equiv e f).symm
  simp only [he] at h1
  rw [h1]
  have : (Measure.map e volume : Measure (ι → ℂ)) = Measure.map g volume := rfl
  rw [this, hmap, integral_smul_measure, diag_int_det]
  have hpos : 0 < ∏ x, ‖d x‖ ^ 2 := Finset.prod_pos fun x _ => pow_pos (norm_pos_iff.2 (hd x)) 2
  rw [abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le]
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  ring

theorem blow_pt {ι : Type} [Fintype ι] (β : (ι → ℂ) → (ι → ℂ)) (L : (ι → ℂ) →L[ℝ] (ι → ℂ))
    (hβ0 : β 0 = 0) (hβd : HasFDerivAt β L 0) (w : ι → ℂ) :
    Tendsto (fun t : ℝ => t * ∑ x, ‖β ((Real.sqrt t)⁻¹ • w) x‖ ^ 2) atTop (𝓝 (∑ x, ‖L w x‖ ^ 2)) := by
  have hl : HasDerivAt (fun s : ℝ => s • w) w 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const w
  have h2 : HasFDerivAt β L ((0:ℝ) • w) := by simpa using hβd
  have h1 : HasDerivAt (fun s : ℝ => β (s • w)) (L w) 0 := h2.comp_hasDerivAt (0:ℝ) hl
  have h3 := h1.tendsto_slope_zero_right
  have h4 : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp Real.tendsto_sqrt_atTop
  have h5 := h3.comp h4
  have hc : Continuous (fun v : ι → ℂ => ∑ x, ‖v x‖ ^ 2) := by fun_prop
  have h6 := (hc.tendsto (L w)).comp h5
  refine h6.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  simp only [Function.comp_def, zero_add, zero_smul, hβ0, sub_zero, inv_inv, Pi.smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht.le, Finset.mul_sum]

theorem blow_bound {ι : Type} [Fintype ι] (β : (ι → ℂ) → (ι → ℂ)) (d : ι → ℂ) (L : (ι → ℂ) →L[ℝ] (ι → ℂ))
    (hd : ∀ x, d x ≠ 0) (hL : ∀ w x, L w x = d x * w x) (hβ0 : β 0 = 0) (hβd : HasFDerivAt β L 0)
    (hprop : ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ B, ∑ x, ‖β B x‖ ^ 2 ≤ η → ‖B‖ ≤ δ) :
    ∃ C T : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ B, t * ∑ x, ‖β B x‖ ^ 2 < 1 → ‖B‖ ≤ C / Real.sqrt t := by
  classical
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ ‖d x‖ := by
    rcases isEmpty_or_nonempty ι with h | h
    · exact ⟨1, one_pos, fun x => (h.false x).elim⟩
    · obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image Finset.univ (fun x => ‖d x‖) Finset.univ_nonempty
      exact ⟨‖d x0‖, norm_pos_iff.2 (hd x0), fun x => hx0 x (Finset.mem_univ x)⟩
  have hLlow : ∀ B, m * ‖B‖ ≤ ‖L B‖ := by
    intro B
    rw [← le_div_iff₀' hm0]
    refine (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hm0.le)).2 fun x => ?_
    rw [le_div_iff₀' hm0]
    calc m * ‖B x‖ ≤ ‖d x‖ * ‖B x‖ := mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _)
      _ = ‖L B x‖ := by rw [hL, norm_mul]
      _ ≤ ‖L B‖ := norm_le_pi_norm (L B) x
  have hev := hβd.isLittleO.def (half_pos hm0)
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.eventually_nhds_iff.1 hev
  have hlow : ∀ B, ‖B‖ < ρ → m / 2 * ‖B‖ ≤ ‖β B‖ := by
    intro B hB
    have h1 := hρ (y := B) (by simpa [dist_zero_right] using hB)
    simp only [hβ0, sub_zero] at h1
    have h2 := hLlow B
    have h3 : ‖L B‖ ≤ ‖β B‖ + ‖β B - L B‖ := by
      calc ‖L B‖ = ‖β B - (β B - L B)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    linarith
  obtain ⟨η, hη0, hη⟩ := hprop (ρ / 2) (half_pos hρ0)
  refine ⟨2 / m, 1 / η, by positivity, fun t ht B hB => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hsum_nn : 0 ≤ ∑ x, ‖β B x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hS : ∑ x, ‖β B x‖ ^ 2 < 1 / t := by
    rw [lt_div_iff₀ ht0]; linarith [mul_comm t (∑ x, ‖β B x‖ ^ 2)]
  have hSη : ∑ x, ‖β B x‖ ^ 2 ≤ η := by
    have : 1 / t ≤ η := by
      rw [div_le_iff₀ ht0]; rw [div_le_iff₀ hη0] at ht; linarith
    linarith
  have hBρ : ‖B‖ < ρ := lt_of_le_of_lt (hη B hSη) (half_lt_self hρ0)
  have hb := hlow B hBρ
  have hnorm2 : ‖β B‖ ^ 2 ≤ ∑ x, ‖β B x‖ ^ 2 := by
    have : ‖β B‖ ≤ Real.sqrt (∑ x, ‖β B x‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun x => ?_
      apply Real.le_sqrt_of_sq_le
      exact Finset.single_le_sum (f := fun x => ‖β B x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ x)
    calc ‖β B‖ ^ 2 ≤ (Real.sqrt (∑ x, ‖β B x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt hsum_nn
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have key : ‖β B‖ * Real.sqrt t < 1 := by
    have h1 : (‖β B‖ * Real.sqrt t) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt ht0.le]; nlinarith
    nlinarith [norm_nonneg (β B), hst]
  rw [le_div_iff₀ hst, le_div_iff₀' hm0]
  nlinarith [norm_nonneg B]

end GlobalTheory.PsCo.PcdSFB

end
end

section

noncomputable section

open MeasureTheory Filter Topology
open GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc3
open scoped ContDiff

namespace GlobalTheory.PsCo.PcdSFB

theorem stBlow : GlobalTheory.PsCo.Pc3.StBlow := by
  intro ι _ β d L hd hL hβ hβ0 hβd hprop F hF hF1 ψ hψ
  obtain ⟨C, T, hT, hCb⟩ := blow_bound β d L hd hL hβ0 hβd hprop
  have hint : ∀ t : ℝ, T ≤ t → Integrable (fun B => (F (t * ∑ x, ‖β B x‖ ^ 2) : ℂ) * ψ B) := by
    intro t ht
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℂ) (C / Real.sqrt t))
      intro B hB
      have h1 : ¬ (t * ∑ x, ‖β B x‖ ^ 2 < 1) := fun h => hB (mem_closedBall_zero_iff.2 (hCb t ht B h))
      simp [hF1 _ (not_lt.1 h1)]
  refine ⟨eventually_atTop.2 ⟨T, hint⟩, ?_⟩
  obtain ⟨MF, hMF⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨Mψ, hMψ⟩ := (isCompact_closedBall (0 : ι → ℂ) C).exists_bound_of_continuousOn hψ.continuousOn
  have hlim : ψ 0 * ((∫ w : ι → ℂ, F (∑ x, ‖w x‖ ^ 2) : ℝ) : ℂ) / ((∏ x, ‖d x‖ ^ 2 : ℝ) : ℂ) =
      ∫ w : ι → ℂ, (F (∑ x, ‖L w x‖ ^ 2) : ℂ) * ψ 0 := by
    simp_rw [hL]
    rw [diag_int d hd (fun v => (F (∑ x, ‖v x‖ ^ 2) : ℂ) * ψ 0), integral_mul_const, integral_complex_ofReal]
    ring
  rw [hlim]
  have hEq : ∀ᶠ t : ℝ in atTop, (∫ w, (F (t * ∑ x, ‖β ((Real.sqrt t)⁻¹ • w) x‖ ^ 2) : ℂ) * ψ ((Real.sqrt t)⁻¹ • w)) =
      (t : ℂ) ^ Fintype.card ι * ∫ B, (F (t * ∑ x, ‖β B x‖ ^ 2) : ℂ) * ψ B := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [scale_int (fun B => (F (t * ∑ x, ‖β B x‖ ^ 2) : ℂ) * ψ B) t ht]
  refine Tendsto.congr' hEq ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (Metric.closedBall (0 : ι → ℂ) C) (fun _ => |MF| * |Mψ|)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t => (by fun_prop : Continuous fun w : ι → ℂ =>
      (F (t * ∑ x, ‖β ((Real.sqrt t)⁻¹ • w) x‖ ^ 2) : ℂ) * ψ ((Real.sqrt t)⁻¹ • w)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    refine Eventually.of_forall fun w => ?_
    by_cases hlt : t * ∑ x, ‖β ((Real.sqrt t)⁻¹ • w) x‖ ^ 2 < 1
    · have hB := hCb t ht _ hlt
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 (by linarith)
      have hs1 : 1 ≤ Real.sqrt t := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt ht1
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le] at hB
      have hw : ‖w‖ ≤ C := by
        have := (inv_mul_le_iff₀ hs).1 hB
        rwa [mul_div_cancel₀ _ hs.ne'] at this
      have hw' : ‖(Real.sqrt t)⁻¹ • w‖ ≤ C := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
        calc (Real.sqrt t)⁻¹ * ‖w‖ ≤ 1 * ‖w‖ := by gcongr; exact inv_le_one_of_one_le₀ hs1
          _ ≤ C := by linarith
      rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hw), norm_mul, Complex.norm_real]
      have hpos : 0 ≤ t * ∑ x, ‖β ((Real.sqrt t)⁻¹ • w) x‖ ^ 2 := by positivity
      exact mul_le_mul ((hMF _ ⟨hpos, hlt.le⟩).trans (le_abs_self _))
        ((hMψ _ (mem_closedBall_zero_iff.2 hw')).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
    · rw [hF1 _ (not_lt.1 hlt)]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      apply Set.indicator_nonneg
      intro _ _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · exact (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const (measure_closedBall_lt_top).ne)
  · refine Eventually.of_forall fun w => ?_
    have h1 := blow_pt β L hβ0 hβd w
    have h2 : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹ • w) atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
      simpa using this.smul_const w
    exact ((Complex.continuous_ofReal.comp hF).continuousAt.tendsto.comp h1).mul ((hψ.tendsto 0).comp h2)

theorem profile_cont {N : ℕ} {G : ℝ → ℝ} (hG : IsProfile N G) (k : ℕ) : Continuous (iteratedDeriv k G) :=
  hG.1.continuous_iteratedDeriv k (by exact_mod_cast le_top)

theorem profile_van {N : ℕ} {G : ℝ → ℝ} (hG : IsProfile N G) (k : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    iteratedDeriv k G x = 0 := by
  have hopen : ∀ y, 1 < y → iteratedDeriv k G y = 0 := by
    intro y hy
    have h0 : G =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz using hG.2.1 z (le_of_lt hz)
    rw [h0.iteratedDeriv_eq k]
    simp
  have hcl : IsClosed {y : ℝ | iteratedDeriv k G y = 0} := isClosed_eq (profile_cont hG k) continuous_const
  have hsub : closure (Set.Ioi (1 : ℝ)) ⊆ {y : ℝ | iteratedDeriv k G y = 0} :=
    closure_minimal (fun y hy => hopen y hy) hcl
  rw [closure_Ioi] at hsub
  exact hsub hx

theorem iteratedDeriv_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) (t x : ℝ) :
    iteratedDeriv k (fun y => G (t * y)) x = t ^ k * iteratedDeriv k G (t * x) := by
  have h := iteratedDeriv_comp_const_mul (n := k) (hG.of_le (by exact_mod_cast le_top)) t
  rw [h]

theorem stFamBlow_of (hB : StBlow) : StFamBlow := by
  unfold StFamBlow
  intro ι _ β d L hd hL hβ hβ0 hβd hprop G hG ψ hψ
  have key := fun k => hB ι β d L hd hL hβ hβ0 hβd hprop (iteratedDeriv k G) (profile_cont hG k) (profile_van hG k)
      (ψ k) (hψ k)
  have hrw : ∀ t : ℝ, ∀ k (B : ι → ℂ),
      ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B =
        (t : ℂ) ^ k * (((iteratedDeriv k G (t * ∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B) := by
    intro t k B
    rw [iteratedDeriv_scale hG.1 k t]
    push_cast
    ring
  have hint : ∀ᶠ t : ℝ in atTop, ∀ k ∈ Finset.range (Fintype.card ι + 1),
      Integrable fun B => ((iteratedDeriv k G (t * ∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B :=
    (eventually_all_finset _).2 fun k _ => (key k).1
  have heq : ∀ᶠ t : ℝ in atTop, (∫ B, ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((iteratedDeriv k (fun x => G (t * x)) (∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1), (t : ℂ) ^ k *
        ∫ B, ((iteratedDeriv k G (t * ∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B := by
    filter_upwards [hint] with t ht
    simp_rw [hrw t]
    rw [integral_finsetSum _ fun k hk => (ht k hk).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
  have hlim : ∀ k ∈ Finset.range (Fintype.card ι + 1), Tendsto (fun t : ℝ => (t : ℂ) ^ k *
        ∫ B, ((iteratedDeriv k G (t * ∑ x, ‖β B x‖ ^ 2) : ℝ) : ℂ) * ψ k B) atTop
      (𝓝 (if k = Fintype.card ι then ψ (Fintype.card ι) 0 *
        ((∫ w : ι → ℂ, iteratedDeriv (Fintype.card ι) G (∑ x, ‖w x‖ ^ 2) : ℝ) : ℂ) /
        ((∏ x, ‖d x‖ ^ 2 : ℝ) : ℂ) else 0)) := by
    intro k hk
    have hk' : k ≤ Fintype.card ι := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    by_cases hkN : k = Fintype.card ι
    · subst hkN
      simpa using (key (Fintype.card ι)).2
    · rw [if_neg hkN]
      have hlt : k < Fintype.card ι := lt_of_le_of_ne hk' hkN
      have h0 : Tendsto (fun t : ℝ => ((t : ℂ) ^ (Fintype.card ι - k))⁻¹) atTop (𝓝 0) := by
        have h2 : Tendsto (fun t : ℝ => (t ^ (Fintype.card ι - k))⁻¹) atTop (𝓝 0) :=
          (tendsto_pow_atTop (Nat.sub_ne_zero_of_lt hlt)).inv_tendsto_atTop
        have h1 : Tendsto (fun t : ℝ => ‖((t : ℂ) ^ (Fintype.card ι - k))⁻¹‖) atTop (𝓝 0) := by
          refine h2.congr' ?_
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
          rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht]
        exact tendsto_zero_iff_norm_tendsto_zero.2 h1
      have h3 := ((key k).2).mul h0
      rw [mul_zero] at h3
      refine h3.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      have hpow : (t : ℂ) ^ Fintype.card ι = (t : ℂ) ^ k * (t : ℂ) ^ (Fintype.card ι - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hk']
      rw [hpow]
      field_simp
  have hsum := tendsto_finsetSum _ hlim
  rw [Finset.sum_ite_eq' (Finset.range (Fintype.card ι + 1)) (Fintype.card ι),
    if_pos (Finset.self_mem_range_succ _)] at hsum
  exact hsum.congr' (by filter_upwards [heq] with t ht using ht.symm)

end GlobalTheory.PsCo.PcdSFB

end
end

section

namespace GlobalTheory.PsCo.Pcd

theorem stFamBlow : GlobalTheory.PsCo.Pc3.StFamBlow :=
  GlobalTheory.PsCo.PcdSFB.stFamBlow_of GlobalTheory.PsCo.PcdSFB.stBlow

end GlobalTheory.PsCo.Pcd

end
