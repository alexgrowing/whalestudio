import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.SUVol.DensChart

open scoped Pointwise

theorem mem_grpBall_iff_norm {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) {ε : ℝ}
    (hε : 0 < ε) (g : H) :
    g ∈ grpBall H ε ↔ ‖(fun τ i j => ((((g : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) i j) - (fun (_ : ι) i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j)‖ < ε := by
  rw [pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem tanBall_eq_ball {ι : Type} [Fintype ι] {r : ℕ} {ε : ℝ} (hε : 0 < ε) :
    tanBall ι r ε = Metric.ball 0 ε := by
  ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl

theorem density_at_one : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (lam : Measure W) [lam.IsAddHaarMeasure] (Q : W → H) (D : W →L[ℝ] (ι → Fin r → Fin r → ℂ)) (h : W → ℝ≥0∞) (a : ℝ≥0∞) (ρ : ℝ), HasStrictFDerivAt (fun w => fun τ i j => ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D 0 → Q 0 = 1 → Function.Injective D → (∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ grpBall H ε, ∃ w : W, ‖w‖ < δ ∧ Q w = g) → Tendsto h (𝓝 0) (𝓝 a) → a ≠ 0 → a ≠ ⊤ → 0 < ρ → (∀ A : Set W, MeasurableSet A → A ⊆ Metric.ball 0 ρ → μ (Q '' A) = ∫⁻ w in A, h w ∂lam) → Tendsto (fun ε : ℝ => μ (grpBall H ε) / (lam.map D) (tanBall ι r ε)) (𝓝[>] 0) (𝓝 a) := by
  intro ι _ r H _ μ W _ _ _ _ _ lam _ Q D h a ρ hD hQ0 hDi hon hh ha0 hat hρ hμ
  set f : W → (ι → Fin r → Fin r → ℂ) := fun w τ i j =>
    ((((Q w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf
  set one : ι → Fin r → Fin r → ℂ := fun _ i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hone
  have hf0 : f 0 = one := by simp [hf, hone, hQ0]
  have hD' : HasStrictFDerivAt f D 0 := hD
  obtain ⟨K, -, hK⟩ := (D : W →ₗ[ℝ] (ι → Fin r → Fin r → ℂ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 hDi)
  set K' : ℝ := (K : ℝ) + 1 with hK'
  have hK'0 : 0 < K' := by positivity
  have hnorm : ∀ w, ‖w‖ ≤ K' * ‖D w‖ := by
    intro w
    have h1 := hK.le_mul_dist w 0
    simp only [dist_zero_right, map_zero] at h1
    calc ‖w‖ ≤ K * ‖D w‖ := h1
      _ ≤ K' * ‖D w‖ := by gcongr; linarith
  have hcw : ∀ c : ℝ, 0 ≤ c → ∀ w, c / K' * ‖w‖ ≤ c * ‖D w‖ := by
    intro c hc w
    calc c / K' * ‖w‖ ≤ c / K' * (K' * ‖D w‖) := by gcongr; exact hnorm w
      _ = c * ‖D w‖ := by field_simp
  have approx : ∀ κ : ℝ, 0 < κ → ∃ δ > 0, ∀ w : W, ‖w‖ < δ → ‖f w - one - D w‖ ≤ κ * ‖w‖ := by
    intro κ hκ
    have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hD'.hasFDerivAt).def hκ
    obtain ⟨δ, hδ, hh'⟩ := Metric.eventually_nhds_iff.1 h1
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have := hh' (y := w) (by rwa [dist_zero_right])
    simpa [hf0] using this
  set V : ℝ → ℝ≥0∞ := fun ε => lam (D ⁻¹' Metric.ball 0 ε) with hVdef
  set S : ℝ → Set W := fun ε => D ⁻¹' Metric.ball 0 ε ∩ Metric.ball 0 ρ with hSdef
  set F : ℝ → ℝ≥0∞ := fun ε => μ (Q '' S ε) with hFdef
  have hV0 : ∀ ε : ℝ, 0 < ε → V ε ≠ 0 := fun ε hε =>
    (Metric.isOpen_ball.preimage D.continuous).measure_ne_zero lam ⟨0, by simp [hε]⟩
  have hVt : ∀ ε : ℝ, V ε ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (measure_closedBall_lt_top (μ := lam) (x := 0) (r := K' * ε)).ne
      (measure_mono fun w hw => ?_)
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ ≤ K' * ε := by gcongr
  have hVhom : ∀ t ε : ℝ, 0 < t → 0 < ε → V (t * ε) = ENNReal.ofReal (t ^ Module.finrank ℝ W) * V ε := by
    intro t ε ht _
    have hs : D ⁻¹' Metric.ball 0 (t * ε) = t • (D ⁻¹' Metric.ball 0 ε) := by
      ext w
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne']
      simp only [Set.mem_preimage, mem_ball_zero_iff, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos ht]
      rw [inv_mul_lt_iff₀ ht]
    simp only [hVdef]
    rw [hs, Measure.addHaar_smul, abs_of_pos (pow_pos ht _)]
  have hSmeas : ∀ ε, MeasurableSet (S ε) := fun ε =>
    (measurableSet_ball.preimage D.measurable).inter measurableSet_ball
  have hSeq : ∀ ε : ℝ, ε < ρ / K' → S ε = D ⁻¹' Metric.ball 0 ε := by
    intro ε hε
    refine Set.inter_eq_left.2 fun w hw => ?_
    rw [Set.mem_preimage, mem_ball_zero_iff] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
      _ < K' * (ρ / K') := by gcongr; linarith [norm_nonneg (D w)]
      _ = ρ := by field_simp
  have hFint : ∀ ε : ℝ, F ε = ∫⁻ w in S ε, h w ∂lam := fun ε =>
    hμ (S ε) (hSmeas ε) Set.inter_subset_right
  have hF : Tendsto (fun ε => F ε / V ε) (𝓝[>] 0) (𝓝 a) := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨a', hb', ha'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (lt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : a' * V ε ≤ F ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc b < a' := hb'
        _ = a' * V ε / V ε := (ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)).symm
        _ ≤ F ε / V ε := ENNReal.div_le_div_right hle _
    · obtain ⟨a', ha', hb'⟩ := exists_between hb
      obtain ⟨δh, hδh, hδ⟩ := Metric.eventually_nhds_iff.1 (hh.eventually (gt_mem_nhds ha'))
      filter_upwards [Ioo_mem_nhdsGT (lt_min (div_pos hρ hK'0) (div_pos hδh hK'0))] with ε hε
      obtain ⟨hε0, hε1⟩ := hε
      rw [lt_min_iff] at hε1
      have hle : F ε ≤ a' * V ε := by
        rw [hFint, hSeq ε hε1.1, ← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_ball.preimage D.measurable) fun w hw => (hδ ?_).le
        rw [Set.mem_preimage, mem_ball_zero_iff] at hw
        rw [dist_zero_right]
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δh / K') := by gcongr; linarith [norm_nonneg (D w)]
          _ = δh := by field_simp
      calc F ε / V ε ≤ a' * V ε / V ε := ENNReal.div_le_div_right hle _
        _ = a' := ENNReal.mul_div_cancel_right (hV0 ε hε0) (hVt ε)
        _ < b := hb'
  have hA : ∀ t : ℝ, 1 < t → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      F (t⁻¹ * ε) ≤ μ (grpBall H ε) ∧ μ (grpBall H ε) ≤ F (t * ε) := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    obtain ⟨δ1, hδ1, H1⟩ := approx ((t - 1) / K') (div_pos (by linarith) hK'0)
    obtain ⟨δ2, hδ2, H2⟩ := approx ((1 - t⁻¹) / K') (div_pos (by linarith) hK'0)
    obtain ⟨ε0, hε0, hon0⟩ := hon (min ρ δ2) (lt_min hρ hδ2)
    filter_upwards [Ioo_mem_nhdsGT (lt_min hε0 (lt_min (div_pos hδ1 hK'0) (div_pos hρ hK'0)))]
      with ε hε
    obtain ⟨hεp, hε1⟩ := hε
    simp only [lt_min_iff] at hε1
    obtain ⟨hεe, hεd, hερ⟩ := hε1
    constructor
    · refine measure_mono ?_
      rintro _ ⟨w, ⟨hw1, -⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff] at hw1
      rw [mem_grpBall_iff_norm H hεp]
      change ‖f w - one‖ < ε
      have hDw : ‖D w‖ < ε := by
        calc ‖D w‖ < t⁻¹ * ε := hw1
          _ < 1 * ε := by gcongr
          _ = ε := one_mul ε
      have hw : ‖w‖ < δ1 := by
        calc ‖w‖ ≤ K' * ‖D w‖ := hnorm w
          _ < K' * (δ1 / K') := by gcongr; linarith
          _ = δ1 := by field_simp
      have e1 := H1 w hw
      have e2 := hcw (t - 1) (by linarith) w
      have e3 : ‖f w - one‖ ≤ ‖D w‖ + ‖f w - one - D w‖ := by
        calc ‖f w - one‖ = ‖D w + (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have e4 : t * ‖D w‖ < ε := by
        calc t * ‖D w‖ < t * (t⁻¹ * ε) := by gcongr
          _ = ε := by field_simp
      nlinarith
    · refine measure_mono fun g hg => ?_
      have hg0 : g ∈ grpBall H ε0 := fun τ i j => (hg τ i j).trans hεe
      obtain ⟨w, hw, rfl⟩ := hon0 g hg0
      rw [lt_min_iff] at hw
      rw [mem_grpBall_iff_norm H hεp] at hg
      change ‖f w - one‖ < ε at hg
      refine ⟨w, ⟨?_, mem_ball_zero_iff.2 hw.1⟩, rfl⟩
      rw [Set.mem_preimage, mem_ball_zero_iff]
      have e1 := H2 w hw.2
      have e2 := hcw (1 - t⁻¹) (by linarith) w
      have e3 : ‖D w‖ ≤ ‖f w - one‖ + ‖f w - one - D w‖ := by
        calc ‖D w‖ = ‖(f w - one) - (f w - one - D w)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have e4 : t⁻¹ * ‖D w‖ < ε := by linarith
      calc ‖D w‖ = t * (t⁻¹ * ‖D w‖) := by field_simp
        _ < t * ε := by gcongr
  have hsq := GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze (F := F) (V := V)
    (A := fun ε => μ (grpBall H ε)) (n := Module.finrank ℝ W) hat hVhom hF hA
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : (0 : ℝ) < ε := hε
  simp only [hVdef]
  rw [tanBall_eq_ball hε, Measure.map_apply D.measurable measurableSet_ball]

end GlobalTheory.SUVol.DensChart
