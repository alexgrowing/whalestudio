import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
import ReciprocityTheory.L2DbarEstimates.LeviForms.Vanish
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MvDivIntegrand

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.VanishAtSimpleZero

open Filter Metric

theorem lintegral_eq_top {n : ℕ} (hn : 0 < n) {g S : V n → ℝ} {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hρ : 0 < ρ) (hg : ∀ᶠ z in 𝓝 (0 : V n), a ≤ g z)
    (hS : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < S z ∧ S z ≤ c * ‖z‖ ^ 2) :
    ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) = ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.and hS)
  have hr0 : 0 < min ε ρ := lt_min hε hρ
  have hsubε : ball (0 : V n) (min ε ρ) ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball (0 : V n) (min ε ρ) ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinf : ∫⁻ z in ball (0 : V n) (min ε ρ), ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) = ⊤ := by
    have hδ : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
    have hT := ReciprocityTheory.L2DbarEstimates.I.vanish_div n hn ReciprocityTheory.L2DbarEstimates.C.mvDiv hr0 hc hδ
    refine top_unique (le_of_tendsto' hT fun k => ?_)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz _ => ?_))
    have hpos : 0 < c * ‖z‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hz) 2)
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_)
    · have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · simp
  have hlow : ENNReal.ofReal a * ∫⁻ z in ball (0 : V n) (min ε ρ),
      ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) ≤
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsubρ)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz hzb => ?_))
    obtain ⟨hgz, hSz⟩ := hball z (hsubε hzb)
    obtain ⟨hS0, hSle⟩ := hSz hz
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hgz (Real.rpow_le_rpow_of_nonpos hS0 hSle (by simp))
      (Real.rpow_nonneg (by positivity) _) (ha.le.trans hgz))
  rw [hinf, ENNReal.mul_top (by simpa using ha)] at hlow
  exact top_unique hlow

theorem vanish_of_simple_zero {n : ℕ} (hn : 0 < n) {u w : V n → ℂ} {s : Fin n → V n → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ContinuousAt u 0) (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hw : DifferentiableAt ℂ w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0)
    (hint : ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-(n : ℝ))) < ⊤) : u 0 = 0 := by
  by_contra hu0
  set f : V n → V n := fun z => (WithLp.toLp 2 fun k => s k z / w z : V n) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.iso_zero hfd.hasFDerivAt hdet hf0
  have hSpos : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < ∑ k, ‖s k z‖ ^ 2 := by
    filter_upwards [closedBall_mem_nhds (0 : V n) hδ] with z hz hz0
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (Ne.symm fun hsum => hz0 ?_)
    refine hiso z hz ?_
    have hk : ∀ k, s k z = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hsum k (Finset.mem_univ _)
      simpa using this
    ext k
    simp [hf, hk k]
  have hbig : ∀ k, ∃ C > 0, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    obtain ⟨C, hC, hCw⟩ := ((hs k).hasFDerivAt.isBigO_sub).exists_pos
    refine ⟨C, hC, hCw.bound.mono fun z hz => ?_⟩
    simpa [hs0 k] using hz
  choose C hC hCb using hbig
  have hSle : ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ (∑ k, C k ^ 2 + 1) * ‖z‖ ^ 2 := by
    filter_upwards [Filter.eventually_all.2 hCb] with z hz
    calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
      _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; simp [mul_pow]
      _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]
  have hpos : 0 < ‖u 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
  have hcont : ContinuousAt (fun z => ‖u z‖ ^ 2) 0 := hu.norm.pow 2
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖u 0‖ ^ 2 / 2 ≤ ‖u z‖ ^ 2 :=
    hcont.eventually (le_mem_nhds (show ‖u 0‖ ^ 2 / 2 < ‖u 0‖ ^ 2 by linarith))
  have htop := lintegral_eq_top hn (g := fun z => ‖u z‖ ^ 2) (S := fun z => ∑ k, ‖s k z‖ ^ 2)
    (by positivity) (by positivity : (0 : ℝ) < ∑ k, C k ^ 2 + 1) hρ hg
    (by filter_upwards [hSpos, hSle] with z h1 h2 hz0 using ⟨h1 hz0, h2⟩)
  exact absurd hint (by rw [htop]; exact lt_irrefl _)

end GlobalTheory.VanishAtSimpleZero

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hdu hds hdw hw0 hs0 hdet hint
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1
  have hb : Metric.ball (0 : V (nd X)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have key := VanishAtSimpleZero.vanish_of_simple_zero hn (u := fun z => u (cpt X x1 z))
    (w := fun z => w0 (cpt X x1 z)) (s := fun k z => s k (cpt X x1 z)) hρ
    ((hdu.differentiableAt hb).continuousAt) (fun k => (hds k).differentiableAt hb)
    (hdw.differentiableAt hb) (by simpa [h0] using hw0) (fun k => by simpa [h0] using hs0 k) hdet hint
  simpa [h0] using key

end GlobalTheory
