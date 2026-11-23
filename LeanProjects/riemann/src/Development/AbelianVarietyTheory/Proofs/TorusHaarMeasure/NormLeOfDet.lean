import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrderToIntegral

open Filter Metric

theorem norm_le_of_det {n : ℕ} {f : V n → V n} {f' : V n →L[ℂ] V n} (hf : HasFDerivAt f f' 0)
    (hdet : f'.det ≠ 0) (h0 : f 0 = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ z in 𝓝 (0 : V n), ‖z‖ ≤ K * ‖f z‖ := by
  obtain ⟨K, hKpos, hK⟩ := (f' : V n →ₗ[ℂ] V n).exists_antilipschitzWith (HE.ker_bot_of_det hdet)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK' : ∀ z : V n, ‖z‖ ≤ K * ‖f' z‖ := fun z => by
    have := hK.le_mul_dist z 0
    simpa using this
  have hlo := hf.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hlo] with z hz
  rw [h0, sub_zero, sub_zero] at hz
  have h1 : ‖f' z‖ ≤ ‖f z‖ + 1 / (2 * K) * ‖z‖ := by
    have : ‖f' z‖ ≤ ‖f z‖ + ‖f z - f' z‖ := by
      calc ‖f' z‖ = ‖f z - (f z - f' z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  have h2 : (K : ℝ) * (1 / (2 * K) * ‖z‖) = ‖z‖ / 2 := by field_simp
  have h3 := mul_le_mul_of_nonneg_left h1 hK0.le
  have h4 := hK' z
  rw [mul_add, h2] at h3
  linarith

theorem sum_sq_lower {n : ℕ} (hn : 0 < n) {w : V n → ℂ} {s : Fin n → V n → ℂ}
    (hw : ContinuousAt w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ ∑ k, ‖s k z‖ ^ 2 := by
  have hF : DifferentiableAt ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0 := by
    by_contra hnd
    rw [fderiv_zero_of_not_differentiableAt hnd] at hdet
    apply hdet
    show LinearMap.det (0 : V n →ₗ[ℂ] V n) = 0
    rw [LinearMap.det_zero, finrank_euclideanSpace, Fintype.card_fin, zero_pow (by omega)]
  obtain ⟨K, hK, hle⟩ := norm_le_of_det hF.hasFDerivAt hdet (by ext k; simp [hs0])
  have hpos : 0 < ‖w 0‖ := norm_pos_iff.2 hw0
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖w 0‖ / 2 ≤ ‖w z‖ :=
    (hw.norm.tendsto.eventually (lt_mem_nhds (half_lt_self hpos))).mono fun z hz => le_of_lt hz
  refine ⟨(‖w 0‖ / 2) ^ 2 / K ^ 2, by positivity, ?_⟩
  filter_upwards [hle, hg] with z hz hwz
  have hwz0 : 0 < ‖w z‖ := lt_of_lt_of_le (half_pos hpos) hwz
  have e1 : ‖(WithLp.toLp 2 fun k => s k z / w z : V n)‖ ^ 2 = (∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_div]
    simp [div_pow]
  have h1 : ‖z‖ ^ 2 ≤ K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2) := by
    rw [← e1, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : (‖w 0‖ / 2) ^ 2 ≤ ‖w z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hwz 2
  calc (‖w 0‖ / 2) ^ 2 / K ^ 2 * ‖z‖ ^ 2
      ≤ ‖w z‖ ^ 2 / K ^ 2 * (K ^ 2 * ((∑ k, ‖s k z‖ ^ 2) / ‖w z‖ ^ 2)) := by gcongr
    _ = ∑ k, ‖s k z‖ ^ 2 := by field_simp

theorem lintegral_lt_top {n : ℕ} (hn : 0 < n) {g : V n → ℂ} {S : V n → ℝ} {a : ℕ} {c : ℝ}
    (hc : 0 < c) (hS : ∀ᶠ z in 𝓝 (0 : V n), c * ‖z‖ ^ 2 ≤ S z)
    (hg : g =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖g z‖ ^ 2 * S z ^ (-((a : ℝ) + (n : ℝ) - 1 / 2))) < ⊤ := by
  obtain ⟨C, hC, hO⟩ := hg.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hO.bound.and hS)
  have : Nontrivial (V n) := ⟨⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℂ), 0, by
    intro h
    have h1 := congrArg (fun v : V n => v ⟨0, hn⟩) h
    simp at h1⟩⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set e : ℝ := (a : ℝ) + (n : ℝ) - 1 / 2 with he
  have he0 : 0 ≤ e := by
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have hint := (mvInt n hn ((n : ℝ) - 1 / 2)).2 (by linarith)
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  have hfin : ENNReal.ofReal (C ^ 2 * c ^ (-e)) *
      ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ‖y‖ ^ (-2 * ((n : ℝ) - 1 / 2)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine lt_of_le_of_lt ?_ hfin
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans ?_ (lintegral_mono_set (ball_subset_ball (min_le_right ε 1)))
  refine lintegral_mono_ae ?_
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : V n) (min ε 1))), z ≠ 0 :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (measure_singleton (0 : V n)))
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  obtain ⟨h1, h2⟩ := hball z (ball_subset_ball (min_le_left ε 1) hz)
  have hz : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [ENNReal.ofReal_rpow_of_pos hz, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [norm_pow, norm_norm] at h1
  have h3 : ‖g z‖ ^ 2 ≤ (C * ‖z‖ ^ a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h4 : S z ^ (-e) ≤ (c * ‖z‖ ^ 2) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  have hSz : 0 ≤ S z := le_trans (by positivity) h2
  have h5 : (‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e) = ‖z‖ ^ (-2 * ((n : ℝ) - 1 / 2)) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hz.le,
      ← Real.rpow_add hz]
    congr 1
    rw [he]
    push_cast
    ring
  calc ‖g z‖ ^ 2 * S z ^ (-e) ≤ (C * ‖z‖ ^ a) ^ 2 * (c * ‖z‖ ^ 2) ^ (-e) :=
        mul_le_mul h3 h4 (Real.rpow_nonneg hSz _) (by positivity)
    _ = C ^ 2 * c ^ (-e) * ((‖z‖ ^ a) ^ 2 * (‖z‖ ^ 2) ^ (-e)) := by
        rw [Real.mul_rpow hc.le (by positivity)]
        ring
    _ = _ := by rw [h5]

end GlobalTheory.OrderToIntegral

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanS_of_isBigO : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (a : ℕ)
    (g : Frame X.Ψ r → ℂ), ContinuousOn g X.dom →
    (∀ j, (fun z : V (nd X) => g (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ a) →
    VanS X Fl.xs Fl.s a g := by
  intro r X Xa Fl a g _ hO j
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hw0 : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hs0 : ∀ k, Fl.s k (Fl.xs j) = 0 :=
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, by
      rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]⟩
  have hw : ContinuousAt (fun z : V (nd X) => Fl.w0 (cpt X (Fl.xs j) z)) 0 := by
    refine ContinuousAt.comp (g := Fl.w0) ?_ (FundSetPf.cont_cpt X (Fl.xs j)).continuousAt
    rw [IW.cpt_zero]
    exact hw0.1.continuousOn.continuousAt ((FourierCoefficientDomain.isOpen_dom X).mem_nhds (Fl.xs_mem j))
  obtain ⟨c, hc, hS⟩ := OrderToIntegral.sum_sq_lower
    (w := fun z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun k z => Fl.s k (cpt X (Fl.xs j) z)) hn hw
    (by simpa only [IW.cpt_zero] using Fl.w0_ne j) (by simpa only [IW.cpt_zero] using hs0)
    (Fl.coord j)
  exact OrderToIntegral.lintegral_lt_top hn hc hS (hO j)

end GlobalTheory
