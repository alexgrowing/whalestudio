import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem polyB_summable_norm_mul_pow {a : ℕ → ℂ} (ha : PolyB a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖a n‖ * r ^ n := by
  obtain ⟨C, A, h⟩ := ha
  have hs : Summable fun n : ℕ => C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by
    refine Summable.mul_left _ (Summable.add ?_ ?_)
    · exact summable_pow_mul_geometric_of_norm_lt_one A (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    · exact summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 _)) (fun n => ?_) hs
  have hb : ((n : ℝ) + 1) ^ A ≤ 2 ^ A * ((n : ℝ) ^ A + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, zero_add, one_pow]
      have : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
      nlinarith [pow_nonneg (le_refl (0:ℝ)) A]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : ((n : ℝ) + 1) ^ A ≤ (2 * n) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
      rw [mul_pow] at this
      nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) A]
  have hC : 0 ≤ C := le_trans (norm_nonneg _) ((h 0).trans (by simp))
  calc ‖a n‖ * r ^ n ≤ C * ((n : ℝ) + 1) ^ A * r ^ n :=
        mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
    _ ≤ C * (2 ^ A * ((n : ℝ) ^ A + 1)) * r ^ n := by gcongr
    _ = C * 2 ^ A * ((n : ℝ) ^ A * r ^ n + r ^ n) := by ring

theorem exists_upperHalfPlane_exp_eq {q : ℂ} (h0 : q ≠ 0) (h1 : ‖q‖ < 1) :
    ∃ τ : ℍ, ∀ n : ℕ, cexp (2 * π * Complex.I * n * τ) = q ^ n := by
  have hπ : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have him : 0 < (Complex.log q / (2 * π * Complex.I)).im := by
    have e : Complex.log q / (2 * π * Complex.I) = -Complex.I * Complex.log q / (2 * π) := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [e]
    have : (-Complex.I * Complex.log q / (2 * π)).im = - (Complex.log q).re / (2 * π) := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im]
      simp
    rw [this, Complex.log_re]
    have hl : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr h0) h1
    have : 0 < 2 * π := by positivity
    apply div_pos (by simpa using hl) this
  refine ⟨⟨_, him⟩, fun n => ?_⟩
  have : 2 * π * Complex.I * (n : ℂ) * ((⟨_, him⟩ : ℍ) : ℂ) = n * Complex.log q := by
    simp only [UpperHalfPlane.coe_mk]
    field_simp
  rw [this, Complex.exp_nat_mul, Complex.exp_log h0]

theorem qs_injective : ∀ a b : ℕ → ℂ, PolyB a → PolyB b → qs a = qs b → a = b := by
  intro a b ha hb hab
  set c : ℕ → ℂ := fun n => a n - b n with hcdef
  have hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → Summable fun n : ℕ => ‖c n‖ * r ^ n := by
    intro r h0 h1
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg h0 _)) (fun n => ?_)
      ((polyB_summable_norm_mul_pow ha h0 h1).add (polyB_summable_norm_mul_pow hb h0 h1))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg h0 _)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c with hp
  have hrad : ((1 / 2 : NNReal) : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_summable_norm ?_
    have := hsum (1 / 2) (by norm_num) (by norm_num)
    refine this.congr (fun n => ?_)
    rw [hp, FormalMultilinearSeries.ofScalars_norm]
    simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simp) hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hval : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → p.sum q = 0 := by
    intro q h0 h1
    obtain ⟨τ, hτ⟩ := exists_upperHalfPlane_exp_eq h0 h1
    have ha' : Summable fun n => a n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow ha (norm_nonneg q) h1)
    have hb' : Summable fun n => b n * q ^ n := Summable.of_norm (by
      simpa [norm_mul, norm_pow] using polyB_summable_norm_mul_pow hb (norm_nonneg q) h1)
    have e := congrFun hab τ
    simp only [qs, hτ] at e
    show ∑' n, p n (fun _ => q) = 0
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, hcdef, sub_mul]
    rw [Summable.tsum_sub ha' hb', e, sub_self]
  have hcont : ContinuousAt p.sum 0 := hP.continuousOn.continuousAt (EMetric.ball_mem_nhds 0 hpos)
  have h0 : p.sum 0 = 0 := by
    have hev : p.sum =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) one_pos)]
        with q hq0 hq1
      exact hval q hq0 (by simpa using hq1)
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
  have hloc : p.sum =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact h0
    · exact hval q hq0 (by simpa using hq)
  have hpz : p = 0 := hP.hasFPowerSeriesAt.eq_zero_of_eventually hloc
  funext n
  have hn : p n = 0 := by rw [hpz]; rfl
  have : c n = 0 := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp hn
  exact sub_eq_zero.mp this

end GlobalTheory.EisM
