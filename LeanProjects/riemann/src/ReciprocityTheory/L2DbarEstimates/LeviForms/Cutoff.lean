import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

namespace SmoothCutoff

noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bump_of_le_half {s : ℝ} (h : s ≤ 1 / 2) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem bump_of_one_le {s : ℝ} (h : 1 ≤ s) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (x := 20 * (1 - s)) (by linarith), mul_zero]

theorem bump_of_mem {s : ℝ} (h1 : 11 / 20 ≤ s) (h2 : s ≤ 19 / 20) : bump s = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s

theorem prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t :=
  (bump_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim : deriv prim = bump := funext fun t => (prim_hasDerivAt t).deriv

theorem prim_contDiff : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩

theorem prim_monotone : Monotone prim :=
  monotone_of_deriv_nonneg (fun t => (prim_hasDerivAt t).differentiableAt)
    (fun t => by rw [deriv_prim]; exact bump_nonneg t)

theorem prim_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : prim t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  apply bump_of_le_half
  have := (Set.mem_uIcc.1 hs)
  rcases this with h | h <;> linarith [h.1, h.2]

theorem prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (bump_continuous.intervalIntegrable _ _) (bump_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := t) (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact bump_of_one_le hs.1

theorem prim_one_ge : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith

theorem prim_nonneg (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this

theorem prim_le (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this

noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1

theorem chi_hasDerivAt (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1

theorem isCutoff_chi : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]

end SmoothCutoff

theorem cutoff : CutoffStatement := ⟨SmoothCutoff.chi, SmoothCutoff.isCutoff_chi⟩

end ReciprocityTheory.L2DbarEstimates.I
