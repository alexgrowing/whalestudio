import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalitiesStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

private lemma twist_estimate_first (a b e M : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 2 ≤ e) (hb : 0 < b)
    (hM : 0 ≤ M) (h : e + a ^ 2 / b ≤ 8 * (1 + M)) :
    0 ≤ a / e ∧ a / e ≤ 1 ∧ 0 < (b * e + a ^ 2) / e ^ 2 ∧ (a / e) ^ 2 ≤ (b * e + a ^ 2) / e ^ 2 ∧
      1 / (1 + M) / 8 ≤ (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one he0]; linarith
  · rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < b * e := by positivity
    linarith
  · have e1 : (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ = 1 / (e + a ^ 2 / b) := by
      field_simp
      ring
    have e2 : 1 / (1 + M) / 8 = 1 / (8 * (1 + M)) := by
      field_simp
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) h

private lemma twist_estimate_second (a b e m : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 300 ≤ e) (hb : 3 / 16 ≤ b)
    (h : e ≤ 2 + 2 * m) :
    e⁻¹ / ((b * e + a ^ 2) / e ^ 2) ≤ 16 / 3 ∧
      1 / (1 + m ^ 2) / 8 ≤ (1 - 5 * ((a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2))) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hb0 : 0 < b := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  have hbe : 3 / 16 * e ≤ b * e := mul_le_mul_of_nonneg_right hb he0.le
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have ha0 : 0 ≤ a ^ 2 := by positivity
  constructor
  · have e1 : e⁻¹ / ((b * e + a ^ 2) / e ^ 2) = e / (b * e + a ^ 2) := by
      field_simp
    rw [e1, div_le_iff₀ hD]
    linarith
  · have e1 : (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2) = a ^ 2 / (b * e + a ^ 2) := by
      field_simp
    have h1 : a ^ 2 / (b * e + a ^ 2) ≤ 1 / 10 := by
      rw [div_le_iff₀ hD]; linarith
    have e2 : 1 / (1 + m ^ 2) / 8 = 1 / 2 * (4 * (1 + m ^ 2))⁻¹ := by
      field_simp
      norm_num
    have h2 : (4 * (1 + m ^ 2))⁻¹ ≤ e⁻¹ := by
      apply inv_anti₀ he0
      nlinarith [sq_nonneg (m - 1 / 4)]
    rw [e1, e2]
    apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)

theorem exists_log_twist : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  intro T hT
  obtain ⟨η, η1, η2, hs, hd, hp, hw⟩ := GlobalTheory.T.exists_concaveTwist_eta_inequalities T hT
  set κ : ℝ → ℝ := fun x => Real.smoothTransition (2 - 16 * x) * (-Real.log (η (-x))) with hκ
  have hloc : ∀ x : ℝ, x < 1 / 16 → κ x = -Real.log (η (-x)) := by
    intro x hx
    simp only [hκ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have hη : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η (-x)) (-η1 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.1
    have h' := HasDerivAt.comp x (h₂ := η) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hη1 : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η1 (-x)) (-η2 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.2
    have h' := HasDerivAt.comp x (h₂ := η1) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hd1 : ∀ x : ℝ, x < 1 / 16 → deriv κ x = η1 (-x) / η (-x) := by
    intro x hx
    have hev : κ =ᶠ[𝓝 x] fun x => -Real.log (η (-x)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hloc y hy
    rw [hev.deriv_eq]
    have h := ((hη x hx).log (hd (-x) (by linarith)).1.ne').neg
    have h2 : HasDerivAt (fun x => -Real.log (η (-x))) (-(-η1 (-x) / η (-x))) x := h
    rw [h2.deriv]; ring
  have hd2 : ∀ x : ℝ, x < 1 / 16 →
      deriv (deriv κ) x = ((-η2 (-x)) * η (-x) + η1 (-x) ^ 2) / η (-x) ^ 2 := by
    intro x hx
    have hev : deriv κ =ᶠ[𝓝 x] fun x => η1 (-x) / η (-x) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hd1 y hy
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun x => η1 (-x) / η (-x)) _ x :=
      (hη1 x hx).div (hη x hx) (hd (-x) (by linarith)).1.ne'
    rw [h2.deriv]; ring
  have hexp : ∀ x : ℝ, x < 1 / 16 → Real.exp (κ x) = (η (-x))⁻¹ := by
    intro x hx
    rw [hloc x hx, Real.exp_neg, Real.exp_log (hd (-x) (by linarith)).1]
  have hwT : ∀ x : ℝ, x ≤ 0 → wT T x = 1 / (1 + (min (-x) (T + 1)) ^ 2) := by
    intro x hx
    unfold wT
    congr 2
    rcases le_total (-x) (T + 1) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  refine ⟨κ, ?_, ⟨Real.log (2 * T + 4), ?_⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 4
    · have h1 : ContDiffAt ℝ ∞ η (-x) :=
        hs.contDiffAt (Ioi_mem_nhds (by linarith))
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => η (-x)) x :=
        ContDiffAt.comp x (g := η) (f := fun x : ℝ => -x) h1 contDiff_neg.contDiffAt
      have h3 := (h2.log (hd (-x) (by linarith)).1.ne').neg
      have h4 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (2 - 16 * x)) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact h4.contDiffAt.mul h3
    · have hev : κ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (1 / 8 : ℝ) < x by linarith)] with y hy
        have hy' : (1 / 8 : ℝ) < y := hy
        simp only [hκ]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    obtain ⟨-, -, h2, -, h3, -⟩ := hp (-x) (by linarith)
    rw [hloc x (by linarith), abs_neg, abs_of_nonneg (Real.log_nonneg (by linarith))]
    apply Real.log_le_log (by linarith)
    have := min_le_right (-x) (T + 1)
    linarith
  · intro x hx
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, h2, h3, -, h5⟩ := hp (-x) (by linarith)
    rw [hd1 x hx', hd2 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_first _ _ _ _ h0 h1 h2 (by linarith) (sq_nonneg _) h5
  · intro x hx1 hx2
    have hx : x ≤ 0 := by linarith
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, -, -, h4, -⟩ := hp (-x) (by linarith)
    obtain ⟨h6, h7⟩ := hw (-x) (by linarith) (by linarith)
    rw [hd2 x hx', hd1 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_second _ _ _ _ h0 h1 (by linarith) h6 h4

end GlobalTheory.OTY
