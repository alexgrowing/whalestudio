import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustionStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.HormanderBall

open ReciprocityTheory.ChartRestriction.G.AR.Up.HE

theorem measurable_wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) : Measurable (wdb n j g) := by
  unfold wdb
  exact (((measurable_fderiv_apply_const ℝ g _).add
    ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)

theorem norm_sum_mul_conj_sq_le {n : ℕ} (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)
  calc ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem hormander_ball : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  intro n c r t φ F0 ht hφ hF0 hlevi
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨X, hX⟩ := GlobalTheory.T.ball_exists_etaleStein_exhaustion n c r
  set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef
  have hh : Measurable h := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)
  have hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hhdef, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)
    have h1 := hlevi y hy ξ
    have h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
      rw [le_inv_mul_iff₀ ht]; exact h1
    have h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2 := by positivity
    calc (∑ j, ‖wdb n j F0 y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2
        ≤ (∑ j, ‖wdb n j F0 y‖ ^ 2) * (t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re) := by
          gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hest⟩ := hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1)
    (by rw [hX]; exact smoothR_val hφ)
    (fun x ξ => by
      rw [hX, levi_val hU]
      exact le_trans (by positivity) (hlevi x.1 x.2 ξ))
    (by rw [hX]; exact smooth_val hF0)
    (hh.comp measurable_subtype_coe) (fun x ξ => by
      have := hb x.1 x.2 ξ
      rw [hX]
      show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re
      simp only [dbarDot, db_val hU]
      rw [levi_val hU]
      exact this)
  refine ⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩
  have hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n) := by
    rw [hX] at hest; exact hest
  have h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤
      ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v)) := by
    rw [← lintegral_val hU, ← lintegral_val hU]
    simpa [wint, extendByZeroOnSubset_apply_coe] using hest'
  refine h4.trans (le_of_eq ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hU.measurableSet fun v _ => ?_
  rw [hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end GlobalTheory.HormanderBall
