import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GauIntegrable
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.OneDim

open GlobalTheory.CompanionTheory.Parseval

lemma profile_integrable : Integrable (fun t : ℝ => ((1 + |t|) ^ 2)⁻¹) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  have hp : (0 : ℝ) < 1 + |t| := by positivity
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg hp.le, Real.rpow_two]

lemma wt_eq_comp (a l ζ : ℝ) (ha : 0 < a) :
    wt a l ζ = (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) := by
  simp only [wt, abs_div, abs_of_pos ha]

lemma wt_integrable (a l : ℝ) (ha : 0 < a) : Integrable (wt a l) := by
  have h1 := profile_integrable.comp_div ha.ne'
  have h2 := h1.comp_sub_right l
  exact h2.congr (Filter.Eventually.of_forall fun ζ => (wt_eq_comp a l ζ ha).symm)

lemma wt_integral (a l : ℝ) (ha : 0 < a) :
    ∫ ζ, wt a l ζ = a * ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹ := by
  have h : wt a l = fun ζ => (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) (ζ - l) :=
    funext fun ζ => wt_eq_comp a l ζ ha
  rw [h, integral_sub_right_eq_self (fun t : ℝ => (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) (t / a)) l,
    Measure.integral_comp_div (fun s : ℝ => ((1 + |s|) ^ 2)⁻¹) a, abs_of_pos ha, smul_eq_mul]

lemma wt_le_near {a l ζ : ℝ} (ha : 0 < a) (hl : l ≠ 0) (h : |ζ| < |l| / 2) :
    wt a l ζ ≤ 2 * a / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have h1 : |l| / 2 ≤ |ζ - l| := by
    have := abs_sub_abs_le_abs_sub l ζ
    rw [abs_sub_comm l ζ] at this
    linarith
  have hy : |l| / (2 * a) ≤ |ζ - l| / a := by
    rw [div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hy0 : 0 < |l| / (2 * a) := by positivity
  set y := |ζ - l| / a with hydef
  have hypos : 0 < y := lt_of_lt_of_le hy0 hy
  have h2 : ((1 + y) ^ 2)⁻¹ ≤ y⁻¹ := by
    apply inv_anti₀ hypos
    nlinarith
  have h3 : y⁻¹ ≤ (|l| / (2 * a))⁻¹ := inv_anti₀ hy0 hy
  have h4 : (|l| / (2 * a))⁻¹ = 2 * a / |l| := inv_div _ _
  calc wt a l ζ = ((1 + y) ^ 2)⁻¹ := rfl
    _ ≤ 2 * a / |l| := by rw [← h4]; exact h2.trans h3

lemma gau_le_far {ε l ζ : ℝ} (hε : 0 < ε) (hl : l ≠ 0) (h : |l| / 2 ≤ |ζ|) :
    gau ε ζ ≤ 1 / |l| := by
  have hlp : 0 < |l| := abs_pos.2 hl
  set x := |l| / ε with hx
  have hxp : 0 < x := by positivity
  have hpi := Real.pi_gt_three
  set u := Real.pi * x ^ 2 / 4 with hu
  have h1 : x ≤ Real.exp u := by
    have := Real.add_one_le_exp u
    have hx2 : 3 * x ^ 2 / 4 ≤ u := by
      rw [hu]
      have : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg x]
  have h2 : Real.exp (-u) ≤ x⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hxp h1
  have h3 : -Real.pi * ζ ^ 2 / ε ^ 2 ≤ -u := by
    have hz : |l| ^ 2 / 4 ≤ ζ ^ 2 := by
      rw [← sq_abs ζ]
      nlinarith
    have hux : u = Real.pi * (|l| ^ 2 / 4) / ε ^ 2 := by
      rw [hu, hx]; field_simp
    rw [hux, neg_mul, neg_div, neg_le_neg_iff]
    gcongr
  have h4 : Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ x⁻¹ := (Real.exp_le_exp.2 h3).trans h2
  unfold gau
  calc ε⁻¹ * Real.exp (-Real.pi * ζ ^ 2 / ε ^ 2) ≤ ε⁻¹ * x⁻¹ := by gcongr
    _ = 1 / |l| := by rw [hx]; field_simp

lemma wt_mul_gau_le {ε a l : ℝ} (hε : 0 < ε) (ha : 0 < a) (hl : l ≠ 0) (ζ : ℝ) :
    wt a l ζ * gau ε ζ ≤ 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ := by
  have hlp : 0 < |l| := abs_pos.2 hl
  have hw := wt_nonneg a l ζ
  have hg := gau_nonneg ε ζ hε
  by_cases h : |ζ| < |l| / 2
  · have h1 := mul_le_mul_of_nonneg_right (wt_le_near ha hl h) hg
    have h2 : 0 ≤ 1 / |l| * wt a l ζ := by positivity
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (gau_le_far hε hl (not_lt.1 h)) hw
    have h2 : 0 ≤ 2 * a / |l| * gau ε ζ := by positivity
    rw [mul_comm (wt a l ζ) (1 / |l|)] at h1
    have : wt a l ζ * gau ε ζ ≤ 1 / |l| * wt a l ζ := by
      rw [mul_comm (1 / |l|)]; rw [mul_comm (1 / |l|)] at h1; exact h1
    linarith

theorem wt_gau_bound :
    ∃ C : ℝ, ∀ ε a l : ℝ, 0 < ε → 0 < a → l ≠ 0 →
      ∫ ζ : ℝ, GlobalTheory.CompanionTheory.Parseval.wt a l ζ * GlobalTheory.CompanionTheory.Parseval.gau ε ζ ≤ C * (a / |l|) := by
  refine ⟨2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹, fun ε a l hε ha hl => ?_⟩
  have hlp : 0 < |l| := abs_pos.2 hl
  have hgi := gau_integrable ε hε
  have hwi := wt_integrable a l ha
  have hR : Integrable (fun ζ => 2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ) :=
    (hgi.const_mul _).add (hwi.const_mul _)
  have hL : Integrable (fun ζ => wt a l ζ * gau ε ζ) := by
    refine hR.mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
    · exact (hwi.aestronglyMeasurable).mul hgi.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (wt_nonneg a l ζ) (gau_nonneg ε ζ hε))]
      exact wt_mul_gau_le hε ha hl ζ
  have hmono := integral_mono hL hR (fun ζ => wt_mul_gau_le hε ha hl ζ)
  have hval : ∫ ζ, (2 * a / |l| * gau ε ζ + 1 / |l| * wt a l ζ)
      = (2 + ∫ t : ℝ, ((1 + |t|) ^ 2)⁻¹) * (a / |l|) := by
    rw [integral_add (hgi.const_mul _) (hwi.const_mul _), integral_const_mul, integral_const_mul,
      gau_integral ε hε, wt_integral a l ha]
    ring
  exact hmono.trans_eq hval

end GlobalTheory.CompanionTheory.Parseval.OneDim
