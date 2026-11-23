import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

lemma ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma norm_inv_ofReal_add_I_sq (t : ℝ) : ‖((t : ℂ) + I)⁻¹ ^ 2‖ = (1 + t ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma tendsto_inv_ofReal_add_I_atTop :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atTop_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma tendsto_inv_ofReal_add_I_atBot :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atBot (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atBot (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atBot_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb

lemma hasDerivAt_neg_inv_ofReal_add_I (t : ℝ) :
    HasDerivAt (fun s : ℝ => -((s : ℂ) + I)⁻¹) (((t : ℂ) + I)⁻¹ ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℂ => w + I) 1 (t : ℂ) := (hasDerivAt_id _).add_const I
  have h2 := (h1.inv (ofReal_add_I_ne_zero t)).neg
  have h3 := h2.comp_ofReal
  convert h3 using 1
  · funext s
    simp
  · rw [inv_pow]
    field_simp

lemma integral_inv_ofReal_add_I_sq : ∫ t : ℝ, ((t : ℂ) + I)⁻¹ ^ 2 = 0 := by
  have hint : MeasureTheory.Integrable (fun t : ℝ => ((t : ℂ) + I)⁻¹ ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · exact (((continuous_ofReal.add continuous_const).inv₀ ofReal_add_I_ne_zero).pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => (norm_inv_ofReal_add_I_sq t).le)
  rw [MeasureTheory.integral_of_hasDerivAt_of_tendsto hasDerivAt_neg_inv_ofReal_add_I hint
    (by simpa using tendsto_inv_ofReal_add_I_atBot.neg)
    (by simpa using tendsto_inv_ofReal_add_I_atTop.neg)]
  simp

theorem cConst_zero : cConst 0 = 0 := by
  unfold cConst hTrans phi
  simp only [mul_zero, neg_zero, Complex.cpow_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul]
  exact integral_inv_ofReal_add_I_sq

end GlobalTheory.HeckeTwo
