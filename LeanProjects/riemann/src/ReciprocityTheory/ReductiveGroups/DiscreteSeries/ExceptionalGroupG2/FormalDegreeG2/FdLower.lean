import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLowerA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdScale
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ProdSubLtEqFactorial
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PBridge
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by
  have hscale : ∀ t : ℕ, 1 ≤ t → ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) =
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) := by
    intro t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hs : 0 < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht')
    rw [lintegral_pcoord_smul _ hs, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have e : (t : ℝ) ^ (pOf ε * qOf ε) * ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = 1 := by
      rw [inv_pow, pow_mul (Real.sqrt _) 2, Real.sq_sqrt ht'.le, mul_inv_cancel₀ (pow_ne_zero _ ht'.ne')]
    rw [e, ENNReal.ofReal_one, one_mul]
  rw [Filter.liminf_congr (Filter.eventually_atTop.2 ⟨1, hscale⟩)]
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2 * Jac ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y))) := by
    intro t
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    exact ((continuous_norm.comp ((fdl_inner_continuous _ (T t) _ _).comp (continuous_const_smul _))).pow 2).mul
      ((jac_continuous ε).comp (continuous_const_smul _))
  refine le_trans ?_ (lintegral_liminf_le hmeas)
  rw [← fdl_gauss ε]
  refine lintegral_mono fun y => ?_
  have h1 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
      (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    have h2 : Filter.Tendsto (fun t : ℕ => ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t)
        (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) Filter.atTop
        (nhds (ENNReal.ofReal (‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)).tendsto _).comp (hlim y)
    have e : ‖((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, sq, ← Real.exp_add]
      congr 1
      ring
    rw [e] at h2
    exact h2
  rw [← h1.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun t => ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)))

end ReciprocityTheory.ChartRestriction.DS.G2
