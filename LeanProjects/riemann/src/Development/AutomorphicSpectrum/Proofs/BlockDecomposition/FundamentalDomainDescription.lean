import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

open NumberField MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

open Ad3.R

theorem pri_eq_diagonal (α : ℚˣ) : pri α = diagonal ℚ α := rfl

theorem md_eq (a : Jd) : md a = (ideleModule ℚ a : ℝ) := rfl

theorem lintegral_posReal_weight_lt_top (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ t : {r : ℝ // 0 < r}, ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ) ∂posRealMeasure < ∞ := by
  have hF : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  rw [posRealMeasure_eq_map_expPos, lintegral_map hF measurable_expPos]
  simp only [coe_expPos]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (τ * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ 1 :=
        pow_le_one₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_left _ _)
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ 1 * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (τ * x) := by rw [one_mul, mul_comm, Real.exp_mul]
    · exact Integrable.lintegral_lt_top (integrableOn_exp_mul_Iic h0 0)
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (-((M : ℝ) - τ) * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ (Real.exp x)⁻¹ ^ M :=
        pow_le_pow_left₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_right _ _) M
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (-((M : ℝ) - τ) * x) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    · exact Integrable.lintegral_lt_top (exp_neg_integrableOn_Ioi 0 (sub_pos.2 h1))

def fundD (w : InfinitePlace ℚ) : Set Jd :=
  (fun a => (normOneSplitting w a).1) ⁻¹' normOneFundamentalDomain ℚ

theorem measurableSet_fundD (w : InfinitePlace ℚ) : MeasurableSet (fundD w) := by
  exact (measurableSet_normOneFundamentalDomain ℚ).preimage (measurePreserving_normOneSplitting w).measurable.fst

theorem split_pri_mul (w : InfinitePlace ℚ) (α : ℚˣ) (a : Jd) :
    (normOneSplitting w (pri α * a)).1 = (normOneSplitting w a).1 * diagonalToNormOne ℚ α := by
  have hp : pri α = (normOneSplitting w).symm (diagonalToNormOne ℚ α, 1) := by
    simp only [normOneSplitting_symm_apply, map_one, mul_one, coe_diagonalToNormOne, pri_eq_diagonal]
  have key : normOneSplitting w (pri α) = (diagonalToNormOne ℚ α, 1) := by
    rw [hp]
    exact (normOneSplitting w).apply_symm_apply _
  rw [map_mul, Prod.fst_mul, key]
  exact mul_comm _ _

theorem existsUnique_pri_mul_mem (w : InfinitePlace ℚ) (a : Jd) :
    ∃! α : ℚˣ, pri α * a ∈ fundD w := by
  have h : ∀ α : ℚˣ, pri α * a ∈ fundD w ↔
      (normOneSplitting w a).1 * diagonalToNormOne ℚ α ∈ normOneFundamentalDomain ℚ := by
    intro α
    show (normOneSplitting w (pri α * a)).1 ∈ normOneFundamentalDomain ℚ ↔ _
    rw [split_pri_mul]
  exact (existsUnique_congr h).2 (existsUnique_mul_mem_normOneFundamentalDomain ℚ _)

theorem lintegral_fundD_lt_top (w : InfinitePlace ℚ) (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ a in fundD w, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞ := by
  have hφm : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  have hIm : Measurable ((normOneFundamentalDomain ℚ).indicator (1 : normOneSubgroup ℚ → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_normOneFundamentalDomain ℚ)
  have hpt : ∀ a : Jd, (fundD w).indicator (fun a => ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ)) a =
      (fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ)) (normOneSplitting w a) := by
    intro a
    by_cases ha : a ∈ fundD w
    · have ha' : (normOneSplitting w a).1 ∈ normOneFundamentalDomain ℚ := ha
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem ha', normOneSplitting_apply_snd, md_eq]
    · have ha' : (normOneSplitting w a).1 ∉ normOneFundamentalDomain ℚ := ha
      simp [ha, ha']
  rw [← lintegral_indicator (measurableSet_fundD w), lintegral_congr hpt,
    (measurePreserving_normOneSplitting w).lintegral_comp
      (f := fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ))
      ((hIm.comp measurable_fst).mul (hφm.comp measurable_snd)),
    lintegral_prod_mul hIm.aemeasurable hφm.aemeasurable, lintegral_indicator_one (measurableSet_normOneFundamentalDomain ℚ)]
  exact ENNReal.mul_lt_top (normOneMeasure_normOneFundamentalDomain_lt_top ℚ)
    (lintegral_posReal_weight_lt_top τ M h0 h1)

theorem exists_idele_fundamentalDomain : Ad3.R.D0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  unfold Ad3.R.D0
  exact ⟨fundD w, measurableSet_fundD w, existsUnique_pri_mul_mem w,
    fun τ M h0 h1 => lintegral_fundD_lt_top w τ M h0 h1⟩

end GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

end
