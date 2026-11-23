import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushC

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_hq (k : ℕ) (T' : ℝ) : Continuous (fun p : (Fin k → ℂ) × ℝ => hq k T' p.1 p.2) := by
  unfold hq
  refine continuous_fst.prodMk ?_
  refine (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    ((continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp
      ((continuous_apply i).comp continuous_fst)).add continuous_const))).mul ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem hq_periodic (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : hq k T' y (θ + 2 * Real.pi) = hq k T' y θ := by
  have key : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have e : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I = θ * Complex.I + 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold hq
  rw [key]

theorem lint_shift (P : ℝ → ℝ≥0∞) (hP : Measurable P) (hper : ∀ θ, P (θ + 2 * Real.pi) = P θ) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), P θ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, P θ := by
  have hπ := Real.pi_pos
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume))]
  have h1 : Set.Ioc 0 (2 * Real.pi) = Set.Ioc 0 Real.pi ∪ Set.Ioc Real.pi (2 * Real.pi) :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have h2 : Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) 0 ∪ Set.Ioc 0 Real.pi :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  rw [h1, h2, lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl), add_comm]
  congr 1
  have hmp : MeasurePreserving (fun x : ℝ => x + 2 * Real.pi) volume volume := measurePreserving_add_right volume _
  have hpre : (fun x : ℝ => x + 2 * Real.pi) ⁻¹' Set.Ioc Real.pi (2 * Real.pi) = Set.Ioc (-Real.pi) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩; constructor <;> linarith
    · rintro ⟨a, b⟩; constructor <;> linarith
  have := hmp.setLIntegral_comp_preimage (s := Set.Ioc Real.pi (2 * Real.pi)) measurableSet_Ioc hP
  rw [hpre] at this
  rw [← this]
  exact lintegral_congr fun a => hper a

theorem hypTh : HypTh := by
  intro k T' hT'
  let L : EuclideanSpace ℂ (Fin k) ≃L[ℝ] (Fin k → ℂ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℂ)
  set μ' : Measure (Fin k → ℂ) := (volume : Measure (EuclideanSpace ℂ (Fin k))).map L with hμ'def
  have hH : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map _
  have hμ' : μ' = Measure.addHaarScalarFactor μ' volume • volume := Measure.isAddLeftInvariant_eq_smul μ' volume
  have hc0 : 0 < Measure.addHaarScalarFactor μ' volume :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume
  set c := Measure.addHaarScalarFactor μ' volume with hcdef
  clear_value c
  refine ⟨(1 / 2) * (c : ℝ≥0∞), ?_, ?_, fun E hE => ?_⟩
  · exact mul_ne_zero (by simp) (by exact_mod_cast hc0.ne')
  · exact ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  have hF : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
    hf.comp (continuous_hq k T').measurable
  rw [← lintegral_indicator_one hE, ← hypMeas_eq k T' hf]
  unfold hypMeas hqI
  rw [mul_assoc]
  congr 1
  have e1 : ∀ (y : EuclideanSpace ℂ (Fin k)) (θ : ℝ),
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
        ((fun i => y i), (Real.sqrt (‖y‖ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I)) =
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' (L y) θ) := by
    intro y θ
    rw [← normSq_sum_eq]
    rfl
  simp_rw [e1]
  have hG : Measurable (fun y : Fin k → ℂ =>
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    hF.lintegral_prod_right'
  set G : (Fin k → ℂ) → ℝ≥0∞ := fun y =>
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ) with hGdef
  have eM : (∫⁻ y : EuclideanSpace ℂ (Fin k), G (L y)) = ∫⁻ y, G y ∂μ' :=
    (lintegral_map hG L.continuous.measurable).symm
  rw [eM, hμ', lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [hGdef]
  dsimp only
  rw [lintegral_lintegral_swap hF.aemeasurable]
  exact lint_shift _ hF.lintegral_prod_left' fun θ => by simp only [hq_periodic]

end PI.RhsWLim.W
