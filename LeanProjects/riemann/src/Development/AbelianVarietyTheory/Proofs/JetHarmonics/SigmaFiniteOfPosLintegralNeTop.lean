import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SideNormalisedGap
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.KFinDecayOfDecInf

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureSigmaFinite

theorem sigmaFinite_of_pos_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have h1 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (meas_ge_le_lintegral_div hg.aemeasurable h0 h1).trans_lt (ENNReal.div_lt_top hfin h0)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x)
    refine Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

theorem measurable_mul_pair (k r : ℕ) :
    Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨h, hpos, hmeas, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hne : ∀ y, h y ≠ 0 := fun y => (hpos y).ne'
  have hF : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ((h (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) : NNReal) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal.comp hmeas).comp (measurable_mul_pair k r)
  have hq' : ∫⁻ x, (h x : ℝ≥0∞) ∂μG =
      ∫⁻ x, (∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS) ∂ν :=
    hq _ (measurable_coe_nnreal_ennreal.comp hmeas)

  refine sigmaFinite_of_pos_lintegral_ne_top
    (g := fun x => ∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS)
    hF.lintegral_prod_right' ?_ ?_
  · intro x hx
    have hfm : Measurable fun s : Formalism.QuantumDeterminants.Mt k r =>
        ((h (fun i j => (Matrix.of s * Matrix.of x) i j) : NNReal) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hmeas).comp
        (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          fun_prop)
    rw [lintegral_eq_zero_iff hfm] at hx
    apply hS
    rw [← Measure.measure_univ_eq_zero]
    have h0 := ae_iff.1 hx
    simpa [hne] using h0
  · rw [← hq']
    exact (hint.trans ENNReal.one_lt_top).ne

end GlobalTheory.QuotientMeasureSigmaFinite
