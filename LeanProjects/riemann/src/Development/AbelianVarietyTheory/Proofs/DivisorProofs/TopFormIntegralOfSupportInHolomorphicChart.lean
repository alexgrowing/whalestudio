import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasEqChartMeasOfCompatOn
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem hasInt_of_chart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d e' W g hW hWe hd' hT h0 hg hint
  have hSW : MeasurableSet (S ∩ W) := hS.inter hW.measurableSet
  have hsub : S ∩ W ⊆ e'.source := Set.inter_subset_right.trans hWe
  have key : ∀ ε : ℝ, glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) S =
      ∫⁻ v in e' '' (S ∩ W), ENNReal.ofReal (ε * g v) := by
    intro ε
    have hD : MeasurableSet (S \ W) := hS.diff hW.measurableSet
    have hz := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := fun i y => ENNReal.ofReal (ε * d i y))
      (ρ' := fun i y => ENNReal.ofReal (ε * d i y)) (c := 0) ENNReal.zero_ne_top hD
      (fun i y hi hy => by rw [h0 i y hy.1 hy.2 hi]; simp)
    have hz' : glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) (S \ W) = 0 := by
      have := congrArg (fun μ : Measure Y => μ (S \ W)) hz
      simpa only [Measure.restrict_apply_self, zero_smul, Measure.coe_zero, Pi.zero_apply] using this
    rw [← measure_inter_add_diff S hW.measurableSet, hz', add_zero,
      glueMeas_eq_chartMeas_of_compat_on e hd hcov hSW e' (fun y => ENNReal.ofReal (ε * g (e' y))) hsub hd'
        (fun i j y hy hi hj => by
          rw [hT.trans i j y hy.1 hi hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm])
        (fun j y hy hj => by
          rw [hg j y hy.1 hy.2 hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]),
      chartMeas_apply_of_subset _ _ hSW hsub]
    refine setLIntegral_congr_fun (measurableSet_image e' hSW hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [e'.left_inv (hsub hy)]
  refine ⟨fun ε => ?_, ?_⟩
  · rw [key]
    exact (Integrable.const_mul hint _).lintegral_lt_top.ne
  · rw [measureReal_def, measureReal_def, key, key,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    simp

end GlobalTheory.GoodTop
