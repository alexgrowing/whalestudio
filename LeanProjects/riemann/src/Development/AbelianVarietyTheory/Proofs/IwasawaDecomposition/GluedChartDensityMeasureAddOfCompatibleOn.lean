import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
open MeasureTheory GlobalTheory.ChartGlue
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartGlue

theorem glueMeas_add_of_compat_on : ∀ {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] {n : ℕ} {κ : Type} (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ (ρ ρ' : κ → Y → ℝ≥0∞),
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) →
    (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      ρ' i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ' j y) →
    (∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))) →
    glueMeas e (fun i y => ρ i y + ρ' i y) S = glueMeas e ρ S + glueMeas e ρ' S := by
  intro Y _ _ _ _ n κ e hd hcov S hS ρ ρ' hρ hρ' hAE

  have same : ∀ (τ τ' : κ → Y → ℝ≥0∞), (∀ i y, y ∈ S → τ i y = τ' i y) →
      glueMeas e τ S = glueMeas e τ' S := by
    intro τ τ' h
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := τ) (ρ' := τ') (c := 1) ENNReal.one_ne_top hS
      (fun i y _ hy => by rw [one_mul]; exact h i y hy)
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [Measure.smul_apply, smul_eq_mul, one_mul, Measure.restrict_apply_self] using this

  have compat : ∀ (τ : κ → Y → ℝ≥0∞), (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
      τ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * τ j y) →
      ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (τ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (τ j) y := by
    intro τ hτ i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hτ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have cσ := compat ρ hρ
  have cσ' := compat ρ' hρ'
  have cs : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y + S.indicator (ρ' i) y =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * (S.indicator (ρ j) y + S.indicator (ρ' j) y) := by
    intro i j y hi hj
    rw [mul_add, cσ i j y hi hj, cσ' i j y hi hj]

  have aem : ∀ i (A : Set Y), MeasurableSet A → A ⊆ (e i).source →
      AEMeasurable (fun v => S.indicator (ρ i) ((e i).symm v)) (volume.restrict ((e i) '' A)) := by
    intro i A hAm hA
    have hT : MeasurableSet ((e i).target ∩ (e i).symm ⁻¹' S) := by
      rw [← (e i).image_source_inter_eq']
      exact measurableSet_image (e i) ((e i).open_source.measurableSet.inter hS) Set.inter_subset_left
    have hg := ((aemeasurable_indicator_iff hT).2 (hAE i)).mono_measure
      (Measure.restrict_le_self (s := (e i) '' A))
    refine hg.congr ((ae_restrict_iff' (measurableSet_image (e i) hAm hA)).2
      (Filter.Eventually.of_forall ?_))
    rintro _ ⟨y, hy, rfl⟩
    have ht : (e i) y ∈ (e i).target := (e i).map_source (hA hy)
    show _ = S.indicator (ρ i) ((e i).symm ((e i) y))
    by_cases hs : (e i).symm ((e i) y) ∈ S
    · rw [Set.indicator_of_mem (show (e i) y ∈ (e i).target ∩ (e i).symm ⁻¹' S from ⟨ht, hs⟩),
        Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (show (e i) y ∉ (e i).target ∩ (e i).symm ⁻¹' S from fun h => hs h.2),
        Set.indicator_of_notMem hs]
  have key : glueMeas e (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y) =
      glueMeas e (fun i => S.indicator (ρ i)) + glueMeas e (fun i => S.indicator (ρ' i)) := by
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    rw [Measure.add_apply, glueMeas_apply e _ hd cs i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i hA hAi,
      glueMeas_apply e (fun i => S.indicator (ρ' i)) hd cσ' i hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi, chartMeas_apply_of_subset _ _ hA hAi,
      chartMeas_apply_of_subset _ _ hA hAi]
    exact lintegral_add_left' (aem i A hA hAi) _
  rw [same (fun i y => ρ i y + ρ' i y) (fun i y => S.indicator (ρ i) y + S.indicator (ρ' i) y)
      (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ (fun i => S.indicator (ρ i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    same ρ' (fun i => S.indicator (ρ' i)) (fun i y hy => by simp only [Set.indicator_of_mem hy]),
    key, Measure.add_apply]

end GlobalTheory.ChartGlue
