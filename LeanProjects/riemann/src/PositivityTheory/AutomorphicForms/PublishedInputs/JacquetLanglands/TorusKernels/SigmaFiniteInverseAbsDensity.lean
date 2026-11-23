import Mathlib

noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

abbrev Y1 : Type := {y : ℝ // y ≠ 0}

def nu1 : Measure Y1 := (Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|)

def scl (t : ℝ) (ht : t ≠ 0) (y : Y1) : Y1 := ⟨t * y.1, mul_ne_zero ht y.2⟩

theorem measurableSet_ne : MeasurableSet {y : ℝ | y ≠ 0} := by
  exact (measurableSet_singleton (0 : ℝ)).compl

theorem measurableEmbedding_val : MeasurableEmbedding (Subtype.val : Y1 → ℝ) := by
  exact MeasurableEmbedding.subtype_coe (s := {y : ℝ | y ≠ 0}) measurableSet_ne

private theorem map_withDensity_comp_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ENNReal) :
    Measure.map f (μ.withDensity fun x => g (f x)) = (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map]

theorem map_val_inverse_abs_density_eq :
    Measure.map Subtype.val nu1 = (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal (1 / |y|) := by
  have hr : Set.range (Subtype.val : Y1 → ℝ) = {0}ᶜ := by
    ext x
    simp
  have h0 : Measure.map (Subtype.val : Y1 → ℝ) (Measure.comap Subtype.val volume) = volume := by
    rw [measurableEmbedding_val.map_comap, hr]
    exact Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton 0))
  unfold nu1
  rw [map_withDensity_comp_of_measurableEmbedding measurableEmbedding_val _ (fun y : ℝ => ENNReal.ofReal (1 / |y|)), h0]

theorem map_mul_rho (t : ℝ) (ht : t ≠ 0) :
    Measure.map (t * ·) ((volume : Measure ℝ).withDensity fun y => ENNReal.ofReal (1 / |y|)) =
      (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal (1 / |y|) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => t * x) :=
    (Homeomorph.mulLeft₀ t ht).measurableEmbedding
  have hmeas : Measurable fun y : ℝ => ENNReal.ofReal (1 / |t * y|) := by fun_prop
  have hpt : (volume : Measure ℝ).withDensity (fun y : ℝ => ENNReal.ofReal (1 / |y|)) =
      ENNReal.ofReal |t| • (volume : Measure ℝ).withDensity (fun y : ℝ => ENNReal.ofReal (1 / |t * y|)) := by
    rw [← withDensity_smul _ hmeas]
    congr 1
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (abs_nonneg t), abs_mul]
    congr 1
    rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr ht), one_mul]
  have hc : ENNReal.ofReal |t| * ENNReal.ofReal |t⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg t), ← abs_mul, mul_inv_cancel₀ ht, abs_one, ENNReal.ofReal_one]
  conv_lhs => rw [hpt]
  rw [Measure.map_smul, map_withDensity_comp_of_measurableEmbedding hemb volume (fun y : ℝ => ENNReal.ofReal (1 / |y|)),
    Real.map_volume_mul_left ht, withDensity_smul_measure, smul_smul, hc, one_smul]

instance sigmaFinite_inverse_abs_density : SigmaFinite nu1 :=
  SigmaFinite.of_map nu1 measurableEmbedding_val.measurable.aemeasurable (by rw [map_val_inverse_abs_density_eq]; infer_instance)

theorem measurePreserving_scl (t : ℝ) (ht : t ≠ 0) : MeasurePreserving (scl t ht) nu1 nu1 := by
  have hm : Measurable (scl t ht) := by
    show Measurable fun y : Y1 => (⟨t * y.1, mul_ne_zero ht y.2⟩ : Y1)
    exact Measurable.subtype_mk ((measurable_const_mul t).comp measurable_subtype_coe)
  refine ⟨hm, ?_⟩
  have hv : Measure.map Subtype.val (Measure.map (scl t ht) nu1) = Measure.map Subtype.val nu1 := by
    rw [Measure.map_map measurableEmbedding_val.measurable hm]
    have hcomp : Subtype.val ∘ scl t ht = (fun x : ℝ => t * x) ∘ Subtype.val := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_mul t) measurableEmbedding_val.measurable,
      map_val_inverse_abs_density_eq, map_mul_rho t ht]
  rw [← measurableEmbedding_val.comap_map (Measure.map (scl t ht) nu1), hv,
    measurableEmbedding_val.comap_map]

end UpperTheory.Esk.UnipotentIntegrandLemmas
