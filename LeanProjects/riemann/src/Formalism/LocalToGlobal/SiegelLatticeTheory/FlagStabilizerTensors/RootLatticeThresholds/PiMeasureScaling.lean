import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.PiMeasureScaling

theorem sf_smul (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • (volume : Measure ℂ)) := by
  lift c to NNReal using hc
  first
  | exact (inferInstance : SigmaFinite (c • (volume : Measure ℂ)))
  | (rw [← ENNReal.smul_def]; infer_instance)

theorem pi_smul_vol {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) = (∏ i, c i) • (volume : Measure (ι → ℂ)) := by
  haveI : ∀ i, SigmaFinite (c i • (volume : Measure ℂ)) := fun i => sf_smul (c i) (hc i)
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi_pi, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem map_scale (s : ℂ) (hs : s ≠ 0) :
    (volume : Measure ℂ).map (fun z => s * z) = ENNReal.ofReal (Complex.normSq s)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ s) = Complex.normSq s := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hpos : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ s) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  exact h

theorem reindex_mp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (fun (y : κ → ℂ) (i : ι) => y (e i)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : ι => ℂ) e.symm
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e.symm)) =
      fun (y : κ → ℂ) (i : ι) => y (e i) := by
    funext y i
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℂ) y (e i)
    simpa using h1
  rw [hf] at h
  exact h

theorem pi_reindex_scale {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) :
    (Measure.pi (fun _ : κ => a • (volume : Measure ℂ))).map (fun y i => s i * y (e i)) =
      (∏ i, a * ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
  classical
  have hk : Measure.pi (fun _ : κ => a • (volume : Measure ℂ)) =
      (∏ _k : κ, a) • (volume : Measure (κ → ℂ)) := pi_smul_vol (fun _ => a) (fun _ => ha)
  have hsc : (volume : Measure (ι → ℂ)).map (fun x i => s i * x i) =
      (∏ i, ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
    haveI : ∀ i, SigmaFinite (Measure.map (fun x => s i * x) (volume : Measure ℂ)) := fun i => by
      rw [map_scale _ (hs i)]
      exact sf_smul _ ENNReal.ofReal_ne_top
    rw [volume_pi, Measure.pi_map_pi (fun i => (measurable_const_mul (s i)).aemeasurable)]
    simp_rw [map_scale _ (hs _)]
    rw [pi_smul_vol _ (fun i => ENNReal.ofReal_ne_top), volume_pi]
  have hcomp : (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) =
      (fun (x : ι → ℂ) i => s i * x i) ∘ (fun (y : κ → ℂ) (i : ι) => y (e i)) := rfl
  rw [hk, Measure.map_smul, hcomp,
    ← Measure.map_map (measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul (s i))
      (reindex_mp e).measurable, (reindex_mp e).map_eq, hsc, smul_smul]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_congr e]

end Formalism.L2.SG.PiMeasureScaling

end
