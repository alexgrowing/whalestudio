import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ENNReal
open MeasureTheory Set

noncomputable section

namespace FSInv

open CP

variable {N : ℕ}

lemma measurable_lineOf : Measurable (lineOf (N := N)) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  rw [continuousOn_iff_continuous_domRestrict]
  have : Set.domRestrict ({0}ᶜ : Set (Fin (N + 1) → ℂ)) (lineOf (N := N)) =
      Projectivization.mk' ℂ ∘ (fun v : ({0}ᶜ : Set (Fin (N + 1) → ℂ)) =>
        (⟨v.1, v.2⟩ : {v : Fin (N + 1) → ℂ // v ≠ 0})) := by
    funext v
    exact lineOf_of_ne v.2
  rw [this]
  exact ProjTopology.continuous_mk'.comp (continuous_subtype_val.subtype_mk _)

lemma insertNth_smul_chartVec (i : Fin (N + 1)) (t : ℂ) (z : Fin N → ℂ) :
    Fin.insertNth i t (t • z) = t • chartVec i z := by
  funext j
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp [chartVec]
  · simp [chartVec]

theorem AmbChart.proof (hL : LinChange.Statement) (hR : Radial.Statement) : AmbChart.Statement := by
  intro N i f hf
  have hlin := measurable_lineOf (N := N)
  have hdens : Measurable fun v : Fin (N + 1) → ℂ => ENNReal.ofReal (ambDensity v) := by
    unfold ambDensity normSq2; fun_prop
  rw [ambMeasure, lintegral_withDensity_eq_lintegral_mul _ hdens
    (show Measurable fun v => f (lineOf v) from hf.comp hlin)]
  set G : (Fin (N + 1) → ℂ) → ℝ≥0∞ := fun v => ENNReal.ofReal (ambDensity v) * f (lineOf v) with hGdef
  have hG : Measurable G := hdens.mul (hf.comp hlin)
  change ∫⁻ v, G v = _
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) i
  have he : ∀ t w, e.symm (t, w) = Fin.insertNth i t w := fun t w => rfl
  rw [← (volume_preserving_piFinSuccAbove (fun _ : Fin (N + 1) => ℂ) i).symm.lintegral_comp_emb
    e.symm.measurableEmbedding, Measure.volume_eq_prod,
    lintegral_prod (fun p => G (e.symm p)) (hG.comp e.symm.measurable).aemeasurable]
  set F : ℂ → (Fin N → ℂ) → ℝ≥0∞ := fun t z =>
    ENNReal.ofReal (‖t‖ ^ (2 * N) * (1 / (1 + ‖t‖ ^ 2 * (1 + normSqSum z)) ^ (N + 2))) with hFdef
  have hF : Measurable (Function.uncurry F) := by
    simp only [hFdef, normSqSum]; fun_prop
  have key : ∀ t : ℂ, t ≠ 0 → ∫⁻ w, G (e.symm (t, w)) = ∫⁻ z, F t z * f (chartInv i z) := by
    intro t ht
    have hdet : LinearMap.det (t • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) = t ^ N := by
      rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_fin_fun, mul_one]
    rw [hL N (t • LinearMap.id) (by rw [hdet]; exact pow_ne_zero _ ht) (fun w => G (e.symm (t, w)))
      (hG.comp (e.symm.measurable.comp measurable_prodMk_left)), hdet,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    simp only [LinearMap.smul_apply, LinearMap.id_apply, he, hGdef, hFdef,
      insertNth_smul_chartVec]
    have hv : t • chartVec i z ≠ 0 := smul_ne_zero ht (chartVec_ne_zero i z)
    have hline : lineOf (t • chartVec i z) = chartInv i z := by
      rw [lineOf_of_ne hv, chartInv, Projectivization.mk_eq_mk_iff']
      exact ⟨t, rfl⟩
    have hnorm : Complex.normSq (t ^ N) = ‖t‖ ^ (2 * N) := by
      rw [Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm]
    rw [hline, ← mul_assoc, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), hnorm, ambDensity,
      normSq2_smul, normSq2_chartVec]
    rfl
  rw [lintegral_congr_ae ((Measure.ae_ne volume (0 : ℂ)).mono fun t ht => key t ht),
    lintegral_lintegral_swap (hF.mul (hf.comp ((measurable_chartInv i).comp measurable_snd))).aemeasurable]
  rw [← lintegral_const_mul _ (show Measurable fun z : Fin N → ℂ =>
    f (chartInv i z) * ENNReal.ofReal (1 / (1 + normSqSum z) ^ (N + 1)) from
      (hf.comp (measurable_chartInv i)).mul (by unfold normSqSum; fun_prop))]
  refine lintegral_congr fun z => ?_
  rw [lintegral_mul_const _ (show Measurable fun t => F t z from hF.comp measurable_prodMk_right)]
  have hs : 0 < 1 + normSqSum z := by linarith [normSqSum_nonneg z]
  simp only [hFdef]
  rw [hR N _ hs]
  ring
