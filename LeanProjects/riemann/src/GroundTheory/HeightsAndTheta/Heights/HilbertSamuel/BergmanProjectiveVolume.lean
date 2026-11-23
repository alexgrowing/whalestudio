import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {N : ℕ}

namespace ProjFS

lemma isOpen_chartVec_ne (i j : Fin (N + 1)) : IsOpen {z : Fin N → ℂ | chartVec i z j ≠ 0} :=
  isOpen_ne_fun (contDiff_chartVec_apply ℂ i j).continuous continuous_const

lemma transition_transition {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    transition j i (transition i j z) = z := by
  change chartCoord i (chartInv j (chartCoord j (chartInv i z))) = z
  rw [chartInv_chartCoord j (show chartInv i z ∈ chartDomain j from hz), chartCoord_chartInv]

lemma chartVec_transition_apply {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (m : Fin (N + 1)) : chartVec j (transition i j z) m = (chartVec i z j)⁻¹ * chartVec i z m := by
  rw [chartVec_transition i j hz]; rfl

lemma image_transition (j : Fin (N + 1)) :
    transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} = {y | chartVec j y 0 ≠ 0} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change chartVec j (transition 0 j z) 0 ≠ 0
    rw [chartVec_transition_apply hz, chartVec_self, mul_one]
    exact inv_ne_zero hz
  · intro hy
    refine ⟨transition j 0 y, ?_, transition_transition hy⟩
    change chartVec 0 (transition j 0 y) j ≠ 0
    rw [chartVec_transition_apply hy, chartVec_self, mul_one]
    exact inv_ne_zero hy

lemma injOn_transition (i j : Fin (N + 1)) :
    Set.InjOn (transition i j) {z : Fin N → ℂ | chartVec i z j ≠ 0} := fun z hz z' hz' h => by
  rw [← transition_transition hz, h, transition_transition hz']

lemma ae_chartVec_ne (j : Fin (N + 1)) : ∀ᵐ y : Fin N → ℂ, chartVec j y 0 ≠ 0 := by
  obtain h | ⟨k, hk⟩ := Fin.eq_self_or_eq_succAbove j 0
  · exact Filter.Eventually.of_forall fun y => by rw [h, chartVec_self]; exact one_ne_zero
  · rw [ae_iff]
    have hset : {y : Fin N → ℂ | ¬ chartVec j y 0 ≠ 0} = Function.eval k ⁻¹' {0} := by
      ext y
      simp only [ne_eq, not_not, mem_setOf_eq, mem_preimage, Function.eval, mem_singleton_iff]
      rw [hk, chartVec_succAbove]
    rw [hset, volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem setLIntegral_fsMeasure_chartDomain (j : Fin (N + 1)) (g : CP N → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y) := by
  have hD : MeasurableSet (chartDomain (N := N) j) := (isOpen_chartDomain j).measurableSet
  rw [fsMeasure, setLIntegral_map hD hg (measurable_chartInv 0), fsChartMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_fsVolumeDensity 0).ennreal_ofReal
      (show Measurable (fun x => g (chartInv 0 x)) from hg.comp (measurable_chartInv 0))
      (hD.preimage (measurable_chartInv 0))]
  have hW : chartInv 0 ⁻¹' chartDomain j = {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := rfl
  rw [hW]
  have hae : (Set.univ : Set (Fin N → ℂ)) =ᵐ[volume]
      transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := by
    rw [image_transition]
    filter_upwards [ae_chartVec_ne j] with y hy
    exact propext ⟨fun _ => hy, fun _ => trivial⟩
  conv_rhs => rw [← setLIntegral_univ]
  rw [setLIntegral_congr hae,
    lintegral_image_eq_lintegral_normSq_det_mul (transition 0 j) _ (isOpen_chartVec_ne 0 j)
      (fun z hz => analyticAt_transition 0 j hz) (injOn_transition 0 j)]
  refine setLIntegral_congr_fun (isOpen_chartVec_ne 0 j).measurableSet fun z hz => ?_
  have h1 : chartInv j (transition 0 j z) = chartInv 0 z :=
    chartInv_chartCoord j (show chartInv 0 z ∈ chartDomain j from hz)
  have h2 : fsVolumeDensity 0 z =
      Complex.normSq (jacC (transition 0 j) z).det * fsVolumeDensity j (transition 0 j z) := by
    rw [fsVolumeDensity_transition 0 j hz,
      det_fderiv_real_eq_normSq _ z (differentiableAt_transition 0 j hz),
      abs_of_nonneg (Complex.normSq_nonneg _)]
  simp only [Pi.mul_apply]
  rw [h1, h2, ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
  ring

end ProjFS

def fsVolume (N : ℕ) : SmoothVolume (projAtlas N) where
  μ := fsMeasure N
  isProb := inferInstance
  dens := fsVolumeDensity
  smooth (j : Fin (N + 1)) := by
    have h : fsVolumeDensity (N := N) j =
        fun z => (N.factorial : ℝ) / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) :=
      funext fun z => fsVolumeDensity_eq j z
    rw [h]
    have hs : ContDiff ℝ ∞ (normSqSum (N := N)) := by
      unfold normSqSum; exact contDiff_normSqSum
    refine (contDiff_const.div (contDiff_const.mul ((contDiff_const.add hs).pow _))
      fun z => ?_).contDiffOn
    have := one_add_normSqSum_pos z
    have := Real.pi_pos
    positivity
  pos (j : Fin (N + 1)) y _ := fsVolumeDensity_pos j y
  chart_lintegral (j : Fin (N + 1)) g hg := by
    change ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y in univ, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y)
    rw [setLIntegral_univ]
    exact ProjFS.setLIntegral_fsMeasure_chartDomain j g hg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
