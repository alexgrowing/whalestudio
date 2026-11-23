import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set
open scoped Pointwise

noncomputable section

namespace SphereMean

theorem setAverage_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ENNReal}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (s : Set α) (g : α → ℝ) :
    ⨍ x in s, g x ∂(c • μ) = ⨍ x in s, g x ∂μ := by
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  rw [setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_measure, measureReal_def,
    measureReal_def]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [mul_inv]
  field_simp

section Linear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem setAverage_comp_linearEquiv (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by
  have hmap : (map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving L μ (map L μ) := ⟨L.continuous.measurable, rfl⟩
  have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ) := by
    rw [setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def,
      measureReal_def, he.map_apply]
  have h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν := isAddLeftInvariant_eq_smul _ _
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν
  rw [h1, h2]
  rw [show (addHaarScalarFactor (map L μ) ν • ν) =
      ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]
  exact setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g

end Linear

def sqNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ j, ‖x j‖ ^ 2

def ballSet (n : ℕ) (s : ℝ) : Set (Fin n → ℂ) := {x | sqNorm x < s}

theorem sqNorm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_sqNorm (n : ℕ) : Continuous (sqNorm (n := n)) := by
  unfold sqNorm
  fun_prop

theorem measurable_sqNorm (n : ℕ) : Measurable (sqNorm (n := n)) :=
  (continuous_sqNorm n).measurable

theorem isOpen_ballSet (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) :=
  isOpen_lt (continuous_sqNorm n) continuous_const

theorem measurableSet_ballSet (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) :=
  (isOpen_ballSet n s).measurableSet

theorem sqNorm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℂ) : sqNorm (c • x) = c ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem ballSet_eq_smul {n : ℕ} {s : ℝ} (hs : 0 < s) : ballSet n s = √s • ballSet n 1 := by
  have h : 0 < √s := Real.sqrt_pos.mpr hs
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ h.ne']
  simp only [ballSet, mem_ofPred_eq, sqNorm_smul, inv_pow, Real.sq_sqrt hs.le]
  rw [inv_mul_lt_iff₀ hs, mul_one]

theorem finrank_fun_complex (n : ℕ) : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem volume_ballSet {n : ℕ} {s : ℝ} (hs : 0 < s) :
    volume (ballSet n s) = ENNReal.ofReal (s ^ n) * volume (ballSet n 1) := by
  rw [ballSet_eq_smul hs, addHaar_smul, finrank_fun_complex, pow_mul, Real.sq_sqrt hs.le,
    abs_of_nonneg (pow_nonneg hs.le n)]

theorem ballSet_subset_closedBall (n : ℕ) : ballSet n 1 ⊆ Metric.closedBall 0 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  have h1 : ‖x j‖ ^ 2 ≤ sqNorm x :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ‖x j‖ ^ 2 < 1 := lt_of_le_of_lt h1 hx
  nlinarith [norm_nonneg (x j)]

theorem volume_ballSet_one_ne_top (n : ℕ) : volume (ballSet n 1) ≠ ⊤ :=
  (measure_mono (ballSet_subset_closedBall n)).trans_lt measure_closedBall_lt_top |>.ne

theorem volume_ballSet_one_pos (n : ℕ) : 0 < volume (ballSet n 1) :=
  (isOpen_ballSet n 1).measure_pos volume ⟨0, by simp [ballSet, sqNorm]⟩

end SphereMean

end

end GroundTheory.Heights₂.Heights
