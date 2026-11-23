import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentSkew

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.HaarLeftInv

def leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin j) (Fin j) ℂ →ₗ[ℝ] Matrix (Fin j) (Fin j) ℂ where
  toFun T := A * T
  map_add' S T := Matrix.mul_add _ _ _
  map_smul' c T := by simp

theorem det_leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (leftMat A) = (‖A.det‖ ^ 2) ^ j := by
  have h := (GlobalTheory.TwoSidedJac.real_jacobians).1 j j A 1 (leftMat A) (fun T => by
    show A * T = A * T * 1
    rw [Matrix.mul_one])
  rw [h, Matrix.det_one, norm_one, one_pow, mul_one, ← pow_mul]

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def leftMul (a : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin j → Fin j → ℂ) :=
  LinearMap.pi fun w => (show (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) from
    leftMat (Matrix.of (a w))).comp (LinearMap.proj w)

theorem det_leftMul (a : MatInf E j) : LinearMap.det (leftMul E j a) = detNorm E j a ^ j := by
  calc LinearMap.det (leftMul E j a)
      = ∏ w, LinearMap.det (leftMat (Matrix.of (a w))) := LinearMap.det_pi _
    _ = ∏ w, (‖(Matrix.of (a w)).det‖ ^ 2) ^ j := by simp only [det_leftMat]
    _ = (∏ w, ‖(Matrix.of (a w)).det‖ ^ 2) ^ j := Finset.prod_pow _ _ _
    _ = detNorm E j a ^ j := by rfl

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [hw, Matrix.det_mul, norm_mul, mul_pow]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact ((Continuous.matrix_det (continuous_apply w)).norm).pow 2

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem measurePreserving_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (a : MatInf E j), 0 < detNorm E j a → MeasurableEmbedding (fun g : MatInf E j => a * g) ∧ MeasurePreserving (fun g : MatInf E j => a * g) (haarGL E j) (haarGL E j) := by
  intro E _ _ j a ha
  have : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    isAddHaar_volume E j
  have hdet0 : LinearMap.det (leftMul E j a) ≠ 0 := by
    rw [det_leftMul]
    exact pow_ne_zero _ ha.ne'
  have hemb : MeasurableEmbedding ⇑(leftMul E j a) :=
    ((LinearMap.toContinuousLinearMap (leftMul E j a)).toContinuousLinearEquivOfDetNeZero
      hdet0).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpos : 0 < (detNorm E j a)⁻¹ ^ j := pow_pos (inv_pos.mpr ha) j
  have hmap : Measure.map (leftMul E j a) (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) =
      ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, det_leftMul, ← inv_pow,
      abs_of_pos hpos]
  have hc0 : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hctop : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((continuous_detNorm E j).measurable.inv).pow_const j).ennreal_ofReal
  have hρf : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ,
      ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) =
        ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have hx : detNorm E j (leftMul E j a x) = detNorm E j a * detNorm E j x := detNorm_mul E j a x
    rw [hx, mul_inv, mul_pow, ENNReal.ofReal_mul hpos.le]
  have hV : Measure.map (leftMul E j a)
      ((volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) =
      (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, withDensity_apply _ (hemb.measurable hs),
      withDensity_apply _ hs]
    calc ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s, ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)
        = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s,
              ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) := by
          simp_rw [hρf]
          rw [lintegral_const_mul' _ _ hctop, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop,
            one_mul]
      _ = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) ∂(Measure.map (leftMul E j a) volume) := by
          rw [setLIntegral_map hs hρ hemb.measurable]
      _ = ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  exact ⟨hemb, hemb.measurable, hV⟩

end GlobalTheory.HaarLeftInv
