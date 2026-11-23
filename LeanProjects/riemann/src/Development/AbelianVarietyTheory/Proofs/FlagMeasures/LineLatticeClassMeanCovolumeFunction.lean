import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDualStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.MeanCov

theorem lintegral_div_inv (κ : ℝ) (hκ : 0 < κ) (w : ℝ → ENNReal) :
    ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) / ENNReal.ofReal t
      = ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  have himg : (fun t : ℝ => κ / t) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos hκ ht
    · intro hs
      have hs0 : s ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hs)
      refine ⟨κ / s, div_pos hκ hs, ?_⟩
      field_simp
  have hder : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun t : ℝ => κ / t) (κ * -(t ^ 2)⁻¹) (Set.Ioi 0) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ht)
    have h1 : HasDerivAt (fun y : ℝ => κ * y⁻¹) (κ * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0).const_mul κ
    have h2 : (fun y : ℝ => κ / y) = fun y => κ * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
    rw [h2]
    exact h1.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => κ / t) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := ne_of_gt (Set.mem_Ioi.mp ha)
    have hb0 : b ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hb)
    have hk0 : κ ≠ 0 := ne_of_gt hκ
    simp only at hab
    field_simp at hab
    nlinarith [hab]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun s => w (κ / s) / ENNReal.ofReal s)
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht' : 0 < t := Set.mem_Ioi.mp ht
  have hq : 0 < κ / t := div_pos hκ ht'
  have habs : |κ * -(t ^ 2)⁻¹| = κ / t * t⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos hκ, abs_of_pos (by positivity)]
    field_simp
  have hkk : κ / (κ / t) = t := by
    field_simp
  simp only
  rw [habs, hkk, ENNReal.ofReal_mul hq.le, ENNReal.ofReal_inv_of_pos ht', div_eq_mul_inv, div_eq_mul_inv]
  have hne : ENNReal.ofReal (κ / t) ≠ 0 := by simpa using hq
  calc ENNReal.ofReal (κ / t) * (ENNReal.ofReal t)⁻¹ * (w t * (ENNReal.ofReal (κ / t))⁻¹)
      = (ENNReal.ofReal (κ / t) * (ENNReal.ofReal (κ / t))⁻¹) * (w t * (ENNReal.ofReal t)⁻¹) := by ring
    _ = w t * (ENNReal.ofReal t)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]

theorem measurable_detNorm (E : Type) [Field E] [NumberField E] (j : ℕ) :
    Measurable (detNorm E j) := by
  have hc : Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2) := by
    refine continuous_finset_prod _ (fun w _ => ?_)
    exact ((Continuous.matrix_det
      (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w)) (continuous_apply w)).norm).pow 2
  exact hc.measurable

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] (j : ℕ) (hj : 1 ≤ j) :
    ∀ᵐ g ∂(haarGL E j), 0 < detNorm E j g := by
  have hm := GlobalTheory.FlagBase.MeanCov.measurable_detNorm E j
  rw [ae_iff]
  have hs : MeasurableSet {g : MatInf E j | ¬ 0 < detNorm E j g} :=
    (measurableSet_lt measurable_const hm).compl
  have hz : ∀ g ∈ {g : MatInf E j | ¬ 0 < detNorm E j g},
      ENNReal.ofReal ((detNorm E j g)⁻¹ ^ j) = 0 := by
    intro g hg
    have hnn : 0 ≤ detNorm E j g := by
      unfold detNorm
      exact Finset.prod_nonneg fun w _ => by positivity
    have h0 : detNorm E j g = 0 := le_antisymm (not_lt.mp hg) hnn
    rw [h0, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]
  unfold haarGL
  refine (withDensity_apply _ hs).trans ?_
  refine (setLIntegral_congr_fun hs hz).trans ?_
  simp

theorem latMean_covAt : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 1 ≤ j → ∀ w : ℝ → ENNReal, Measurable w → latMean E j (fun L => w (covAt E j L)) = glVol E j * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal t := by
  intro E _ _ hE j hj w hw
  unfold latMean glVol
  rw [← ENNReal.tsum_mul_right]
  refine tsum_congr fun c => ?_
  obtain ⟨κ, hκ, hL⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 (Quot.out c).1 (Quot.out c).2
  have hF : Measurable fun t : ℝ => w (κ / t) := hw.comp (measurable_const.div measurable_id)
  have hd : (haarGL E j).withDensity (fun g => w (covAt E j (latAt E j (Quot.out c).1 g)))
      = (haarGL E j).withDensity (fun g => w (κ / detNorm E j g)) := by
    refine withDensity_congr_ae ?_
    filter_upwards [GlobalTheory.FlagBase.MeanCov.ae_detNorm_pos E j hj] with g hg
    rw [(hL g hg).2.1]
  rw [hd]
  refine (GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE j hj _ (Quot.out c).2 (fun t => w (κ / t)) hF).trans ?_
  congr 1
  exact GlobalTheory.FlagBase.MeanCov.lintegral_div_inv κ hκ w

end GlobalTheory.FlagBase.MeanCov
