import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLevelSetSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace SliceLevelSet

def moll (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨((k : ℝ) + 1)⁻¹ / 2, ((k : ℝ) + 1)⁻¹, by positivity, by
    have : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    linarith⟩

theorem tendsto_moll_rOut : Tendsto (fun k => (moll k).rOut) atTop (𝓝 0) := by
  show Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0)
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [one_div] using this

def smooth (a : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  convolution ((moll k).normed volume) a (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem contDiff_smooth {a : ℝ → ℝ} (ha : Continuous a) (k : ℕ) : ContDiff ℝ ∞ (smooth a k) :=
  (moll k).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (moll k).contDiff_normed ha.locallyIntegrable

theorem hasCompactSupport_smooth {a : ℝ → ℝ} (has : HasCompactSupport a) (k : ℕ) :
    HasCompactSupport (smooth a k) :=
  (moll k).hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) has

theorem smooth_nonneg {a : ℝ → ℝ} (ha0 : ∀ r, 0 ≤ a r) (k : ℕ) (r : ℝ) : 0 ≤ smooth a k r := by
  unfold smooth
  rw [convolution_def]
  exact integral_nonneg fun u => by
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_nonneg ((moll k).nonneg_normed u) (ha0 _)

theorem integral_smooth {a : ℝ → ℝ} (ha : Continuous a) (has : HasCompactSupport a) (k : ℕ) :
    ∫ r, smooth a k r = ∫ r, a r := by
  unfold smooth
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ)
    ((moll k).continuous_normed.integrable_of_hasCompactSupport (moll k).hasCompactSupport_normed)
    (ha.integrable_of_hasCompactSupport has), (moll k).integral_normed]
  simp

theorem tendsto_smooth {a : ℝ → ℝ} (ha : Continuous a) (r : ℝ) :
    Tendsto (fun k => smooth a k r) atTop (𝓝 (a r)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous tendsto_moll_rOut ha r

theorem sheetSum_abs_nonneg {n d : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ sheetSum I A (fun x s => |F x s|) y := by
  unfold sheetSum
  refine finsum_nonneg fun x => finsum_nonneg fun _ => ?_
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem fatou {n d : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hfin : ∀ y, (fibre I A y).Finite)
    (K : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → (Fin d → ℂ) → ℝ) (T : (Fin n → ℂ) → ℝ)
    (w : ℕ → ℝ → ℝ) (a : ℝ → ℝ) (hw : ∀ r, Tendsto (fun k => w k r) atTop (𝓝 (a r))) {C : ℝ} (hC : 0 ≤ C)
    (hint : ∀ k, Integrable (fun y => sheetSum I A (fun x s => |w k (T x) * K x s y|) y))
    (hle : ∀ k, (∫ y, sheetSum I A (fun x s => |w k (T x) * K x s y|) y) ≤ C) :
    Integrable (fun y => sheetSum I A (fun x s => |a (T x) * K x s y|) y) ∧
      (∫ y, sheetSum I A (fun x s => |a (T x) * K x s y|) y) ≤ C := by
  classical
  set S : ℕ → (Fin d → ℂ) → ℝ := fun k y => sheetSum I A (fun x s => |w k (T x) * K x s y|) y with hS
  set S' : (Fin d → ℂ) → ℝ := fun y => sheetSum I A (fun x s => |a (T x) * K x s y|) y with hS'
  have hlim : ∀ y, Tendsto (fun k => S k y) atTop (𝓝 (S' y)) := by
    intro y
    simp only [hS, hS', CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x _ => ?_
    by_cases hx : ∃ s, IsSheetAt I A x s
    · simp only [dif_pos hx]
      exact ((hw _).mul_const _).abs
    · simp only [dif_neg hx]
      exact tendsto_const_nhds
  have hS0 : ∀ k y, 0 ≤ S k y := fun k y => sheetSum_abs_nonneg _ y
  have hS'0 : ∀ y, 0 ≤ S' y := fun y => sheetSum_abs_nonneg _ y
  have hmeas : AEStronglyMeasurable S' volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).1) (ae_of_all _ hlim)
  have hlint : ∫⁻ y, ENNReal.ofReal (S' y) ≤ ENNReal.ofReal C := by
    calc ∫⁻ y, ENNReal.ofReal (S' y) = ∫⁻ y, liminf (fun k => ENNReal.ofReal (S k y)) atTop := by
          refine lintegral_congr fun y => ?_
          exact ((ENNReal.continuous_ofReal.tendsto _).comp (hlim y)).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (S k y)) atTop :=
          lintegral_liminf_le' fun k => (hint k).1.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun k => ?_))
          rw [← ofReal_integral_eq_lintegral_ofReal (hint k) (ae_of_all _ (hS0 k))]
          exact ENNReal.ofReal_le_ofReal (hle k)
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    calc ∫⁻ y, ‖S' y‖ₑ = ∫⁻ y, ENNReal.ofReal (S' y) :=
          lintegral_congr fun y => Real.enorm_eq_ofReal (hS'0 y)
      _ ≤ ENNReal.ofReal C := hlint
      _ < ⊤ := ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hS'0) hmeas]
    exact ENNReal.toReal_le_of_le_ofReal hC hlint

end SliceLevelSet

theorem SliceLevelSet.proof (h₁ : SliceLevelSetSmooth.Statement) : SliceLevelSet.Statement := by
  intro n e h W g ℓ A ψ hW hg hℓ hA hψ hψs
  set a : ℝ → ℝ := fun r => |ψ r| with ha_def
  have ha : Continuous a := hψ.abs
  have has : HasCompactSupport a := hψs.comp_left (g := fun r : ℝ => |r|) abs_zero
  have ha0 : ∀ r, 0 ≤ a r := fun r => abs_nonneg _
  have hM0 : 0 ≤ ∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) y :=
    integral_nonneg fun y => SliceLevelSet.sheetSum_abs_nonneg _ y
  have hC : 0 ≤ (∫ y, chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
      (fun _ x => Real.log (h.dualNorm x)) y) * ∫ r, a r :=
    mul_nonneg hM0 (integral_nonneg ha0)
  have hk := fun k => h₁ n e h W g ℓ A (SliceLevelSet.smooth a k) hW hg hℓ hA
    (SliceLevelSet.contDiff_smooth ha k) (SliceLevelSet.hasCompactSupport_smooth has k)
    (SliceLevelSet.smooth_nonneg ha0 k)
  have habs : ∀ k, ∫ r, |SliceLevelSet.smooth a k r| = ∫ r, a r := fun k => by
    rw [← SliceLevelSet.integral_smooth ha has k]
    exact integral_congr_ae (ae_of_all _ fun r => abs_of_nonneg (SliceLevelSet.smooth_nonneg ha0 k r))
  have key := SliceLevelSet.fatou (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA)
    (fun x s y => gradDens (fun _ : Fin e => (fun x => Real.log (h.dualNorm x)) ∘ s)
      ((fun x => Real.log (h.dualNorm x)) ∘ s) ((fun x => Real.log (h.dualNorm x)) ∘ s) y)
    (fun x => Real.log (h.dualNorm x)) (SliceLevelSet.smooth a) a (SliceLevelSet.tendsto_smooth ha) hC
    (fun k => (hk k).1) (fun k => (habs k) ▸ (hk k).2)
  have hfun : ∀ (x : Fin n → ℂ) (c : ℝ), |a (Real.log (h.dualNorm x)) * c| = |ψ (Real.log (h.dualNorm x)) * c| :=
    fun x c => by simp only [ha_def, abs_mul, abs_abs]
  simp only [hfun] at key
  exact key

end

end GroundTheory.Heights₂.Heights
