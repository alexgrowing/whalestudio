import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul

noncomputable section
open scoped ContDiff
open Set MeasureTheory

namespace GlobalTheory.ParamIntCut

theorem hasDerivAt_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (s y : ℝ) :
    HasDerivAt (F s) (fderiv ℝ (Function.uncurry F) (s, y) (0, 1)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  exact h1.comp_hasDerivAt y h2

theorem hasDerivAt_intervalIntegral {F : ℝ → ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, F s y)
      (∫ s in a..b, fderiv ℝ (Function.uncurry F) (s, y₀) (0, 1)) y₀ := by
  set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
  have hPc : Continuous (Function.uncurry P) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hsec : ∀ (G : ℝ → ℝ → ℝ), Continuous (Function.uncurry G) → ∀ y, Continuous (fun s => G s y) :=
    fun G hG y => hG.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ (uIcc a b) ×ˢ (Metric.closedBall y₀ 1), ‖Function.uncurry P p‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn hPc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (a := a) (b := b) (F := fun y s => F s y) (F' := fun y s => P s y) (x₀ := y₀)
    (bound := fun _ => C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => (hsec F hFc y).aestronglyMeasurable)
    ((hsec F hFc y₀).intervalIntegrable _ _)
    ((hsec P hPc y₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (t, y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hasDerivAt_snd hF t y)
  exact key.2

theorem contDiff_nat_intervalIntegral (a b : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), ContDiff ℝ ∞ (Function.uncurry F) →
      ContDiff ℝ n (fun y => ∫ s in a..b, F s y)
  | 0, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_intervalIntegral a b h1 y).continuousAt
  | n + 1, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
    have hPs : ContDiff ℝ ∞ (Function.uncurry P) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_intervalIntegral a b h1 y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y => ∫ s in a..b, F s y) = fun y => ∫ s in a..b, P s y :=
      funext fun y => (hasDerivAt_intervalIntegral a b h1 y).deriv
    rw [hd]
    exact contDiff_nat_intervalIntegral a b n P hPs

end GlobalTheory.ParamIntCut

namespace GlobalTheory.PsCo.Pc1

theorem isCutFn_intervalIntegral_and_deriv :
    ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) →
      (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) →
      GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧
        ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  intro F a b hF ⟨R, hR⟩
  have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
  refine ⟨⟨contDiff_infty.2 fun n => GlobalTheory.ParamIntCut.contDiff_nat_intervalIntegral a b n F hF, R, fun y hy => ?_⟩,
    fun y => ?_⟩
  · show ∫ s in a..b, F s y = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => hR s hs y hy)]
    simp
  · rw [(GlobalTheory.ParamIntCut.hasDerivAt_intervalIntegral a b h1 y).deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact ((GlobalTheory.ParamIntCut.hasDerivAt_snd h1 s y).deriv).symm

end GlobalTheory.PsCo.Pc1
