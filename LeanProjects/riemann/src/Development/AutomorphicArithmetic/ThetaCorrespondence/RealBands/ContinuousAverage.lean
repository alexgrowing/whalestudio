import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Weight
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsCompactBall

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem wt_pos' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : 0 < wt g := by
  unfold wt; positivity

private theorem wt_mul_le {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) : wt (g * h) ≤ wt g * wt h := by
  unfold wt
  rw [← mul_pow]
  have h1 := (isCompact_ball n ε).2.1 (umat g) (umat h)
  have e : umat (g * h) = umat g * umat h := rfl
  rw [e]
  have a := Real.sqrt_nonneg (hs (umat g))
  have b := Real.sqrt_nonneg (hs (umat h))
  refine pow_le_pow_left₀ (by positivity) ?_ _
  nlinarith

private theorem wt_inv' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : wt g⁻¹ = wt g := by
  unfold wt
  rw [(isCompact_ball n ε).2.2.1 g]

private theorem continuous_wt' {n : ℕ} (ε : Fin n → Bool) : Continuous fun g : UJ ε => wt g := by
  unfold wt
  exact (continuous_const.add (isCompact_ball n ε).2.2.2.sqrt).pow _

private theorem norm_translate_le {n : ℕ} {ε : Fin n → Bool} {f : UJ ε → ℂ} {C : ℝ}
    (hC : ∀ g, ‖f g‖ * wt g ≤ C) (x m y : UJ ε) : ‖f (x * m * y)‖ ≤ C * wt x * wt y * (wt m)⁻¹ := by
  have h1 : wt m ≤ wt x * wt (x * m * y) * wt y := by
    calc wt m = wt (x⁻¹ * (x * m * y) * y⁻¹) := by congr 1; group
      _ ≤ wt (x⁻¹ * (x * m * y)) * wt y⁻¹ := wt_mul_le _ _
      _ ≤ wt x⁻¹ * wt (x * m * y) * wt y⁻¹ :=
        mul_le_mul_of_nonneg_right (wt_mul_le _ _) (wt_pos' _).le
      _ = _ := by rw [wt_inv', wt_inv']
  rw [← div_eq_mul_inv, le_div_iff₀ (wt_pos' m)]
  calc ‖f (x * m * y)‖ * wt m ≤ ‖f (x * m * y)‖ * (wt x * wt (x * m * y) * wt y) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖f (x * m * y)‖ * wt (x * m * y) * (wt x * wt y) := by ring
    _ ≤ C * (wt x * wt y) :=
        mul_le_mul_of_nonneg_right (hC _) (mul_pos (wt_pos' _) (wt_pos' _)).le
    _ = _ := by ring

theorem UpperTheory.Lit.Cusp.continuous_average :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : UJ ε → ℂ), Continuous f → Decays f → Integrable f (muG ε) ∧
      ∀ (S : Subgroup (UJ ε)) (ν : Measure (UJ ε)), IsHaarSub (S : Set (UJ ε)) ν →
        ∀ x, Continuous fun y => ∫ m, f (x * m * y) ∂ν := by
  intro n ε f hf ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (wt_pos' _).le) (hC 1)
  refine ⟨?_, fun S ν hν x => ?_⟩
  · have hH : IsHaarSub ((⊤ : Subgroup (UJ ε)) : Set (UJ ε)) (muG ε) := by
      haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
      exact GlobalTheory.Dec.isHaarSub_univ (muG ε)
    refine ((integrable_wt n ε ⊤ _ hH).const_mul C).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [← div_eq_mul_inv, le_div_iff₀ (wt_pos' g)]
    exact hC g
  · rw [continuous_iff_continuousAt]
    intro y₀
    refine continuousAt_of_dominated (bound := fun m => C * wt x * (wt y₀ + 1) * (wt m)⁻¹) ?_ ?_
      ((integrable_wt n ε S ν hν).const_mul _) ?_
    · exact Eventually.of_forall fun y =>
        (hf.comp ((continuous_const.mul continuous_id).mul continuous_const)).aestronglyMeasurable
    · have hn : ∀ᶠ y in 𝓝 y₀, wt y < wt y₀ + 1 :=
        (continuous_wt' ε).continuousAt.eventually (gt_mem_nhds (lt_add_one _))
      filter_upwards [hn] with y hy
      refine Eventually.of_forall fun m => (norm_translate_le hC x m y).trans ?_
      have := wt_pos' x
      have := wt_pos' m
      gcongr
    · exact Eventually.of_forall fun m => (hf.comp (continuous_const.mul continuous_id)).continuousAt
