import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

theorem contDiff_invChart {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ ∞ fun w : ℂ => if w = 0 then 0 else φ w⁻¹ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hc.isCompact.isBounded
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    have hr : (0 : ℝ) < 1 / (max R 0 + 1) := by positivity
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with v hv
    by_cases hv0 : v = 0
    · simp [hv0]
    · rw [if_neg hv0]
      refine image_eq_zero_of_notMem_tsupport fun h => ?_
      have h1 := hR h
      rw [Metric.mem_closedBall, dist_zero_right, norm_inv] at h1
      rw [Metric.mem_ball, dist_zero_right] at hv
      have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h2 : ‖v‖⁻¹ > max R 0 + 1 := by
        rw [gt_iff_lt, lt_inv_comm₀ (by positivity) hn]
        simpa [one_div] using hv
      linarith [le_max_left R 0]
  · have e : (fun v : ℂ => if v = 0 then 0 else φ v⁻¹) =ᶠ[𝓝 w] fun v => φ v⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds hw] with v hv
      rw [if_neg hv]
    exact (hφ.contDiffAt.comp w (contDiffAt_inv ℝ hw)).congr_of_eventuallyEq e

theorem contDiff_sphere_elim {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (k : sphere.ι) :
    ContDiff ℝ ∞ fun s : V 1 => ((sphere.e k).symm s).elim 0 φ := by
  have hp : ContDiff ℝ ∞ fun s : V 1 => s 0 :=
    ((EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).restrictScalars ℝ).contDiff
  change Fin 2 at k
  fin_cases k
  · exact hφ.comp hp
  · have e : (fun s : V 1 => ((sphere.e (1 : Fin 2)).symm s).elim 0 φ) =
        (fun w : ℂ => if w = 0 then 0 else φ w⁻¹) ∘ fun s : V 1 => s 0 := by
      funext s
      show (ReciprocityTheory.AnForm.M.projectiveLineChartAtInfinity.invFun (EuclideanSpace.equiv (Fin 1) ℂ s)).elim 0 φ = _
      simp only [ReciprocityTheory.AnForm.M.projectiveLineChartAtInfinity, Function.comp_apply]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rfl
    exact e ▸ (contDiff_invChart hφ hc).comp hp

theorem smoothOn_extend_sphere : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (φ : ℂ → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport φ → (famAtlas A).SmoothOn univ fun y => ((y.2.elim 0 φ : ℝ) : ℂ) := by
  intro M _ A φ hφ hc
  rintro ⟨j, k⟩
  have d : ContDiff ℝ ∞ fun x : V (1 + 1) => ((appendV 1 1).symm x).2 :=
    contDiff_snd.comp (((appendV 1 1).symm : V (1 + 1) →L[ℂ] V 1 × V 1).restrictScalars ℝ).contDiff
  have h := Complex.ofRealCLM.contDiff.comp ((contDiff_sphere_elim hφ hc k).comp d)
  exact h.contDiffOn

end GlobalTheory.BcUnique
