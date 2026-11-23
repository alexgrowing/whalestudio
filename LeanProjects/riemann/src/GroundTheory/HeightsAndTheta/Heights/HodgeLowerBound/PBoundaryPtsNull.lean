import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryPtsNull
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem volume_coord_hyperplane {m : ℕ} (i : Fin m) : volume {t : Fin m → ℂ | t i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem differentiable_segre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    Differentiable ℂ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  unfold segre
  fun_prop

theorem BoundaryPtsNull.proof : BoundaryPtsNull.Statement := by
  intro II T _ _ K _ ι _ Ω _ _ E _ _ D Ψ _
  classical
  let F : Fin D.nCharts → (Fin D.n → ℂ) → Fin D.n → ℂ := fun a t j =>
    Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0
  let s : Fin D.nCharts → Fin D.n → Set (Fin D.n → ℂ) := fun a i =>
    {t | ‖t‖ < 1 ∧ t i = 0 ∧ Ψ (segre ((D.chart a).γ t)) 0 ≠ 0}
  refine measure_mono_null (t := ⋃ a, ⋃ i, F a '' s a i) ?_
    (measure_iUnion_null fun a => measure_iUnion_null fun i => ?_)
  · rintro y ⟨z, hz, hzB, hΨ⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
    have hγB : (D.chart a).γ t ∈ D.Bd := by
      have := D.bd_torus _ hzB (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
      convert this using 1
      funext p
      simp only [torusSmul]
      rw [inv_mul_cancel_left₀ (hc _)]
    have ht1 : ‖t‖ < 1 := by linarith
    obtain ⟨i, -, hi⟩ := ((D.chart a).boundary t (mem_ball_zero_iff.2 ht1)).1 hγB
    rw [segre_torusSmul, map_smul] at hΨ
    have h0 := congrFun hΨ 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hv0 : Ψ (segre ((D.chart a).γ t)) 0 ≠ 0 := fun h => by simp [h] at h0
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨i, t, ⟨ht1, hi, hv0⟩, ?_⟩⟩
    funext j
    have hj := congrFun hΨ j.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hj
    show Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0 = y j
    rw [div_eq_iff hv0, ← hj]
    linear_combination (-(Ψ (segre ((D.chart a).γ t)) j.succ)) * h0
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (fun t ht => ht.2.1) (volume_coord_hyperplane i))
    intro t ht
    have hγ : DifferentiableAt ℂ (D.chart a).γ t :=
      ((D.chart a).analytic t (mem_ball_zero_iff.2 ht.1)).differentiableAt
    have hS : DifferentiableAt ℂ (fun t => segre ((D.chart a).γ t)) t := by
      have := differentiable_segre.differentiableAt.comp t hγ
      exact this
    have hG : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t))) t := by
      have := (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp t hS
      exact this
    have hF : DifferentiableAt ℂ (F a) t := by
      refine differentiableAt_pi.2 fun j => ?_
      have hn : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) j.succ) t :=
        differentiableAt_pi.1 hG j.succ
      have hd : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) 0) t :=
        differentiableAt_pi.1 hG 0
      show DifferentiableAt ℂ
        (fun t => Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0) t
      simp only [div_eq_mul_inv]
      exact hn.mul (hd.inv ht.2.2)
    exact (hF.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
