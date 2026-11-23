import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal

noncomputable section

variable {n : ℕ} {U : Set (V n)}

theorem ext_glue (hU : IsOpen U) (g G : V n → ℂ) (hg : DifferentiableOn ℂ g U)
    (hgn : ∀ W : Set (V n), IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0)
    (hG : DifferentiableOn ℂ G {y | y ∈ U ∧ g y ≠ 0})
    (hL : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧
      ∫⁻ y in ball p ρ \ {y | g y = 0}, ENNReal.ofReal (‖G y‖ ^ 2) < ⊤) :
    ∃ G' : V n → ℂ, DifferentiableOn ℂ G' U ∧ Set.EqOn G' G {y | y ∈ U ∧ g y ≠ 0} := by
  classical
  have hloc : ∀ p ∈ U, ∃ ρ > 0, ball p ρ ⊆ U ∧ ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball p ρ) ∧
      Set.EqOn F G (ball p ρ \ {y | g y = 0}) := by
    intro p hp
    obtain ⟨ρ, hρ, hsub, hint⟩ := hL p hp
    obtain ⟨F, hF, hFeq⟩ := ReciprocityTheory.L2DbarEstimates.ext n p ρ g G (hg.mono hsub)
      (hG.mono fun y hy => ⟨hsub hy.1, hy.2⟩) hint
    exact ⟨ρ, hρ, hsub, F, hF, hFeq⟩
  choose ρ hρ hsub F hF hFeq using hloc
  have agree : ∀ y (hy : y ∈ U) z (hz : z ∈ U) x, x ∈ ball y (ρ y hy) → x ∈ ball z (ρ z hz) →
      F y hy x = F z hz x := by
    intro y hy z hz x hxy hxz
    by_contra hne
    have hcy : ContinuousAt (F y hy) x :=
      (hF y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hxy)
    have hcz : ContinuousAt (F z hz) x :=
      (hF z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hxz)
    have hev : ∀ᶠ t in 𝓝 x, F y hy t ≠ F z hz t := by
      first
        | exact hcy.eventually_ne hcz hne
        | exact ((hcy.sub hcz).eventually_ne (sub_ne_zero.mpr hne)).mono fun t ht h => ht (sub_eq_zero.mpr h)
    have hs : {t | t ∈ ball y (ρ y hy) ∧ t ∈ ball z (ρ z hz) ∧ F y hy t ≠ F z hz t} ∈ 𝓝 x :=
      Filter.inter_mem (isOpen_ball.mem_nhds hxy) (Filter.inter_mem (isOpen_ball.mem_nhds hxz) hev)
    obtain ⟨W, hWs, hWo, hxW⟩ := _root_.mem_nhds_iff.mp hs
    obtain ⟨t, htW, hgt⟩ := hgn W hWo (fun t ht => hsub y hy (hWs ht).1) ⟨x, hxW⟩
    have h1 := hFeq y hy ⟨(hWs htW).1, hgt⟩
    have h2 := hFeq z hz ⟨(hWs htW).2.1, hgt⟩
    exact (hWs htW).2.2 (h1.trans h2.symm)
  refine ⟨fun y => if hy : y ∈ U then F y hy y else 0, ?_, ?_⟩
  · intro y hy
    have hnb : ball y (ρ y hy) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hρ y hy))
    have heq : (fun y => if hy : y ∈ U then F y hy y else 0) =ᶠ[𝓝 y] F y hy := by
      filter_upwards [hnb] with x hx
      have hxU : x ∈ U := hsub y hy hx
      rw [dif_pos hxU]
      exact agree x hxU y hy x (mem_ball_self (hρ x hxU)) hx
    exact (((hF y hy).differentiableAt hnb).congr_of_eventuallyEq heq).differentiableWithinAt
  · intro y hy
    show (if h : y ∈ U then F y h y else 0) = G y
    rw [dif_pos hy.1]
    exact hFeq y hy.1 ⟨mem_ball_self (hρ y hy.1), hy.2⟩

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
