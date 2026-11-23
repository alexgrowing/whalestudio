import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set Metric

noncomputable section

variable {n : ℕ} {Ω : Set (V n)} {g : V n → ℂ}

theorem not_loc_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : ∀ z ∈ Ω, ¬ g =ᶠ[𝓝 z] 0 := by
  intro z hz hzero
  obtain ⟨z0, hz0, hgz0⟩ := hne
  set u := {w : V n | ∀ᶠ y in 𝓝 w, g y = (0 : V n → ℂ) y} with hu_def
  set v := {w : V n | ∀ᶠ y in 𝓝 w, ¬ (g =ᶠ[𝓝 y] 0)} with hv_def
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen v := isOpen_setOfPred_eventually_nhds
  have hcov : Ω ⊆ u ∪ v := by
    intro w hw
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ w hw
    have hfr : ∃ᶠ y in 𝓝 w, g =ᶠ[𝓝 y] 0 := by
      rw [Filter.Frequently]; intro h; exact hnv h
    obtain ⟨y, hy1, hy2⟩ := (hfr.and_eventually (ball_mem_nhds w hρ)).exists
    have hB0 := C.ident n (ball w ρ) g y isOpen_ball (convex_ball w ρ) (hg.mono hB) hy2 hy1
    exact hnu (Filter.eventually_of_mem (ball_mem_nhds w hρ) fun x hx => hB0 hx)
  have hv0 : z0 ∈ v := by
    have hct : ContinuousAt g z0 := hg.continuousOn.continuousAt (hΩ.mem_nhds hz0)
    have hev : ∀ᶠ y in 𝓝 z0, g y ≠ 0 := hct.eventually_ne hgz0
    exact hev.mono fun y hy h => hy (by simpa using h.eq_of_nhds)
  obtain ⟨w, -, hwu, hwv⟩ := hc u v hu hv hcov ⟨z, hz, hzero⟩ ⟨z0, hz0, hv0⟩
  obtain ⟨y, hy1, hy2⟩ := ((Filter.Eventually.eventually_nhds hwu).and hwv).exists
  exact hy2 hy1

theorem null_zero (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) : volume (Ω ∩ {z | g z = 0}) = 0 := by
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hΩ x hx.1
  refine ⟨(Ω ∩ {z | g z = 0}) ∩ ball x ρ, inter_mem_nhdsWithin _ (ball_mem_nhds x hρ), ?_⟩
  have hnz : ∃ y ∈ ball x ρ, g y ≠ 0 := by
    by_contra h
    push Not at h
    exact not_loc_zero hΩ hc hg hne x hx.1
      (Filter.eventually_of_mem (ball_mem_nhds x hρ) fun y hy => h y hy)
  exact measure_mono_null (fun y hy => by
    simp only [mem_inter_iff, mem_setOf_eq, Metric.mem_ball] at hy ⊢; tauto) (extNull n x ρ g (hg.mono hB) hnz)

theorem ext_glue (hΩ : IsOpen Ω) (hc : IsPreconnected Ω) (hg : DifferentiableOn ℂ g Ω)
    (hne : ∃ z ∈ Ω, g z ≠ 0) {F' : V n → ℂ} (hF' : DifferentiableOn ℂ F' {z | z ∈ Ω ∧ g z ≠ 0})
    (hL2 : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧
      ∫⁻ y in ball z ρ \ {y | g y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤) :
    ∃ F : V n → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z ∈ Ω, g z ≠ 0 → F z = F' z := by
  classical
  have hU : ∀ z ∈ Ω, ∃ ρ > 0, ball z ρ ⊆ Ω ∧ ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball z ρ) ∧
      EqOn U F' (ball z ρ \ {y | g y = 0}) := by
    intro z hz
    obtain ⟨ρ, hρ, hB, hI⟩ := hL2 z hz
    obtain ⟨U, hU1, hU2⟩ := ext n z ρ g F' (hg.mono hB) (hF'.mono fun y hy => ⟨hB hy.1, hy.2⟩) hI
    exact ⟨ρ, hρ, hB, U, hU1, hU2⟩
  choose! ρ hρ hB U hUd hEq using hU
  let F : V n → ℂ := fun z => if g z ≠ 0 then F' z else U z z
  have key : ∀ z0 ∈ Ω, ∀ w ∈ ball z0 (ρ z0), F w = U z0 w := by
    intro z0 hz0 w hw
    by_cases hgw : g w = 0
    · have hwΩ : w ∈ Ω := hB z0 hz0 hw
      simp only [F, hgw, ne_eq, not_true_eq_false, if_false]
      by_contra hne'
      have hN : ∀ᶠ y in 𝓝 w, y ∈ ball z0 (ρ z0) ∩ ball w (ρ w) :=
        (isOpen_ball.inter isOpen_ball).mem_nhds ⟨hw, mem_ball_self (hρ w hwΩ)⟩
      have h1 : ContinuousAt (U z0) w :=
        ((hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds hw)).continuousAt
      have h2 : ContinuousAt (U w) w :=
        ((hUd w hwΩ).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ w hwΩ)))).continuousAt
      have hev : ∀ᶠ y in 𝓝 w, U w y - U z0 y ≠ 0 := (h2.sub h1).eventually_ne (sub_ne_zero.2 hne')
      have hfr : ∃ᶠ y in 𝓝 w, g y ≠ 0 := by
        rw [Filter.Frequently]
        intro h
        exact not_loc_zero hΩ hc hg hne w hwΩ (h.mono fun y hy => by simpa using hy)
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfr.and_eventually (hN.and hev)).exists
      exact hy3 (sub_eq_zero.2 ((hEq w hwΩ ⟨hy2.2, hy1⟩).trans (hEq z0 hz0 ⟨hy2.1, hy1⟩).symm))
    · simp only [F, ne_eq, hgw, not_false_eq_true, if_true]
      exact (hEq z0 hz0 ⟨hw, hgw⟩).symm
  refine ⟨F, fun z0 hz0 => ?_, fun z _ hgz => by simp [F, hgz]⟩
  have hd : DifferentiableAt ℂ (U z0) z0 :=
    (hUd z0 hz0).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ z0 hz0)))
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact Filter.eventually_of_mem (ball_mem_nhds z0 (hρ z0 hz0)) fun w hw => key z0 hz0 w hw

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoD
