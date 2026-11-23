import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtNull
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivC

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter

variable {n : ℕ}

theorem dense_nonzero {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {z : V n} (hz : z ∈ U) :
    ∃ᶠ y in 𝓝 z, y ∈ U ∧ g y ≠ 0 := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hz0 : ∀ᶠ y in 𝓝 z, g y = 0 := by
    filter_upwards [hcon, hU.mem_nhds hz] with y hy hyU
    by_contra h
    exact hy ⟨hyU, h⟩
  have hsub : U ⊆ {y | ∀ᶠ x in 𝓝 y, g x = 0} := by
    refine hUc.subset_of_closure_inter_subset isOpen_setOf_eventually_nhds ⟨z, hz, hz0⟩ ?_
    rintro y ⟨hycl, hyU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hycl ε hε
    have hbb : b ∈ ball y ε := by
      rw [mem_ball, dist_comm]
      exact hdist
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball y ε) g b isOpen_ball (convex_ball y ε)
      (hg.mono hball) hbb hb
    exact Filter.eventually_of_mem (ball_mem_nhds y hε) (fun w hw => by simpa using hEq hw)
  obtain ⟨w, hwU, hw⟩ := hg0
  exact hw (hsub hwU).self_of_nhds

theorem ext_glue {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {H : V n → ℂ}
    (hH : DifferentiableOn ℂ H (U ∩ {z | g z ≠ 0}))
    (hloc : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0})) :
    ∃ H' : V n → ℂ, DifferentiableOn ℂ H' U ∧ EqOn H' H (U ∩ {z | g z ≠ 0}) := by
  classical
  choose! r hr hrU hint using hloc

  have hE : ∀ z ∈ U, ∃ E : V n → ℂ, DifferentiableOn ℂ E (ball z (r z)) ∧
      EqOn E H (ball z (r z) \ {y | g y = 0}) := by
    intro z hz
    exact ReciprocityTheory.L2DbarEstimates.C.ext n (ball z (r z)) g H isOpen_ball (hg.mono (hrU z hz))
      (hH.mono (fun y hy => ⟨hrU z hz hy.1, hy.2⟩)) (hint z hz)
  choose! E hEd hEe using hE

  have hagree : ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ ball y (r y) ∩ ball z (r z), E y w = E z w := by
    intro y hy z hz w hw
    have hwU : w ∈ U := hrU y hy hw.1
    have hopen : IsOpen (ball y (r y) ∩ ball z (r z)) := isOpen_ball.inter isOpen_ball
    have hc1 : ContinuousAt (E y) w :=
      (hEd y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.1)
    have hc2 : ContinuousAt (E z) w :=
      (hEd z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.2)
    have hfreq : ∃ᶠ v in 𝓝 w, E y v - E z v ∈ ({0} : Set ℂ) := by
      have h1 := (dense_nonzero hU hUc hg hg0 hwU).and_eventually
        (hopen.mem_nhds hw : ∀ᶠ v in 𝓝 w, v ∈ ball y (r y) ∩ ball z (r z))
      refine h1.mono ?_
      rintro v ⟨⟨-, hgv⟩, hv1, hv2⟩
      rw [Set.mem_singleton_iff, sub_eq_zero, hEe y hy ⟨hv1, hgv⟩, hEe z hz ⟨hv2, hgv⟩]
    have h0 := isClosed_singleton.mem_of_frequently_of_tendsto hfreq (hc1.sub hc2)
    simpa [sub_eq_zero] using h0
  refine ⟨fun w => E w w, ?_, ?_⟩
  · intro z hz
    have hev : (fun w => E w w) =ᶠ[𝓝 z] E z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr z hz)), hU.mem_nhds hz]
        with w hw hwU
      exact hagree w hwU z hz w ⟨mem_ball_self (hr w hwU), hw⟩
    exact (((hEd z hz).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq hev).differentiableWithinAt
  · rintro w ⟨hwU, hgw⟩
    exact hEe w hwU ⟨mem_ball_self (hr w hwU), hgw⟩

end UpDivC

end ReciprocityTheory.ChartRestriction.G.AR.Up
