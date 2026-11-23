import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ae_eq_eqOn {n : ℕ} {Ω : Set (V n)} {U U' : V n → ℂ} (hΩ : IsOpen Ω)
    (hU : ContinuousOn U Ω) (hU' : ContinuousOn U' Ω) (h : U =ᵐ[volume.restrict Ω] U') :
    EqOn U U' Ω := by
  exact Measure.eqOn_open_of_ae_eq h hΩ hU hU'

theorem reg_glue {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ball x r ⊆ Ω ∧
      ∃ U : V n → ℂ, DifferentiableOn ℂ U (ball x r) ∧ u =ᵐ[volume.restrict (ball x r)] U) :
    ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U := by
  classical
  choose! r hr hsub U hU hae using hloc
  have agree : ∀ x ∈ Ω, ∀ y ∈ Ω, EqOn (U x) (U y) (ball x (r x) ∩ ball y (r y)) := by
    intro x hx y hy
    apply ae_eq_eqOn (isOpen_ball.inter isOpen_ball)
    · exact ((hU x hx).mono inter_subset_left).continuousOn
    · exact ((hU y hy).mono inter_subset_right).continuousOn
    · have h1 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U x :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_left (hae x hx)
      have h2 : u =ᵐ[volume.restrict (ball x (r x) ∩ ball y (r y))] U y :=
        ae_restrict_of_ae_restrict_of_subset inter_subset_right (hae y hy)
      exact h1.symm.trans h2
  have loc : ∀ y ∈ Ω, ∀ x ∈ ball y (r y), U x x = U y x := by
    intro y hy x hx
    have hxΩ : x ∈ Ω := hsub y hy hx
    exact agree x hxΩ y hy ⟨mem_ball_self (hr x hxΩ), hx⟩
  refine ⟨fun x => U x x, ?_, ?_⟩
  · intro y hy
    have hnhds : ball y (r y) ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self (hr y hy))
    have hev : (fun x => U x x) =ᶠ[𝓝 y] U y :=
      Filter.eventually_of_mem hnhds (fun x hx => loc y hy x hx)
    exact (((hU y hy).differentiableAt hnhds).congr_of_eventuallyEq hev).differentiableWithinAt
  · obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : Ω => ball (x : V n) (r x)) (fun _ => isOpen_ball)
    have hcov : Ω = ⋃ x ∈ T, ball ((x : Ω) : V n) (r x) := by
      rw [hT]
      ext z
      simp only [mem_iUnion]
      constructor
      · intro hz
        exact ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
      · rintro ⟨x, hx⟩
        exact hsub x x.2 hx
    rw [hcov, Filter.EventuallyEq, ae_restrict_biUnion_iff _ hTc]
    intro x _
    filter_upwards [hae x x.2, self_mem_ae_restrict (measurableSet_ball (x := (x : V n)) (ε := r x))]
      with z hz hzb
    rw [hz]
    exact (loc x x.2 z hzb).symm

end ReciprocityTheory.L2DbarEstimates.C
