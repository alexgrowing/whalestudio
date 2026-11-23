import Mathlib

theorem UpperTheory.exists_smooth_extension_near :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {m : ℕ∞} {U : Set E},
      IsOpen U → ∀ {F : E → V}, ContDiffOn ℝ (m : WithTop ℕ∞) F U → ∀ {x : E}, x ∈ U →
        ∃ G : E → V, ContDiff ℝ (m : WithTop ℕ∞) G ∧ G =ᶠ[nhds x] F := by
  intro E _ _ _ V _ _ m U hU F hF x hx
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  let b : ContDiffBump x := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hsub : tsupport (b : E → ℝ) ⊆ U := by
    rw [b.tsupport_eq]
    exact hball
  refine ⟨fun y => b y • F y, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact (b.contDiff (n := m)).contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hy))
    · have h0 : (b : E → ℝ) =ᶠ[nhds y] 0 :=
        notMem_tsupport_iff_eventuallyEq.1 fun h => hy (hsub h)
      have h1 : (fun z => b z • F z) =ᶠ[nhds y] fun _ => (0 : V) := by
        filter_upwards [h0] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · filter_upwards [b.eventuallyEq_one] with z hz
    simp [hz]
