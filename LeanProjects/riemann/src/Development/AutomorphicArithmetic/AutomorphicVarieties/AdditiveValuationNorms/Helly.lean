import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.helly :
    ∀ (l : ℕ) [Fact l.Prime] (x : ℕ → ℤ_[l]) (r : ℕ → ℝ), (∀ a b, ‖x a - x b‖ ≤ max (r a) (r b)) →
      ∃ s : ℤ_[l], ∀ a, ‖s - x a‖ ≤ r a := by
  intro l _ x r hx
  have hne : ∀ u : Finset ℕ,
      ((Set.univ : Set ℤ_[l]) ∩ ⋂ a ∈ u, Metric.closedBall (x a) (r a)).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with hu | hu
    · exact ⟨0, by simp [hu]⟩
    · obtain ⟨a0, ha0, hmin⟩ := u.exists_min_image r hu
      refine ⟨x a0, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm]
      intro a ha
      exact (hx a0 a).trans (max_le (hmin a ha) le_rfl)
  obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty
    (fun a => Metric.closedBall (x a) (r a)) (fun a => Metric.isClosed_closedBall) hne
  refine ⟨s, fun a => ?_⟩
  have h1 := Set.mem_iInter.1 hs a
  rw [Metric.mem_closedBall, dist_eq_norm] at h1
  exact h1
