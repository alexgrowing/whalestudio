import Mathlib

open Metric

namespace GlobalTheory

theorem exists_schwartz_bump_of_proper_onto_open :
    ∀ {P U : Type} [TopologicalSpace P] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (π : P → U), Continuous π → ∀ (W' : Set U), IsOpen W' →
    (∀ S : Set U, IsCompact S → S ⊆ W' → IsCompact (π ⁻¹' S)) → ∀ (p₀ : P), π p₀ ∈ W' →
    ∀ (O : Set P), IsOpen O → π ⁻¹' {π p₀} ⊆ O →
    ∃ (φ : SchwartzMap U ℂ) (C : Set P), (∀ x, (φ x).im = 0 ∧ 0 ≤ (φ x).re) ∧ 0 < (φ (π p₀)).re ∧ IsCompact C ∧ C ⊆ O ∧
      ∀ p ∉ C, φ (π p) = 0 := by
  intro P U _ _ _ _ π hπ W' hW' hprop p₀ hp₀ O hO hfib
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hW' (π p₀) hp₀
  have hR : 0 < r₀ / 2 := half_pos hr₀
  have hcbR : closedBall (π p₀) (r₀ / 2) ⊆ W' :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hball
  have hK : IsCompact (π ⁻¹' closedBall (π p₀) (r₀ / 2) ∩ Oᶜ) :=
    (hprop _ (isCompact_closedBall _ _) hcbR).inter_right hO.isClosed_compl
  have hKi : IsCompact (π '' (π ⁻¹' closedBall (π p₀) (r₀ / 2) ∩ Oᶜ)) := hK.image hπ
  have hx : π p₀ ∉ π '' (π ⁻¹' closedBall (π p₀) (r₀ / 2) ∩ Oᶜ) := by
    rintro ⟨p, ⟨_, hpO⟩, hpx⟩
    exact hpO (hfib (by simpa using hpx))
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp hKi.isClosed.isOpen_compl (π p₀) hx
  set s := min r (r₀ / 2) / 2 with hs_def
  have hmin : 0 < min r (r₀ / 2) := lt_min hr hR
  have hs : 0 < s := half_pos hmin
  have hsR : s ≤ r₀ / 2 := (half_le_self hmin.le).trans (min_le_right _ _)
  have hsr : s < r := (half_lt_self hmin).trans_le (min_le_left _ _)
  let b : ContDiffBump (π p₀) := ⟨s / 2, s, half_pos hs, half_lt_self hs⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff),
    π ⁻¹' closedBall (π p₀) s, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change (((b x : ℝ) : ℂ)).im = 0 ∧ 0 ≤ (((b x : ℝ) : ℂ)).re
    simp [b.nonneg]
  · change 0 < (((b (π p₀) : ℝ) : ℂ)).re
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hs).le)]
    simp
  · exact hprop _ (isCompact_closedBall _ _) ((closedBall_subset_closedBall hsR).trans hcbR)
  · intro p hp
    by_contra hpO
    have hmem : π p ∈ π '' (π ⁻¹' closedBall (π p₀) (r₀ / 2) ∩ Oᶜ) :=
      ⟨p, ⟨closedBall_subset_closedBall hsR hp, hpO⟩, rfl⟩
    exact hrb (closedBall_subset_ball hsr hp) hmem
  · intro p hp
    change ((b (π p) : ℝ) : ℂ) = 0
    have hd : s ≤ dist (π p) (π p₀) := by
      simp only [Set.mem_preimage, mem_closedBall, not_le] at hp
      exact hp.le
    rw [b.zero_of_le_dist hd]
    simp

end GlobalTheory
