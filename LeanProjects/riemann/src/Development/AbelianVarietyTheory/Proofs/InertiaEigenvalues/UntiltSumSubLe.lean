import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  intro l _ ι s r x hr hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : sh (0 : Fl l) = 0 := by
      have h : (0 : Fl l).untilt = 0 := Perfection.teichmuller_zero
      simp only [sh, h]; rfl
    simp only [Finset.sum_empty, h0, sub_zero, norm_zero]
    exact ⟨mul_nonneg (norm_nonneg _) hr, hr⟩
  | insert a t ha ih =>
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hxa : ‖sh (x a)‖ ≤ r := hs a (Finset.mem_insert_self a t)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (x a) (∑ i ∈ t, x i) hxa ih'.2
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, h2⟩
    have : sh (x a + ∑ i ∈ t, x i) - (sh (x a) + ∑ i ∈ t, sh (x i)) =
        (sh (x a + ∑ i ∈ t, x i) - sh (x a) - sh (∑ i ∈ t, x i)) + (sh (∑ i ∈ t, x i) - ∑ i ∈ t, sh (x i)) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih'.1)

end GlobalTheory
