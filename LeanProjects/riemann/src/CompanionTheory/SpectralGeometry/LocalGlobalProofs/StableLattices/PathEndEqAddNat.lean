import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

namespace GlobalTheory.CompanionTheory.RgPath

open CompanionTheory.RgExh

theorem pathEnd_eq_add_nat {n : ℕ} (ss : List (_root_.Fin n)) :
    ∀ χ : _root_.Fin n → ℂ, ∃ m : _root_.Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
      ∀ a, a ∈ ss → 1 ≤ m a := by
  induction ss with
  | nil =>
    intro χ
    exact ⟨0, by funext a; simp [pathEnd], by simp⟩
  | cons s ss ih =>
    intro χ
    obtain ⟨m', h, hm⟩ := ih (χ + Pi.single s 1)
    refine ⟨m' + Pi.single s 1, ?_, ?_⟩
    · rw [pathEnd, h]
      funext a
      by_cases e : a = s
      · subst e
        simp
        ring
      · simp [Pi.single_eq_of_ne e]
    · intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · simp
      · have := hm a ha
        simp only [Pi.add_apply]
        omega

theorem pathEndNat : CompanionTheory.RgExh.Fin.PathEndNat := fun _ χ ss => pathEnd_eq_add_nat ss χ

end GlobalTheory.CompanionTheory.RgPath
