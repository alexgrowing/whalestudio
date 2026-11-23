import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh

private theorem simplePath_cons_iff {n : ℕ} (χ : Fin n → ℂ) (a : Fin n) (l : List (Fin n)) :
    SimplePath χ (a :: l) ↔ (∀ r, r ≠ a → χ r ≠ χ a) ∧ SimplePath (χ + Pi.single a 1) l :=
  Iff.rfl

theorem simplePath_ne {n : ℕ} (ss : List (Fin n)) :
    ∀ χ : Fin n → ℂ, SimplePath χ ss → ∀ r s, r ≠ s → (r ∈ ss ∨ s ∈ ss) → χ r ≠ χ s := by
  induction ss with
  | nil =>
    intro χ _ r s _ h
    simp at h
  | cons a l ih =>
    intro χ hp r s hrs hmem
    rw [simplePath_cons_iff] at hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hra : r = a
    · subst hra
      exact (h1 s (Ne.symm hrs)).symm
    by_cases hsa : s = a
    · subst hsa
      exact h1 r hrs
    have hmem' : r ∈ l ∨ s ∈ l := by
      simp only [List.mem_cons] at hmem
      tauto
    have h3 := ih _ h2 r s hrs hmem'
    simpa [Pi.single_apply, hra, hsa] using h3

theorem simpleDistinct : CompanionTheory.RgExh.Fin.SimpleDistinct := by
  unfold CompanionTheory.RgExh.Fin.SimpleDistinct
  intro n χ ss hp hall r s hrs
  by_contra hne
  exact simplePath_ne ss χ hp r s hne (Or.inl (hall r)) hrs

end GlobalTheory.CompanionTheory.RgExhFin
