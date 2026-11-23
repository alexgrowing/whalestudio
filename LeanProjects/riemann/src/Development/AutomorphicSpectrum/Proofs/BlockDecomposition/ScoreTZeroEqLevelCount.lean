import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TZero

open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem score_tZero_level : ∀ {n : ℕ} (lev : Fin n → ℕ), Monotone lev → ∀ a : Fin n,
    score (tZero lev) a = ((univ.filter fun b => lev a < lev b).card : ℤ)
      - ((univ.filter fun b => lev b < lev a).card : ℤ) + ((a : ℕ) : ℤ) := by
  intro n lev hm a
  have hlt : ∀ b, lev a < lev b → a < b := fun b h => by
    by_contra hc
    exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
  have h1 : ((tZero lev).filter fun p => p.1 = a).card
      = (univ.filter fun b => lev a < lev b).card := by
    symm
    refine Finset.card_bij (fun b _ => (a, b)) ?_ ?_ ?_
    · intro b hb
      have hb' : lev a < lev b := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb', hlt b hb']
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).2
    · rintro ⟨x, b⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨_, h⟩, rfl⟩ := hp
      exact ⟨b, by simp [h], rfl⟩
  have h2 : (((prs n) \ tZero lev).filter fun p => p.2 = a).card
      = (univ.filter fun b => b < a ∧ lev b = lev a).card := by
    symm
    refine Finset.card_bij (fun b _ => (b, a)) ?_ ?_ ?_
    · intro b hb
      have hb' := (Finset.mem_filter.mp hb).2
      simp [tZero, prs, hb'.1, hb'.2]
    · intro b _ c _ h
      exact (Prod.ext_iff.mp h).1
    · rintro ⟨b, x⟩ hp
      simp only [tZero, prs, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_and,
        not_lt] at hp
      obtain ⟨⟨h, h'⟩, rfl⟩ := hp
      exact ⟨b, by simp [h, le_antisymm (hm h.le) (h' h)], rfl⟩
  have h3 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    simpa [Finset.filter_gt_eq_Iio] using Fin.card_Iio a
  have h4 : (univ.filter fun b => lev b < lev a).card
      + (univ.filter fun b => b < a ∧ lev b = lev a).card = (a : ℕ) := by
    rw [← h3, ← Finset.card_filter_add_card_filter_not (s := univ.filter fun b : Fin n => b < a)
      (fun b => lev b < lev a)]
    congr 2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        refine ⟨?_, h⟩
        by_contra hc
        exact absurd (hm (not_lt.mp hc)) (not_le.mpr h)
      · exact fun h => h.2
    · ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, fun hc => absurd h' (ne_of_lt hc)⟩
      · rintro ⟨h, h'⟩
        exact ⟨h, le_antisymm (hm h.le) (not_lt.mp h')⟩
  unfold score
  rw [h1, h2]
  have h4' : ((univ.filter fun b => lev b < lev a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ lev b = lev a).card : ℤ) = ((a : ℕ) : ℤ) := by
    exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.CoefId
