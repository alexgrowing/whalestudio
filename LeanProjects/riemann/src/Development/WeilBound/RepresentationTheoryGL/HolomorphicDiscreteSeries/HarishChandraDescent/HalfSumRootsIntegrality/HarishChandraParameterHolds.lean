import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Commutant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.RhoEqRhoCAddRhoN

noncomputable section

open Finset

namespace PositivityTheory.RgHe3.HarishChandraParameter

open ReciprocityTheory.ChartRestriction.DS

private theorem abs_half_sub_of_mem_Icc {x y n : ℝ} (hx0 : 0 ≤ x) (hxn : x ≤ n) (hy0 : 0 ≤ y) (hyn : y ≤ n) :
    |(x - y) / 2| ≤ n / 2 := by
  rw [abs_le]
  constructor <;> linarith

theorem abs_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ (n : ℝ) / 2 := by
  unfold rhoC
  apply abs_half_sub_of_mem_Icc (Nat.cast_nonneg _) _ (Nat.cast_nonneg _)
  · exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  · exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

theorem abs_rhoN_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoN ε a| ≤ (n : ℝ) / 2 := by
  unfold rhoN
  apply abs_half_sub_of_mem_Icc (Nat.cast_nonneg _) _ (Nat.cast_nonneg _)
  · exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  · exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)

end PositivityTheory.RgHe3.HarishChandraParameter

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgHe3.HarishChandraParameter

private theorem card_range_filter_lt_or_even_eq {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    #{b : Fin n | a < b ∧ ε b = ε a} + #{b : Fin n | a < b ∧ ¬ ε b = ε a} +
    #{b : Fin n | b < a ∧ ε b = ε a} + #{b : Fin n | b < a ∧ ¬ ε b = ε a} + 1 = n := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := ({b : Fin n | a < b} : Finset (Fin n))) (p := fun b => ε b = ε a)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := ({b : Fin n | b < a} : Finset (Fin n))) (p := fun b => ε b = ε a)
  simp only [Finset.filter_filter] at h1 h2
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi] at h1
  rw [Finset.filter_gt_eq_Iio, Fin.card_Iio] at h2
  have := a.isLt
  omega

private theorem exists_int_rhoC_sub_rhoN_sub_half' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    ∃ m : ℤ, rhoC ε a - rhoN ε a - ((n : ℝ) - 1) / 2 = m := by
  have hc := card_range_filter_lt_or_even_eq ε a
  refine ⟨-((#{b : Fin n | b < a ∧ ε b = ε a} : ℤ) + (#{b : Fin n | a < b ∧ ¬ ε b = ε a} : ℤ)), ?_⟩
  have hc' : ((#{b : Fin n | a < b ∧ ε b = ε a} : ℕ) : ℝ) + (#{b : Fin n | a < b ∧ ¬ ε b = ε a} : ℕ) +
      (#{b : Fin n | b < a ∧ ε b = ε a} : ℕ) + (#{b : Fin n | b < a ∧ ¬ ε b = ε a} : ℕ) + 1 = n := by
    exact_mod_cast hc
  unfold rhoC rhoN
  simp only [ne_eq]
  push_cast
  linarith

theorem harish_chandra_parameter_holds : HCOf := by
  intro n ε L h hL hh hgap
  have key : ∀ a b : Fin n, a < b →
      h ≤ (L - rhoN ε + rhoC ε) a - (L - rhoN ε + rhoC ε) b := by
    intro a b hab
    simp only [Pi.add_apply, Pi.sub_apply]
    have h1 := abs_le.1 (abs_rhoC_le ε a)
    have h2 := abs_le.1 (abs_rhoC_le ε b)
    have h3 := abs_le.1 (abs_rhoN_le ε a)
    have h4 := abs_le.1 (abs_rhoN_le ε b)
    have h5 := hgap a b hab
    linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  refine ⟨L - rhoN ε + rhoC ε, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b hab
    have := key a b hab
    linarith
  · intro a
    obtain ⟨m1, hm1⟩ := hL a
    obtain ⟨m2, hm2⟩ := exists_int_rhoC_sub_rhoN_sub_half' ε a
    refine ⟨m1 + m2, ?_⟩
    simp only [Pi.add_apply, Pi.sub_apply]
    push_cast
    linarith
  · ext a
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  · intro a b hne
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (key a b hab).trans (le_abs_self _)
    · exact absurd (congrArg ε hab) hne
    · rw [abs_sub_comm]
      exact (key b a hab).trans (le_abs_self _)
  · intro a
    simp only [Pi.add_apply, Pi.sub_apply]
    have h1 := abs_le.1 (abs_rhoC_le ε a)
    have h3 := abs_le.1 (abs_rhoN_le ε a)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

end PositivityTheory.RgHe3
