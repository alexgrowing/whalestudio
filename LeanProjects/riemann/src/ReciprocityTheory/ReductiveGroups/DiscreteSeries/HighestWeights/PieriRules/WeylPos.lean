import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS

private lemma weylPos_above_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 ≤ (univ.filter fun c => a < c ∧ ε c = ε a).card := by
  have hsub : (univ.filter fun c => b < c ∧ ε c = ε b) ⊆ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hab.trans hc.1, hc.2.trans he.symm⟩
  have hss : (univ.filter fun c => b < c ∧ ε c = ε b) ⊂ (univ.filter fun c => a < c ∧ ε c = ε a) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨b, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

private lemma weylPos_below_lt {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card := by
  have hsub : (univ.filter fun c => c < a ∧ ε c = ε a) ⊆ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hab, hc.2.trans he⟩
  have hss : (univ.filter fun c => c < a ∧ ε c = ε a) ⊂ (univ.filter fun c => c < b ∧ ε c = ε b) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨a, by simp [hab, he], by simp⟩
  exact Finset.card_lt_card hss

theorem rhoC_sub_ge_one {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    1 ≤ rhoC ε a - rhoC ε b := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 ≤
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 ≤
      ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) := by exact_mod_cast h2
  unfold rhoC
  linarith

theorem rhoC_consec {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b)
    (hc : ∀ c, a < c → c < b → ε c ≠ ε a) : rhoC ε a - rhoC ε b = 1 := by
  have h1 := weylPos_above_lt ε hab he
  have h2 := weylPos_below_lt ε hab he
  have h3 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
      (univ.filter fun c => b < c ∧ ε c = ε b).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le b _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c b with h | h | h
    · exact absurd hc'.2 (hc c hc'.1 h)
    · exact Or.inl h
    · exact Or.inr ⟨h, hc'.2.trans he⟩
  have h4 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
      (univ.filter fun c => c < a ∧ ε c = ε a).card + 1 := by
    refine (Finset.card_le_card ?_).trans (Finset.card_insert_le a _)
    intro c hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hc' ⊢
    rcases lt_trichotomy c a with h | h | h
    · exact Or.inr ⟨h, hc'.2.trans he.symm⟩
    · exact Or.inl h
    · exact absurd (hc'.2.trans he.symm) (hc c h hc'.1)
  have e1 : ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) =
      ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h3 h1
  have e2 : ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) =
      ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) + 1 := by
    exact_mod_cast le_antisymm h4 h2
  unfold rhoC
  rw [e1, e2]
  ring

theorem weylPos : WeylPosStatement := by
  intro n ε μ hμ
  unfold weylK
  refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  have hr := rhoC_sub_ge_one ε hb.1 hb.2
  have hd := hμ a b hb.1 hb.2
  apply div_pos
  · simp only [Pi.add_apply]
    linarith
  · linarith

end ReciprocityTheory.ChartRestriction.DS.HW
