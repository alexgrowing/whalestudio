import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section

namespace Formalism.G0

namespace ChoiceOfTopsP

lemma not_good {n : ℕ} {T : Finset ℕ} {L₂ K r N₁ G : ℕ} (h : ¬ GoodOrbit n T L₂ K r N₁ G) :
    ¬ CondA n T L₂ K ∨ (¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ∨ ¬ CondC n T G ∨ T.card < N₁ := by
  unfold GoodOrbit at h
  by_cases hN : N₁ ≤ T.card
  · tauto
  · right; right; right; omega

lemma term_le (p a b c d : Prop) {_ : Decidable p} {_ : Decidable a} {_ : Decidable b}
    {_ : Decidable c} {_ : Decidable d} (w : ℝ) (hw : 0 ≤ w) (h : p → a ∨ b ∨ c ∨ d) :
    (if p then w else 0) ≤
      (if a then w else 0) + (if b then w else 0) + (if c then w else 0) + (if d then w else 0) := by
  by_cases hp : p
  · rcases h hp with h' | h' | h' | h' <;>
      split_ifs <;> linarith
  · split_ifs <;> linarith

lemma probNotGood_le (n : ℕ) (δ : ℝ) (L₂ K r N₁ G : ℕ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    probNotGood n δ L₂ K r N₁ G ≤
      condProb n δ (fun T => ¬ CondA n T L₂ K) +
      condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) +
      condProb n δ (fun T => ¬ CondC n T G) +
      condProb n δ (fun T => T.card < N₁) := by
  classical
  unfold probNotGood condProb
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro T _
  have hw : 0 ≤ δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) :=
    mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)
  refine term_le _ _ _ _ _ _ hw ?_
  rintro ⟨h0T, hg⟩
  rcases not_good hg with h | h | h | h
  · exact Or.inl ⟨h0T, h⟩
  · exact Or.inr (Or.inl ⟨h0T, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h0T, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h0T, h⟩))

end ChoiceOfTopsP

theorem choiceOfTops_of (ha : TopsChoicePartA) (hb : TopsChoiceSecondBound) (hc : TopsChoiceThirdBound) (hn : SmallCardCondProbBound) : ChoiceOfTops := by
  intro n δ L₂ K r N₁ G hn2 hev hδ hL hLδ hr hN
  have hL' : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  have hδ1 : δ ≤ 1 := by nlinarith
  have h := ChoiceOfTopsP.probNotGood_le n δ L₂ K r N₁ G hδ hδ1
  have h1 := ha n δ L₂ K hn2 hδ hL hLδ
  have h2 := hb n δ L₂ r N₁ hn2 hev hδ hL hLδ hr hN
  have h3 := hc n δ G hn2 hδ hδ1
  have h4 := hn n δ N₁ hn2 hδ hδ1
  linarith

end Formalism.G0
