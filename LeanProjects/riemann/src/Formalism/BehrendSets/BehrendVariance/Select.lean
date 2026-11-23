import Mathlib
import Formalism.BehrendSets.Statement

open Finset

noncomputable section

namespace Formalism.BehrendSets.Select

variable {α : Type} [DecidableEq α]

lemma wt_nonneg (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) :
    0 ≤ wt X δ T :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma step (X : Finset α) (δ : ℝ) {a : α} (ha : a ∉ X) (g : Finset α → ℝ) :
    ∑ T ∈ (insert a X).powerset, wt (insert a X) δ T * g T =
      ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * g T + δ * g (insert a T)) := by
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
  have haXT : a ∉ X \ T := fun h => ha (Finset.mem_sdiff.1 h).1
  have e1 : wt (insert a X) δ T = wt X δ T * (1 - δ) := by
    unfold wt
    rw [Finset.insert_sdiff_of_notMem X haT, Finset.card_insert_of_notMem haXT, pow_succ]
    ring
  have e2 : wt (insert a X) δ (insert a T) = wt X δ T * δ := by
    unfold wt
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha,
      Finset.card_insert_of_notMem haT, pow_succ]
    ring
  rw [e1, e2]
  ring

lemma moments (X : Finset α) (δ : ℝ) :
    (∑ T ∈ X.powerset, wt X δ T * 1 = 1) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) = δ * X.card) ∧
    (∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2 =
      δ * X.card * (1 - δ) + δ ^ 2 * (X.card : ℝ) ^ 2) := by
  induction X using Finset.induction_on with
  | empty => simp [wt]
  | insert a X ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    rw [step X δ ha, step X δ ha, step X δ ha, Finset.card_insert_of_notMem ha]
    have e0 : ∑ T ∈ X.powerset, wt X δ T * ((1 - δ) * 1 + δ * 1) =
        ∑ T ∈ X.powerset, wt X δ T * 1 := by
      apply Finset.sum_congr rfl
      intro T _
      ring
    have e1 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) + δ * (((insert a T).card : ℕ) : ℝ)) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    have e2 : ∑ T ∈ X.powerset, wt X δ T *
          ((1 - δ) * ((T.card : ℕ) : ℝ) ^ 2 + δ * (((insert a T).card : ℕ) : ℝ) ^ 2) =
        ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
          + 2 * δ * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
          + δ * ∑ T ∈ X.powerset, wt X δ T * 1 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.1 hT h)
      rw [Finset.card_insert_of_notMem haT]
      push_cast
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, h0]
    · rw [e1, h0, h1]
      push_cast
      ring
    · rw [e2, h0, h1, h2]
      push_cast
      ring

lemma variance (X : Finset α) (δ : ℝ) :
    ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 = δ * X.card * (1 - δ) := by
  obtain ⟨h0, h1, h2⟩ := moments X δ
  have e : ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 =
      ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ) ^ 2
        - 2 * (δ * X.card) * ∑ T ∈ X.powerset, wt X δ T * (T.card : ℝ)
        + (δ * X.card) ^ 2 * ∑ T ∈ X.powerset, wt X δ T * 1 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [e, h0, h1, h2]
  ring

end Formalism.BehrendSets.Select

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Select in
theorem select : Select := by
  intro α _ X δ lam Y hδ0 hδ1 hY hlam hvar
  classical
  obtain ⟨h0, -, -⟩ := moments X δ
  have wnn : ∀ T, 0 ≤ wt X δ T := wt_nonneg X hδ0 hδ1
  set E := expect X δ Y with hEdef
  have hEs : ∑ T ∈ X.powerset, wt X δ T * Y T = E := rfl
  have hE : 0 ≤ E := Finset.sum_nonneg (fun T _ => mul_nonneg (wnn T) (hY T))
  by_contra hcon
  push Not at hcon

  have w1 : ∑ T ∈ X.powerset,
      (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) < 1 / 2 := by
    have hl2 : 0 < lam ^ 2 := by positivity
    calc ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0)
        ≤ ∑ T ∈ X.powerset, wt X δ T * ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
          apply Finset.sum_le_sum
          intro T _
          split_ifs with hp
          · have hsq : lam ^ 2 < ((T.card : ℝ) - δ * X.card) ^ 2 := by
              rw [← sq_abs ((T.card : ℝ) - δ * X.card)]
              exact pow_lt_pow_left₀ hp hlam.le (by norm_num)
            rw [mul_div_assoc]
            have : 1 ≤ ((T.card : ℝ) - δ * X.card) ^ 2 / lam ^ 2 := by
              rw [one_le_div hl2]
              exact hsq.le
            nlinarith [wnn T]
          · exact div_nonneg (mul_nonneg (wnn T) (sq_nonneg _)) hl2.le
      _ = δ * X.card * (1 - δ) / lam ^ 2 := by
          rw [← Finset.sum_div, variance]
      _ < 1 / 2 := by
          rw [div_lt_iff₀ hl2]
          linarith

  have w2 : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) ≤ 1 / 2 := by
    rcases hE.lt_or_eq with hEpos | hE0
    · calc ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0)
          ≤ ∑ T ∈ X.powerset, wt X δ T * Y T / (2 * E) := by
            apply Finset.sum_le_sum
            intro T _
            have h2E : 0 < 2 * E := by linarith
            split_ifs with hp
            · rw [mul_div_assoc]
              have : 1 ≤ Y T / (2 * E) := by
                rw [one_le_div h2E]
                exact hp.le
              nlinarith [wnn T]
            · exact div_nonneg (mul_nonneg (wnn T) (hY T)) h2E.le
        _ = E / (2 * E) := by
            rw [← Finset.sum_div, hEs]
        _ = 1 / 2 := by
            field_simp
    · have hz : ∀ T ∈ X.powerset, wt X δ T * Y T = 0 := by
        have hsum : ∑ T ∈ X.powerset, wt X δ T * Y T = 0 := hEs.trans hE0.symm
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun T _ => mul_nonneg (wnn T) (hY T))).1 hsum
      have : ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        split_ifs with hp
        · rw [← hE0] at hp
          have hYp : 0 < Y T := by linarith
          rcases mul_eq_zero.1 (hz T hT) with h | h
          · exact h
          · linarith
        · rfl
      rw [this]
      norm_num

  have cover : ∑ T ∈ X.powerset, wt X δ T * 1 ≤
      ∑ T ∈ X.powerset, (if lam < |(T.card : ℝ) - δ * X.card| then wt X δ T else 0) +
      ∑ T ∈ X.powerset, (if 2 * E < Y T then wt X δ T else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro T hT
    have hTX : T ⊆ X := Finset.mem_powerset.1 hT
    by_cases hp : lam < |(T.card : ℝ) - δ * X.card|
    · rw [if_pos hp, mul_one]
      split_ifs
      · linarith [wnn T]
      · linarith
    · rw [if_neg hp, mul_one, zero_add]
      have hq : 2 * E < Y T := hcon T hTX (not_lt.1 hp)
      rw [if_pos hq]
  rw [h0] at cover
  linarith

end Formalism.BehrendSets
