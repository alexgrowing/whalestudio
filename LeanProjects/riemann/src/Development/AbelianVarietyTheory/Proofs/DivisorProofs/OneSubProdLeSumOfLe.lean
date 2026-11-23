import Mathlib
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

open scoped BigOperators Matrix in
open Polynomial in
private lemma one_sub_prod_le_sum_one_sub_of_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one h0' h1'
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have key := ih h0' h1'
    nlinarith [mul_nonneg (sub_nonneg.2 hP1) (sub_nonneg.2 ha1)]

open scoped BigOperators Matrix in
open Polynomial in

theorem _root_.GlobalTheory.degree_ratio_shift_bound : ∀ (Pl : Type) [Fintype Pl] (N p kc : ℕ) (u1 : Pl → ℕ → ℝ) (g1 w : Pl → ℝ) (T : ℝ), kc ≤ p → p ≤ N → 0 < T → (∀ τ, 0 < w τ) → (∀ τ, 3 * (N : ℝ) < g1 τ) → (∀ τ i l, i < l → l < N → u1 τ l < u1 τ i) → (∀ τ i l, i < p → p ≤ l → l < N → g1 τ ≤ u1 τ i - u1 τ l) → (∀ τ i l, i < kc → p ≤ l → l < N → w τ / (2 * T) ≤ u1 τ i - u1 τ l) → let u' : Pl → ℕ → ℝ := fun τ i => if i < p then u1 τ i else u1 τ i + 3 * N; let deg : (Pl → ℕ → ℝ) → ℝ := fun v => ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l); 0 < deg u' ∧ 0 ≤ 1 - deg u' / deg u1 ∧ 1 - deg u' / deg u1 ≤ 3 * N * ∑ τ, (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
  intro Pl inst N p kc u1 g1 w T hkc hpN hT hw hg hmono hgap hwgap u' deg
  have hN : (0 : ℝ) ≤ 3 * N := by positivity
  have hd : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l → 0 < u1 τ i - u1 τ l := by
    intro τ l i hl hi
    exact sub_pos.2 (hmono τ i l (Finset.mem_range.1 hi) (Finset.mem_range.1 hl))
  obtain ⟨F, hF⟩ : ∃ F : Pl → ℕ → ℕ → ℝ,
      ∀ τ l i, F τ l i = (u' τ i - u' τ l) / (u1 τ i - u1 τ l) := ⟨_, fun _ _ _ => rfl⟩
  have hfac : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      u' τ i - u' τ l = (u1 τ i - u1 τ l) * F τ l i := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [hF]
    field_simp
  have hFeq : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      F τ l i = if i < p ∧ p ≤ l then 1 - 3 * (N : ℝ) / (u1 τ i - u1 τ l) else 1 := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [Finset.mem_range] at hl hi
    rw [hF]
    by_cases hip : i < p
    · by_cases hpl : p ≤ l
      · have hl' : ¬ l < p := not_lt.2 hpl
        simp only [u', hip, hl', hpl, and_self, ↓reduceIte]
        field_simp <;> ring
      · have hl' : l < p := lt_of_not_ge hpl
        simp only [u', hip, hl', hpl, and_false, ↓reduceIte]
        exact div_self hne
    · have hl' : ¬ l < p := by omega
      simp only [u', hip, hl', false_and, ↓reduceIte]
      rw [show u1 τ i + 3 * (N : ℝ) - (u1 τ l + 3 * N) = u1 τ i - u1 τ l by ring]
      exact div_self hne
  have hF01 : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      0 < F τ l i ∧ F τ l i ≤ 1 := by
    intro τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · have hdp := hd τ l i hl hi
      have hlt : 3 * (N : ℝ) < u1 τ i - u1 τ l :=
        (hg τ).trans_le (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
      have h3 : 3 * (N : ℝ) / (u1 τ i - u1 τ l) < 1 := (div_lt_one hdp).2 hlt
      have h4 : 0 ≤ 3 * (N : ℝ) / (u1 τ i - u1 τ l) := div_nonneg hN hdp.le
      constructor <;> linarith
    · exact ⟨one_pos, le_rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Pl → ℕ → ℝ, ∀ τ i, c τ i = if i < kc then 2 * T / w τ else 1 / g1 τ :=
    ⟨_, fun _ _ => rfl⟩
  have hbound : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      1 - F τ l i ≤ 3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) := by
    intro τ l i hl hi
    have hdp := hd τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · rw [sub_sub_cancel, div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hN
      rw [hc]
      split_ifs with hk
      · have h1 : w τ ≤ (u1 τ i - u1 τ l) * (2 * T) :=
          (div_le_iff₀ (by linarith)).1 (hwgap τ i l hk h.2 (Finset.mem_range.1 hl))
        rw [div_le_div_iff₀ hdp (hw τ)]
        nlinarith
      · have hgpos : 0 < g1 τ := lt_of_le_of_lt hN (hg τ)
        exact one_div_le_one_div_of_le hgpos (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
    · simp
  have hsum : ∀ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
      3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) =
      3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
        + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
    intro τ
    simp_rw [← Finset.mul_sum]
    congr 1
    have hS : ∑ i ∈ Finset.range p, c τ i =
        (kc : ℝ) * (2 * T / w τ) + ((p - kc : ℕ) : ℝ) * (1 / g1 τ) := by
      rw [← Finset.sum_range_add_sum_Ico _ hkc]
      have e1 : ∑ i ∈ Finset.range kc, c τ i = ∑ i ∈ Finset.range kc, 2 * T / w τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_pos (Finset.mem_range.1 hi)]
      have e2 : ∑ i ∈ Finset.Ico kc p, c τ i = ∑ i ∈ Finset.Ico kc p, 1 / g1 τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_neg (not_lt.2 (Finset.mem_Ico.1 hi).1)]
      rw [e1, e2, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico,
        nsmul_eq_mul, nsmul_eq_mul]
    have hinner : ∀ l, ∑ i ∈ Finset.range l, (if i < p ∧ p ≤ l then c τ i else 0) =
        if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0 := by
      intro l
      by_cases hl : p ≤ l
      · rw [if_pos hl, ← Finset.sum_range_add_sum_Ico _ hl]
        have e1 : ∑ i ∈ Finset.range p, (if i < p ∧ p ≤ l then c τ i else 0) =
            ∑ i ∈ Finset.range p, c τ i :=
          Finset.sum_congr rfl fun i hi => if_pos ⟨Finset.mem_range.1 hi, hl⟩
        have e2 : ∑ i ∈ Finset.Ico p l, (if i < p ∧ p ≤ l then c τ i else 0) = 0 :=
          Finset.sum_eq_zero fun i hi =>
            if_neg fun h => absurd h.1 (not_lt.2 (Finset.mem_Ico.1 hi).1)
        rw [e1, e2, add_zero]
      · rw [if_neg hl]
        exact Finset.sum_eq_zero fun i _ => if_neg fun h => hl h.2
    rw [Finset.sum_congr rfl fun l _ => hinner l, ← Finset.sum_range_add_sum_Ico _ hpN]
    have e3 : ∑ l ∈ Finset.range p, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => if_neg (not_le.2 (Finset.mem_range.1 hl))
    have e4 : ∑ l ∈ Finset.Ico p N, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) =
        ∑ l ∈ Finset.Ico p N, ∑ i ∈ Finset.range p, c τ i :=
      Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_Ico.1 hl).1
    rw [e3, e4, zero_add, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hS]
    ring
  have hQ : ∀ τ l, l ∈ Finset.range N →
      0 < ∏ i ∈ Finset.range l, F τ l i ∧ ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ l hl =>
    ⟨Finset.prod_pos fun i hi => (hF01 τ l i hl hi).1,
      Finset.prod_le_one (fun i hi => (hF01 τ l i hl hi).1.le) fun i hi => (hF01 τ l i hl hi).2⟩
  have hR : ∀ τ, 0 < ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ∧
      ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ =>
    ⟨Finset.prod_pos fun l hl => (hQ τ l hl).1,
      Finset.prod_le_one (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2⟩
  have hP0 : 0 < ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i :=
    Finset.prod_pos fun τ _ => (hR τ).1
  have hP1 : ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 :=
    Finset.prod_le_one (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
  have hdeg1 : 0 < deg u1 := by
    simp only [deg]
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun l hl =>
      Finset.prod_pos fun i hi => hd τ l i hl hi
  have hdeg : deg u' = deg u1 * ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    simp only [deg, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun l hl =>
      Finset.prod_congr rfl fun i hi => hfac τ l i hl hi
  have hratio : deg u' / deg u1 = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    have hne := hdeg1.ne'
    rw [hdeg]
    field_simp
  refine ⟨by rw [hdeg]; exact mul_pos hdeg1 hP0, by rw [hratio]; linarith, ?_⟩
  rw [hratio]
  calc 1 - ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i
      ≤ ∑ τ, (1 - ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i) :=
        one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, (1 - ∏ i ∈ Finset.range l, F τ l i) :=
        Finset.sum_le_sum fun τ _ => one_sub_prod_le_sum_one_sub_of_mem_Icc _ _
          (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l, (1 - F τ l i) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun i hi => (hF01 τ l i hl hi).1.le)
            fun i hi => (hF01 τ l i hl hi).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
          3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          Finset.sum_le_sum fun i hi => hbound τ l i hl hi
    _ = ∑ τ, 3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
          + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) :=
        Finset.sum_congr rfl fun τ _ => hsum τ
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory
