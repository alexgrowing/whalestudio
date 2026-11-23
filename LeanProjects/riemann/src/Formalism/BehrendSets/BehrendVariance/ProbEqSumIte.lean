import Mathlib
import Formalism.BehrendSets.Statement

open Finset

noncomputable section

namespace Formalism.BehrendSets.Rand

variable {α : Type} [DecidableEq α]

theorem prob_eq_sum_ite (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset, if P T then wt X δ T else 0 := by
  unfold prob
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : P T
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem prob_filter (X : Finset α) (δ : ℝ) (P : Finset α → Prop) [DecidablePred P] :
    prob X δ P = ∑ T ∈ X.powerset.filter P, wt X δ T := by
  rw [prob_eq_sum_ite, Finset.sum_filter]

theorem wt_nonneg (X T : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : 0 ≤ wt X δ T := by
  unfold wt
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (sub_nonneg.mpr h1) _)

theorem prob_total (X : Finset α) (δ : ℝ) : prob X δ (fun _ => True) = 1 := by
  rw [prob_filter]
  rw [filter_true_of_mem (fun _ _ => trivial)]
  have h : ∀ T ∈ X.powerset, wt X δ T = δ ^ T.card * (1 - δ) ^ (X.card - T.card) := by
    intro T hT
    unfold wt
    rw [card_sdiff_of_subset (mem_powerset.mp hT)]
  rw [Finset.sum_congr rfl h, Finset.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

theorem wt_union (X S U : Finset α) (δ : ℝ) (hU : U ⊆ X \ S) :
    wt X δ (S ∪ U) = δ ^ S.card * wt (X \ S) δ U := by
  unfold wt
  have hd : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (mem_sdiff.mp (hU hb)).2 ha
  have he : X \ (S ∪ U) = (X \ S) \ U := by
    ext a
    simp only [mem_sdiff, mem_union]
    tauto
  rw [card_union_of_disjoint hd, pow_add, he, mul_assoc]

theorem prob_sub (X S : Finset α) (δ : ℝ) (hS : S ⊆ X) :
    prob X δ (fun T => S ⊆ T) = δ ^ S.card := by
  symm
  calc δ ^ S.card = δ ^ S.card * prob (X \ S) δ (fun _ => True) := by
        rw [prob_total, mul_one]
    _ = ∑ U ∈ (X \ S).powerset, δ ^ S.card * wt (X \ S) δ U := by
        rw [prob_filter, filter_true_of_mem (fun _ _ => trivial), Finset.mul_sum]
    _ = prob X δ (fun T => S ⊆ T) := by
        rw [prob_filter]
        symm
        refine Finset.sum_nbij' (fun T => T \ S) (fun U => S ∪ U) ?_ ?_ ?_ ?_ ?_
        · intro T hT
          rw [mem_filter, mem_powerset] at hT
          rw [mem_powerset]
          intro x hx
          rw [mem_sdiff] at hx ⊢
          exact ⟨hT.1 hx.1, hx.2⟩
        · intro U hU
          rw [mem_powerset] at hU
          rw [mem_filter, mem_powerset]
          exact ⟨union_subset hS (hU.trans sdiff_subset), subset_union_left⟩
        · intro T hT
          rw [mem_filter] at hT
          exact union_sdiff_of_subset hT.2
        · intro U hU
          rw [mem_powerset] at hU
          ext x
          have hx := @hU x
          simp only [mem_sdiff, mem_union] at hx ⊢
          tauto
        · intro T hT
          rw [mem_filter, mem_powerset] at hT
          have hU : T \ S ⊆ X \ S := by
            intro x hx
            rw [mem_sdiff] at hx ⊢
            exact ⟨hT.1 hx.1, hx.2⟩
          rw [← wt_union X S (T \ S) δ hU, union_sdiff_of_subset hT.2]

theorem prob_sub_le (X S : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) :
    prob X δ (fun T => S ⊆ T) ≤ δ ^ S.card := by
  by_cases hS : S ⊆ X
  · exact (prob_sub X S δ hS).le
  · have h : prob X δ (fun T => S ⊆ T) = 0 := by
      rw [prob_filter, Finset.filter_false_of_mem, Finset.sum_empty]
      intro T hT hST
      exact hS (hST.trans (mem_powerset.mp hT))
    rw [h]
    exact pow_nonneg h0 _

theorem prob_mono (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (P Q : Finset α → Prop)
    (hPQ : ∀ T ⊆ X, P T → Q T) : prob X δ P ≤ prob X δ Q := by
  classical
  rw [prob_filter, prob_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    rw [mem_filter, mem_powerset] at hT ⊢
    exact ⟨hT.1, hPQ T hT.1 hT.2⟩
  · intro T _ _
    exact wt_nonneg X T h0 h1

theorem prob_exists_le {ι : Type} (X : Finset α) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (J : Finset ι) (E : ι → Finset α → Prop) :
    prob X δ (fun T => ∃ j ∈ J, E j T) ≤ ∑ j ∈ J, prob X δ (E j) := by
  classical
  rw [prob_eq_sum_ite X δ (fun T => ∃ j ∈ J, E j T),
    Finset.sum_congr rfl (fun j _ => prob_eq_sum_ite X δ (E j)), Finset.sum_comm]
  apply Finset.sum_le_sum
  intro T _
  have hnn : ∀ i ∈ J, 0 ≤ (if E i T then wt X δ T else 0) := by
    intro i _
    by_cases h : E i T
    · rw [if_pos h]; exact wt_nonneg X T h0 h1
    · rw [if_neg h]
  by_cases h : ∃ j ∈ J, E j T
  · rw [if_pos h]
    obtain ⟨j, hj, hE⟩ := h
    calc wt X δ T = (if E j T then wt X δ T else 0) := by rw [if_pos hE]
      _ ≤ ∑ i ∈ J, (if E i T then wt X δ T else 0) :=
        Finset.single_le_sum (f := fun i => if E i T then wt X δ T else 0) hnn hj
  · rw [if_neg h]
    exact Finset.sum_nonneg hnn

theorem tops_bad (X : Finset α) (δ : ℝ) (L K : ℕ) (t : α) (𝒲 : Finset (Finset α))
    (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (hW : ∀ W ∈ 𝒲, W.card ≤ L) :
    prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
      ≤ δ * 𝒲.card * ((L : ℝ) * δ) ^ K := by
  calc prob X δ (fun T => t ∈ T ∧ ∃ W ∈ 𝒲, K + 1 ≤ (T ∩ W).card)
      ≤ prob X δ (fun T => ∃ W ∈ 𝒲, ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T) := by
        apply prob_mono X h0 h1
        rintro T - ⟨htT, W, hW𝒲, hK⟩
        refine ⟨W, hW𝒲, ?_⟩
        have hA : K ≤ ((T ∩ W).erase t).card := by
          have := pred_card_le_card_erase (s := T ∩ W) (a := t)
          omega
        obtain ⟨S, hSA, hSc⟩ := exists_subset_card_eq hA
        refine ⟨S, mem_powersetCard.mpr ⟨hSA.trans (erase_subset_erase t inter_subset_right), hSc⟩,
          ?_⟩
        exact insert_subset htT (hSA.trans ((erase_subset t _).trans inter_subset_left))
    _ ≤ ∑ W ∈ 𝒲, prob X δ (fun T => ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T) :=
        prob_exists_le X h0 h1 𝒲
          (fun W T => ∃ S ∈ powersetCard K (W.erase t), insert t S ⊆ T)
    _ ≤ ∑ W ∈ 𝒲, ∑ S ∈ powersetCard K (W.erase t), prob X δ (fun T => insert t S ⊆ T) :=
        Finset.sum_le_sum fun W _ => prob_exists_le X h0 h1 _ (fun S T => insert t S ⊆ T)
    _ ≤ ∑ W ∈ 𝒲, ∑ S ∈ powersetCard K (W.erase t), δ ^ (K + 1) := by
        apply Finset.sum_le_sum
        intro W _
        apply Finset.sum_le_sum
        intro S hS
        have hS' := mem_powersetCard.mp hS
        have htS : t ∉ S := fun h => (mem_erase.mp (hS'.1 h)).1 rfl
        have hc : (insert t S).card = K + 1 := by rw [card_insert_of_notMem htS, hS'.2]
        rw [← hc]
        exact prob_sub_le X _ h0
    _ ≤ ∑ W ∈ 𝒲, (L : ℝ) ^ K * δ ^ (K + 1) := by
        apply Finset.sum_le_sum
        intro W hW𝒲
        rw [Finset.sum_const, card_powersetCard, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg h0 _)
        have h2 : (W.erase t).card.choose K ≤ L ^ K :=
          (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (card_erase_le.trans (hW W hW𝒲)) K)
        exact_mod_cast h2
    _ = δ * 𝒲.card * ((L : ℝ) * δ) ^ K := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
        ring

theorem expect_card (X : Finset α) (δ : ℝ) :
    expect X δ (fun T => (T.card : ℝ)) = δ * X.card := by
  unfold expect
  have h1 : ∀ T ∈ X.powerset,
      wt X δ T * (T.card : ℝ) = ∑ x ∈ X, if x ∈ T then wt X δ T else 0 := by
    intro T hT
    rw [Finset.sum_ite_mem, inter_eq_right.mpr (mem_powerset.mp hT), Finset.sum_const,
      nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ x ∈ X, (∑ T ∈ X.powerset, if x ∈ T then wt X δ T else 0) = δ := by
    intro x hx
    calc (∑ T ∈ X.powerset, if x ∈ T then wt X δ T else 0)
        = prob X δ (fun T => {x} ⊆ T) := by
          rw [prob_eq_sum_ite]
          refine Finset.sum_congr rfl fun T _ => ?_
          by_cases h : x ∈ T
          · rw [if_pos h, if_pos (singleton_subset_iff.mpr h)]
          · rw [if_neg h, if_neg (fun h' => h (singleton_subset_iff.mp h'))]
      _ = δ := by rw [prob_sub X {x} δ (singleton_subset_iff.mpr hx), card_singleton, pow_one]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem expect_sum_ite {ι : Type} (X : Finset α) (δ : ℝ) (I : Finset ι) (c : ι → ℝ)
    (E : ι → Finset α → Prop) (dec : ∀ i, DecidablePred (E i)) :
    expect X δ (fun T => ∑ i ∈ I, c i * (if E i T then 1 else 0))
      = ∑ i ∈ I, c i * prob X δ (E i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prob_eq_sum_ite X δ (E i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : E i T
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

end Formalism.BehrendSets.Rand

namespace Formalism.BehrendSets

open Formalism.BehrendSets.Rand

end Formalism.BehrendSets
