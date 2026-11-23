import Formalism.SubspaceCounting.TopsChoiceSecondBound

noncomputable section

open Finset

namespace Formalism.G0

namespace TopsConditionalProbabilityWindows

open Classical in

def P (U : Finset ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ :=
  ∑ t ∈ U.powerset, if A t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0

theorem condProb_eq (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (A : Finset ℕ → Prop) :
    condProb n δ A = P ((range n).erase 0) δ (fun t => A (insert 0 t)) := by
  classical
  have h0 : 0 ∈ range n := mem_range.2 hn
  have hU : range n = insert 0 ((range n).erase 0) := (insert_erase h0).symm
  have hc : ((range n).erase 0).card = n - 1 := by rw [card_erase_of_mem h0, card_range]
  unfold condProb P
  conv_lhs => rw [hU]
  rw [sum_powerset_insert (notMem_erase 0 _)]
  rw [sum_eq_zero (fun t ht => ?_), zero_add]
  · apply sum_congr rfl
    intro t ht
    have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
    have hnt : n - (t.card + 1) = n - 1 - t.card := by omega
    rw [card_insert_of_notMem h0t, hc, hnt]
    by_cases hA : A (insert 0 t)
    · rw [if_pos ⟨mem_insert_self 0 t, hA⟩, if_pos hA]
      simp
    · rw [if_neg (fun h => hA h.2), if_neg hA]
  · have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
    rw [if_neg (fun h => h0t h.1)]

theorem w_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (a b : ℕ) : 0 ≤ δ ^ a * (1 - δ) ^ b := by
  have : 0 ≤ 1 - δ := by linarith
  positivity

theorem P_mono {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {A B : Finset ℕ → Prop}
    (h : ∀ t ∈ U.powerset, A t → B t) : P U δ A ≤ P U δ B := by
  classical
  unfold P
  apply sum_le_sum
  intro t ht
  by_cases hA : A t
  · rw [if_pos hA, if_pos (h t ht hA)]
  · rw [if_neg hA]
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl

theorem prob_exists_le_sum {ι : Type*} {U : Finset ℕ} {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (s : Finset ι)
    (A : ι → Finset ℕ → Prop) :
    P U δ (fun t => ∃ j ∈ s, A j t) ≤ ∑ j ∈ s, P U δ (A j) := by
  classical
  unfold P
  rw [sum_comm]
  apply sum_le_sum
  intro t _
  have hnn : ∀ j ∈ s, 0 ≤ (if A j t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) := by
    intro j _
    split_ifs
    · exact w_nonneg h0 h1 _ _
    · exact le_rfl
  by_cases h : ∃ j ∈ s, A j t
  · rw [if_pos h]
    obtain ⟨j, hj, hA⟩ := h
    calc δ ^ t.card * (1 - δ) ^ (U.card - t.card)
        = (if A j t then δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) := by rw [if_pos hA]
      _ ≤ _ := single_le_sum (f := fun j => if A j t then
            δ ^ t.card * (1 - δ) ^ (U.card - t.card) else 0) hnn hj
  · rw [if_neg h]
    exact sum_nonneg hnn

theorem prob_subset_eq_pow_card {U S : Finset ℕ} (δ : ℝ) (hS : S ⊆ U) :
    P U δ (fun t => S ⊆ t) = δ ^ S.card := by
  classical
  let g : ℕ → ℝ := fun i => if i ∈ S then 0 else 1 - δ
  have hprod : ∏ i ∈ U, ((fun _ => δ) i + g i) = δ ^ S.card := by
    have : ∀ i ∈ U, ((fun _ => δ) i + g i) = if i ∈ S then δ else 1 := by
      intro i _
      simp only [g]
      split_ifs <;> ring
    rw [prod_congr rfl this, prod_ite_mem, inter_eq_right.2 hS, prod_const]
  rw [← hprod, prod_add]
  unfold P
  apply sum_congr rfl
  intro t ht
  have htU : t ⊆ U := mem_powerset.1 ht
  rw [prod_const]
  by_cases hSt : S ⊆ t
  · rw [if_pos hSt]
    have : ∀ i ∈ U \ t, g i = 1 - δ := by
      intro i hi
      have hit : i ∉ S := fun h => (mem_sdiff.1 hi).2 (hSt h)
      simp only [g, if_neg hit]
    rw [prod_congr rfl this, prod_const, card_sdiff_of_subset htU]
  · rw [if_neg hSt]
    obtain ⟨i, hiS, hit⟩ := not_subset.1 hSt
    have : ∏ i ∈ U \ t, g i = 0 :=
      prod_eq_zero (mem_sdiff.2 ⟨hS hiS, hit⟩) (by simp only [g, if_pos hiS])
    rw [this, mul_zero]

theorem window_subset (n i L : ℕ) (hn : 1 ≤ n) : window n i L ⊆ range n := by
  intro x hx
  unfold window at hx
  obtain ⟨j, _, rfl⟩ := mem_image.1 hx
  exact mem_range.2 (Nat.mod_lt _ (by omega))

theorem window_card (n i L : ℕ) : (window n i L).card ≤ L := by
  unfold window
  exact card_image_le.trans (card_range L).le

theorem window_bound (δ : ℝ) (h0 : 0 ≤ δ) (L K : ℕ) (hLδ : (L : ℝ) * δ ≤ 1) (W : Finset ℕ)
    (hW : W.card ≤ L) :
    ∑ S ∈ powersetCard (if 0 ∈ W then K else K + 1) (W.erase 0), δ ^ S.card
      ≤ (L.choose K : ℝ) * δ ^ K := by
  classical
  have hs : ∀ m : ℕ, ∑ S ∈ powersetCard m (W.erase 0), δ ^ S.card
      = ((W.erase 0).card.choose m : ℝ) * δ ^ m := by
    intro m
    rw [sum_congr rfl (fun S hS => by rw [(mem_powersetCard.1 hS).2]), sum_const,
      card_powersetCard, nsmul_eq_mul]
  have hE : (W.erase 0).card ≤ L := card_erase_le.trans hW
  have hδK : 0 ≤ δ ^ K := by positivity
  by_cases hw : 0 ∈ W
  · rw [if_pos hw, hs]
    have : (((W.erase 0).card.choose K : ℕ) : ℝ) ≤ (L.choose K : ℝ) := by
      exact_mod_cast Nat.choose_le_choose K hE
    exact mul_le_mul_of_nonneg_right this hδK
  · rw [if_neg hw, hs]
    have h1 : (((W.erase 0).card.choose (K + 1) : ℕ) : ℝ) ≤ (L.choose (K + 1) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose (K + 1) hE
    have h2 : (L.choose (K + 1) : ℝ) * δ ^ (K + 1) ≤ (L.choose K : ℝ) * δ ^ K := by
      have e : (L.choose (K + 1) : ℝ) * ((K : ℝ) + 1) = (L.choose K : ℝ) * ((L - K : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq L K
      have hle : ((L - K : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L K
      have hC : 0 ≤ (L.choose K : ℝ) := Nat.cast_nonneg _
      have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      have key : (L.choose (K + 1) : ℝ) * δ ^ (K + 1) * ((K : ℝ) + 1)
          ≤ (L.choose K : ℝ) * δ ^ K * ((K : ℝ) + 1) := by
        calc (L.choose (K + 1) : ℝ) * δ ^ (K + 1) * ((K : ℝ) + 1)
            = ((L.choose (K + 1) : ℝ) * ((K : ℝ) + 1)) * δ * δ ^ K := by ring
          _ = (L.choose K : ℝ) * ((L - K : ℕ) : ℝ) * δ * δ ^ K := by rw [e]
          _ ≤ (L.choose K : ℝ) * (L : ℝ) * δ * δ ^ K := by gcongr
          _ = (L.choose K : ℝ) * δ ^ K * ((L : ℝ) * δ) := by ring
          _ ≤ (L.choose K : ℝ) * δ ^ K * 1 :=
              mul_le_mul_of_nonneg_left hLδ (mul_nonneg hC hδK)
          _ ≤ (L.choose K : ℝ) * δ ^ K * ((K : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hδK)
      exact le_of_mul_le_mul_right key (by linarith)
    calc (((W.erase 0).card.choose (K + 1) : ℕ) : ℝ) * δ ^ (K + 1)
        ≤ (L.choose (K + 1) : ℝ) * δ ^ (K + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := h2

theorem key (n L K : ℕ) (t : Finset ℕ) (h0t : 0 ∉ t) (h : ¬ CondA n (insert 0 t) L K) :
    ∃ i ∈ range n, ∃ S ∈ powersetCard (if 0 ∈ window n i L then K else K + 1)
      ((window n i L).erase 0), S ⊆ t := by
  classical
  unfold CondA at h
  push Not at h
  obtain ⟨i, hi, hK⟩ := h
  refine ⟨i, mem_range.2 hi, ?_⟩
  set W := window n i L
  set s := t ∩ W.erase 0 with hs_def
  have hm : (if 0 ∈ W then K else K + 1) ≤ s.card := by
    by_cases hw : 0 ∈ W
    · rw [if_pos hw]
      have hsub : insert 0 t ∩ W ⊆ insert 0 s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        rcases mem_insert.1 hx1 with rfl | hxt
        · exact mem_insert_self _ _
        · refine mem_insert_of_mem (mem_inter.2 ⟨hxt, mem_erase.2 ⟨?_, hx2⟩⟩)
          rintro rfl
          exact h0t hxt
      have := (card_le_card hsub).trans (card_insert_le 0 s)
      omega
    · rw [if_neg hw]
      have hsub : insert 0 t ∩ W ⊆ s := by
        intro x hx
        rcases mem_inter.1 hx with ⟨hx1, hx2⟩
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact hw hx2
        rcases mem_insert.1 hx1 with hx | hxt
        · exact absurd hx hx0
        · exact mem_inter.2 ⟨hxt, mem_erase.2 ⟨hx0, hx2⟩⟩
      have := card_le_card hsub
      omega
  obtain ⟨S, hSs, hSc⟩ := exists_subset_card_eq hm
  refine ⟨S, mem_powersetCard.2 ⟨?_, hSc⟩, ?_⟩
  · exact fun x hx => (mem_inter.1 (hSs hx)).2
  · exact fun x hx => (mem_inter.1 (hSs hx)).1

end TopsConditionalProbabilityWindows

open TopsConditionalProbabilityWindows in
theorem tops_choice_part_a : TopsChoicePartA := by
  classical
  intro n δ L₂ K hn hδ hL hLδ
  have hL' : (1 : ℝ) ≤ L₂ := by exact_mod_cast hL
  have hδ1 : δ ≤ 1 := by nlinarith
  have hn1 : 1 ≤ n := by omega
  rw [condProb_eq n hn1]
  set U := (range n).erase 0 with hU
  let F : ℕ → Finset (Finset ℕ) := fun i =>
    powersetCard (if 0 ∈ window n i L₂ then K else K + 1) ((window n i L₂).erase 0)
  calc P U δ (fun t => ¬ CondA n (insert 0 t) L₂ K)
      ≤ P U δ (fun t => ∃ i ∈ range n, ∃ S ∈ F i, S ⊆ t) := by
        apply P_mono hδ hδ1
        intro t ht h
        have h0t : 0 ∉ t := fun h => notMem_erase 0 (range n) (mem_powerset.1 ht h)
        exact key n L₂ K t h0t h
    _ ≤ ∑ i ∈ range n, P U δ (fun t => ∃ S ∈ F i, S ⊆ t) :=
        prob_exists_le_sum hδ hδ1 (range n) (fun i t => ∃ S ∈ F i, S ⊆ t)
    _ ≤ ∑ i ∈ range n, ∑ S ∈ F i, P U δ (fun t => S ⊆ t) :=
        sum_le_sum fun i _ => prob_exists_le_sum hδ hδ1 (F i) (fun S t => S ⊆ t)
    _ = ∑ i ∈ range n, ∑ S ∈ F i, δ ^ S.card := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro S hS
        apply prob_subset_eq_pow_card
        intro x hx
        have hx' := (mem_powersetCard.1 hS).1 hx
        exact mem_erase.2 ⟨(mem_erase.1 hx').1, window_subset n i L₂ hn1 (mem_erase.1 hx').2⟩
    _ ≤ ∑ i ∈ range n, (L₂.choose K : ℝ) * δ ^ K :=
        sum_le_sum fun i _ => window_bound δ hδ L₂ K hLδ _ (window_card n i L₂)
    _ = n * (L₂.choose K : ℝ) * δ ^ K := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

end Formalism.G0
